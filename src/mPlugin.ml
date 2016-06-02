open Errors
open Pp
open Util
open Names
open Term
open Decl_kinds
open Libobject
open Globnames
open Proofview.Notations

(** Utilities *)

let translate_name id =
  let id = Id.to_string id in
  Id.of_string (id^"ᶠ" )
	       
(* (\** Record of translation between globals *\) *)

let translator : MTranslate.translator ref =
  Summary.ref ~name:"Modal Global Table" Refmap.empty

type translator_obj = (global_reference * global_reference) list

let add_translator translator l =
  List.fold_left (fun accu (src, dst) -> Refmap.add src dst accu) translator l

let cache_translator (_, l) =
  translator := add_translator !translator l

let load_translator _ l = cache_translator l
let open_translator _ l = cache_translator l
let subst_translator (subst, l) =
  let map (src, dst) = (subst_global_reference subst src, subst_global_reference subst dst) in
  List.map map l

let in_translator : translator_obj -> obj =
  declare_object { (default_object "MODAL TRANSLATOR") with
    cache_function = cache_translator;
    load_function = load_translator;
    open_function = open_translator;
    discharge_function = (fun (_, o) -> Some o);
    classify_function = (fun o -> Substitute o);
  }

(** Tactic *)

(* let empty_translator = Refmap.empty *)

let modal_tac modal c =
  Proofview.Goal.nf_enter
    begin fun gl ->
	  let env = Proofview.Goal.env gl in
	  let sigma = Proofview.Goal.sigma gl in
	  let fctx = { MTranslate.modal = modal; MTranslate.translator = !translator } in
	  let (ans,sigma) = MTranslate.translate env fctx sigma c in
	  let sigma, _ = Typing.type_of env sigma ans in
	  Proofview.Unsafe.tclEVARS sigma <*>
	    Tactics.letin_tac None (Names.Name.Anonymous) ans None Locusops.allHyps
    end

let modal_tac_named modal c id =
  Proofview.Goal.nf_enter
    begin fun gl ->
	  let env = Proofview.Goal.env gl in
	  let sigma = Proofview.Goal.sigma gl in
	  let fctx = { MTranslate.modal = modal; MTranslate.translator = !translator } in
	  let (ans,sigma) = MTranslate.translate env fctx sigma c in
	  let sigma, _ = Typing.type_of env sigma ans in
	  Proofview.Unsafe.tclEVARS sigma <*>
	    Tactics.letin_tac None (Names.Name id) ans None Locusops.allHyps
    end

    
let modal_translate_constant modal cst ids =
  let id = match ids with
    | None -> translate_name (Nametab.basename_of_global (ConstRef cst))
    | Some [id] -> id
    | Some _ -> error "Not the right number of provided names"
  in
  (** Translate the type *)
  let typ, _ = Universes.type_of_global (ConstRef cst) in
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let fctx = { MTranslate.modal = modal; MTranslate.translator = !translator } in
  let (typ,sigma) = MTranslate.translate_type env fctx sigma typ in
  let sigma, _ = Typing.type_of env sigma typ in
  let _uctx = Evd.evar_universe_context sigma in
  (** Define the term by tactic *)
  let body = Option.get (Global.body_of_constant cst) in
  let (body, sigma) = MTranslate.translate env fctx sigma body in
  msg_info (Termops.print_constr body);
  let evdref = ref sigma in
  let () = Typing.check env evdref body typ in
  let sigma = !evdref in
  let (_, uctx) = Evd.universe_context sigma in
  let ce = Declare.definition_entry ~types:typ ~univs:uctx body in
  let cd = Entries.DefinitionEntry ce in
  let decl = (cd, IsProof Lemma) in
  let cst_ = Declare.declare_constant id decl in
  [ConstRef cst, ConstRef cst_]


let eta_reduce c =
  let rec aux c =
    match kind_of_term c with
    | Lambda (n, t, b) ->
       let rec eta b =
	 match kind_of_term b with
	 | App (f, args) ->
	    if isRelN 1 (Array.last args) then
	      let args', _ = Array.chop (Array.length args - 1) args in
	      if Array.for_all (Vars.noccurn 1) args' then Vars.subst1 mkProp (mkApp (f, args'))
	      else let b' = aux b in if Term.eq_constr b b' then c else eta b'
	    else let b' = aux b in if Term.eq_constr b b' then c else eta b'
	 | _ -> let b' = aux b in
		if Term.eq_constr b' b then c else eta b'
       in eta b
    | _ -> map_constr aux c
  in aux c

let get_mind_globrefs mind =
  let open Declarations in
  let mib = Global.lookup_mind mind in
  let map i body =
    let ind = IndRef (mind, i) in
    let map_cons j _ = ConstructRef ((mind, i), j + 1) in
    ind :: List.mapi map_cons (Array.to_list body.mind_consnames)
  in
  let l = List.mapi map (Array.to_list mib.mind_packets) in
  List.flatten l

let modal_translate_ind modal ind ids =
  [IndRef ind, IndRef ind]

let modal_translate (reflector, eta, univ, univ_to_univ, forall, unit, path) gr ids =
  let r = gr in
  let gr = Nametab.global gr in
  let reflector = Nametab.global reflector in
  let eta = Nametab.global eta in
  let univ = Nametab.global univ in
  let univ_to_univ = Nametab.global univ_to_univ in
  let forall = Nametab.global forall in
  let unit = Nametab.global unit in
  let path = Nametab.global path in
  let modal = {
      MTranslate.mod_O = reflector;
      MTranslate.mod_eta = eta;
      MTranslate.mod_univ = univ;
      MTranslate.mod_univ_to_univ = univ_to_univ;
      MTranslate.mod_forall = forall;
      MTranslate.mod_unit = unit;
      MTranslate.mod_paths = path;
    } in
  let ans = match gr with
    | ConstRef cst -> modal_translate_constant modal cst ids
    | IndRef ind -> modal_translate_ind modal ind ids
    | _ -> error "Translation not handled."
  in
  let () = Lib.add_anonymous_leaf (in_translator ans) in
  let msg_translate (src, dst) =
    Pp.msg_info (str "Global " ++ Printer.pr_global src ++
		   str " has been translated as " ++ Printer.pr_global dst ++ str ".")
  in
  List.iter msg_translate ans
	    
let modal_implement (reflector, eta, univ, univ_to_univ, forall, unit, path) id typ idopt =
  let env = Global.env () in
  let reflector = Nametab.global reflector in
  let eta = Nametab.global eta in
  let univ = Nametab.global univ in
  let univ_to_univ = Nametab.global univ_to_univ in
  let forall = Nametab.global forall in
  let unit = Nametab.global unit in
  let path = Nametab.global path in
  let modal = {
      MTranslate.mod_O = reflector;
      MTranslate.mod_eta = eta;
      MTranslate.mod_univ = univ;
      MTranslate.mod_univ_to_univ = univ_to_univ;
      MTranslate.mod_forall = forall;
      MTranslate.mod_unit = unit;
      MTranslate.mod_paths = path;
    } in
  let id_ = match idopt with
    | None -> translate_name id
    | Some id -> id
  in
  let kind = Global, Flags.use_polymorphic_flag (), DefinitionBody Definition in
  let sigma = Evd.from_env env in
  let (typ, uctx) = Constrintern.interp_type env sigma typ in
  let sigma = Evd.from_ctx uctx in
  let fctx = { MTranslate.modal = modal; MTranslate.translator = !translator } in
  let (typ_,sigma) = MTranslate.translate_type env fctx sigma typ in
  let hook _ dst =
    (** Declare the original term as an axiom *)
    let param = (None, false, (typ, Evd.evar_context_universe_context uctx), None) in
    let cb = Entries.ParameterEntry param in
    let cst = Declare.declare_constant id (cb, IsDefinition Definition) in
    (** Attach the axiom to the forcing implementation *)
    Lib.add_anonymous_leaf (in_translator [ConstRef cst, dst])
  in
  let hook ctx = Lemmas.mk_hook hook in
  (* let sigma, univtouniv = Evarutil.new_global sigma univ_to_univ in *)
  (* let typ_ = mkApp (univtouniv, [|typ_|]) in *)
  let sigma, _ = Typing.type_of env sigma typ_ in
  let () = Lemmas.start_proof_univs id_ kind sigma typ_ hook in
  ()

(** Error handling *)

let _ = register_handler
	begin function
	| MTranslate.MissingGlobal gr ->
	   let ref = Nametab.shortest_qualid_of_global Id.Set.empty gr in
	   str "No modal translation for global " ++ Libnames.pr_qualid ref ++ str "."
	| _ -> raise Unhandled
end
