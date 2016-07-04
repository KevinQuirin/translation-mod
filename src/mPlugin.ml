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
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let sigma, cstu = Evd.fresh_constant_instance env sigma cst in
  let poly = Environ.polymorphic_pconstant cstu env in
  let body = Environ.constant_value_in env cstu in
  let typ = Environ.constant_type_in env cstu in
  let typ = Typeops.type_of_constant_type env typ in
  let fctx = { MTranslate.modal = modal; MTranslate.translator = !translator } in
  let (typ,sigma) = MTranslate.translate_type env fctx sigma typ in
  let sigma, _ = Typing.type_of env sigma typ in
  let _uctx = Evd.evar_universe_context sigma in
  (** Define the term by tactic *)
  let (body, sigma) = MTranslate.translate env fctx sigma body in
  msg_info (Termops.print_constr body);
  let evdref = ref sigma in
  let () = Typing.check env evdref body typ in
  let sigma = !evdref in
  let (_, uctx) = Evd.universe_context sigma in
  let ce = Declare.definition_entry ~poly ~types:typ ~univs:uctx body in
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

let modal_translate_ind_one modal env ids substind invsubst params ind (sigma,acc) =
  let fctx = { MTranslate.modal = modal; MTranslate.translator = !translator } in
  let open Declarations in
  let open Entries in
  let (sigma, s) =
    if List.mem Sorts.InType ind.mind_kelim then Evarutil.new_Type env sigma
    else (sigma, mkProp)
  in
  let nparams = List.length params in
  let (sigma, arity) =
    (** On obtient l'arité de l'inductif en traduisant le type de chaque indice
          i.e : si I ... : (i1 : A1),...,(in : An),s alors l'arité traduite 
          est (i1 : [A1])...(in : [An]), s *)
    let nindexes = List.length ind.mind_arity_ctxt - nparams in
    let ctx = List.firstn nindexes ind.mind_arity_ctxt in
    let env' = Environ.push_rel_context params env in
    let a = it_mkProd_or_LetIn s ctx in
    let (a,sigma) = MTranslate.translate_type env' fctx sigma a in
    (** En traduisant le type, le codomaine a aussi été traduit. On le remplace par le codomaine
          originel *)
    let (a, _) = decompose_prod_n nindexes a in 
    (sigma, compose_prod a s)
  in
  let typename = ind.mind_typename in
  let consnames = ind.mind_consnames in
  let translate_names id =
    let id = Id.to_string id in
    Id.of_string (id^"_m" )
  in
  let name_m, consnames_m = match ids with
    | None ->
       (translate_names typename, CArray.map_to_list translate_names consnames)
    | Some ids when List.length ids = Array.length consnames + 1 ->
       (List.hd ids, List.tl ids)
    | _ ->
       error "Not the right number of provided names"
  in
  let user_lc = ind.mind_user_lc in
  (* for i=0 to (Array.length user_lc -1) do *)
    (* msg_info (Termops.print_constr user_lc.(i)) *)
  (* done; *)
  let fold_lc (sigma, lc_) typ =
    let (u,sigma) = MTranslate.translate env fctx sigma typ in
    (sigma, u :: lc_)
    
    (* let typ_,s = decompose_prod typ in *)
    (* let typ_ = Array.of_list typ_ in *)
    (* let f (x,u) sigma = *)
    (*   let (u,sigma) = MTranslate.translate_type env fctx sigma u in *)
    (*   ((x,u),sigma) *)
    (* in *)
    (* let (typ_,sigma) = CArray.fold_map' f typ_ sigma in *)
    (* let typ_ = Array.to_list typ_ in *)
    (* let typ_ = compose_prod typ_ s in *)
    (* (sigma, typ_ :: lc_) *)
  in
  let (sigma, lc_) = Array.fold_left fold_lc (sigma, []) user_lc in

  (* for i=0 to (Array.length (Array.of_list lc_) -1) do *)
    (* msg_info (Termops.print_constr (Array.of_list lc_).(i)) *)
  (* done; *)
  let template = match ind.mind_arity with
    | RegularArity _ -> false
    | TemplateArity _ -> true
  in
  let ind_ = {
      mind_entry_typename = name_m;
      mind_entry_arity = arity;
      mind_entry_template = template;
      mind_entry_consnames = consnames_m;
      mind_entry_lc = List.rev lc_
    } in      
  (sigma, ind_ :: acc)

let modal_translate_ind_mind modal ind ids =
  let open Declarations in
  let open Entries in
  let env = Global.env () in
  let sigma = Evd.from_env env in

  let (mib,_) = Global.lookup_inductive ind in
  let substind =
    Array.map_to_list (fun oib -> (oib.mind_typename, None,
				   Inductive.type_of_inductive env ((mib, oib), Univ.Instance.empty)))
		      mib.mind_packets
  in
  let invsubst = List.map pi1 substind in
  let translator = add_translator !translator (List.map (fun id -> VarRef id, VarRef id) invsubst) in
  let fctx = { MTranslate.modal = modal; MTranslate.translator = translator } in

  let packets = mib.mind_packets in
  let params = mib.mind_params_ctxt in
  let params_m,sigma = MTranslate.translate_context env fctx sigma params in
  let sigma,packets_m = Array.fold_right (modal_translate_ind_one modal env ids substind invsubst params_m) packets (sigma,[]) in


  let record = match mib.mind_record with
  | None -> None
  | Some None -> Some None
  | Some (Some (id, _, _)) -> Some (Some (translate_name id))
  in
  
  (* let debug b = *)
  (*   msg_info (Nameops.pr_id b.mind_entry_typename ++ str " : " ++ Termops.print_constr (it_mkProd_or_LetIn b.mind_entry_arity params_m)); *)
  (*   let cs = List.combine b.mind_entry_consnames b.mind_entry_lc in *)
  (*   let pr_constructor (id, tpe) = *)
  (*     msg_info (Nameops.pr_id id ++ str " : " ++ Termops.print_constr tpe) *)
  (*   in *)
  (*   List.iter pr_constructor cs *)
  (* in *)
  (* List.iter debug packets_m; *)
  
  let make_param = function
  | (na, None, t) -> (Nameops.out_name na, LocalAssum t)
  | (na, Some body, _) -> (Nameops.out_name na, LocalDef body)
  in
  let params_ = List.map make_param params_m in
  let (_, uctx) = Evd.universe_context sigma in
  let mib_m = {
      mind_entry_record = record;
      mind_entry_finite = mib.mind_finite;
      mind_entry_params = params_;
      mind_entry_inds = packets_m;
      mind_entry_polymorphic = mib.mind_polymorphic;
      mind_entry_universes = uctx;
      mind_entry_private = mib.mind_private
    } in
  let (_, kn), _ = Declare.declare_mind mib_m in
  let mib_ = Global.mind_of_delta_kn kn in
  let map_data gr = match gr with
  | IndRef (mib, i) -> (gr, IndRef (mib_, i))
  | ConstructRef ((mib, i), j) -> (gr, ConstructRef ((mib_, i), j))
  | _ -> assert false
  in
  List.map map_data (get_mind_globrefs (fst ind))

  
    

let modal_translate_ind modal ind ids =
  modal_translate_ind_mind modal ind ids
  (* [IndRef ind, IndRef ind] *)

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
  let () = msg_info (Printer.pr_constr typ_) in
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
