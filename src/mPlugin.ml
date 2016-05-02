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
  Id.of_string (id ^ "°")

(* (\** Record of translation between globals *\) *)

	       
let translator : MTranslate.translator ref =
  Summary.ref ~name:"Forcing Global Table" Refmap.empty

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

let empty_translator = Refmap.empty

let modal_tac modal c =
  Proofview.Goal.nf_enter
    begin fun gl ->
	  let env = Proofview.Goal.env gl in
	  let sigma = Proofview.Goal.sigma gl in
	  let (ans,sigma) = MTranslate.translate modal env sigma c in
	  let sigma, _ = Typing.type_of env sigma ans in
	  Proofview.Unsafe.tclEVARS sigma <*>
	    Tactics.letin_tac None (Names.Name.Anonymous) ans None Locusops.allHyps
    end

let modal_tac_named modal c id =
  Proofview.Goal.nf_enter
    begin fun gl ->
	  let env = Proofview.Goal.env gl in
	  let sigma = Proofview.Goal.sigma gl in
	  let (ans,sigma) = MTranslate.translate modal env sigma c in
	  let sigma, _ = Typing.type_of env sigma ans in
	  Proofview.Unsafe.tclEVARS sigma <*>
	    Tactics.letin_tac None (Names.Name id) ans None Locusops.allHyps
    end

let modal_implement (reflector, univ, univ_to_univ, forall, unit) id typ idopt =
  let env = Global.env () in
  let reflector = Universes.constr_of_global (Nametab.global reflector) in
  let univ = Universes.constr_of_global (Nametab.global univ) in
  let univ_to_univ = Universes.constr_of_global (Nametab.global univ_to_univ) in
  let forall = Universes.constr_of_global (Nametab.global forall) in
  let unit = Universes.constr_of_global (Nametab.global unit) in
  let modal = {
    MTranslate.mod_O = reflector;
    MTranslate.mod_univ = univ;
    MTranslate.mod_univ_to_univ = univ_to_univ;
    MTranslate.mod_forall = forall;
    MTranslate.mod_unit = unit;
  } in
  let id_ = match idopt with
  | None -> translate_name id
  | Some id -> id
  in
  let kind = Global, false, DefinitionBody Definition in
  let sigma = Evd.from_env env in
  let (typ, uctx) = Constrintern.interp_type env sigma typ in
  let sigma = Evd.from_ctx uctx in
  let (typ_,sigma) = MTranslate.translate_type modal env sigma typ in
  let (sigma, _) = Typing.type_of env sigma typ_ in
  let hook _ dst =
    (** Declare the original term as an axiom *)
    let param = (None, false, (typ, Evd.evar_context_universe_context uctx), None) in
    let cb = Entries.ParameterEntry param in
    let cst = Declare.declare_constant id (cb, IsDefinition Definition) in
    (** Attach the axiom to the forcing implementation *)
    Lib.add_anonymous_leaf (in_translator [ConstRef cst, dst])
  in
  let hook ctx = Lemmas.mk_hook hook in
  let sigma, _ = Typing.type_of env sigma typ_ in
  let () = Lemmas.start_proof_univs id_ kind sigma typ_ hook in
  ()
