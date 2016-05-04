open Names
open Term
open Declarations
open Environ
open Globnames
open Pp

type modality = {
    mod_O : Constr.t;
    mod_univ : Constr.t;
    mod_univ_to_univ : Constr.t;
    mod_forall : Constr.t;
    mod_unit : Constr.t;
  }

type translator = global_reference Refmap.t
exception MissingGlobal of global_reference

type forcing_context = {
    (* context : forcing_condition list; *)
    (** Forcing contexts are flagging variables of the rel_context in the same
    order. We statically know that variables coming from the introduction of
    a forcing condition come by pairs: the first one is a level, the second one
    a morphism. There is therefore only [Lift] condition for such pairs. *)
    modal : modality;
    (** Underlying category *)
    translator : translator;
    (** A map associating to all source constant a forced constant *)
  }

let apply_global env sigma gr u fctx =
  (** FIXME *)
  let p' =
    try Refmap.find gr fctx.translator
    with Not_found -> raise (MissingGlobal gr)
  in
  let (sigma, c) = Evd.fresh_global env sigma p' in
  match gr with
  | IndRef _ -> assert false
  | _ -> (c, sigma)

let rec translate modal env fctx sigma c =
  match kind_of_term c with
  | Rel n ->
     (mkRel n, sigma)
  (* assert false *)
  | Var id ->
     apply_global env sigma (VarRef id) Univ.Instance.empty fctx
     (* (mkVar id, sigma) *)
  (* assert false *)
  | Sort s ->
     let (sigma, s') =
       if Sorts.is_prop s then (sigma, Sorts.prop)
       else Evd.new_sort_variable Evd.univ_flexible sigma
     in
     let sigma = Evd.set_leq_sort env sigma s s' in
     (modal.mod_univ, sigma)
  | Cast (c, k, t) -> assert false
  | Prod (na, t, u) ->
     let (mt, sigma) = (translate modal env fctx sigma t) in (* Translation of t *)
     let (mu, sigma) = (translate modal env fctx sigma u) in (* Translation of u *)
     let mt1 = mkApp (modal.mod_univ_to_univ, [|mt|]) in
     let mu1 = mkApp (modal.mod_univ_to_univ, [|mu|]) in
     (* (ans,sigma) *)     
     (mkApp (modal.mod_forall,
	     [| mt ; mkLambda (na, mt1, mu) |]
	    ), sigma)
  | Lambda (na, t, u) ->
     let (mt,sigma) = (translate modal env fctx sigma t) in (* Translation of t *)
     let (mu,sigma) = (translate modal env fctx sigma u) in (* Translation of u *)
     let mt = mkApp(modal.mod_univ_to_univ, [|mt|]) in (* π1 mt *) 
     (mkLambda (na,mt,mu), sigma)
  (* assert false *)
  | LetIn (na, c, t, u) ->
     (* mkLetIn (na, translate modal env c, translate modal env t, translate modal env u) *)
     assert false
  | App (t, args) ->
     let (mt,sigma) = (translate modal env fctx sigma t) in (* Translation of t *)
     let margs = Array.map fst (Array.map (translate modal env fctx sigma) args) in (* Translation of arguments *)
     (mkApp (mt, margs), sigma)
  (* assert false *)
  | Const pc -> assert false
  | Ind (ind,i) ->
     let _, oib = Inductive.lookup_mind_specif env ind in
     let name = Id.to_string oib.mind_typename in
     if ("Unit" = name) then
       (modal.mod_unit, sigma)
     else
       let mind = mkIndU (ind,i) in
       (mkApp(modal.mod_O, [|mind|]),sigma)
  | Construct pc -> assert false
  | Case (ci, c, r, p) -> assert false
  | Fix f -> assert false
  | CoFix f -> assert false
  | Proj (p, c) -> assert false
  | Meta _ -> assert false
  | Evar _ -> assert false

and translate_type modal env fctx sigma t =
  let (mt,sigma) = translate modal env fctx sigma t in
  (mt,sigma)
