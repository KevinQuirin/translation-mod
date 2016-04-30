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

(* Check if the type c is inductive, and if it is, if it has exactly one constructor *)
let inductive_with_one_constr env c =
  match kind_of_term c with
  |Ind (ind,_) ->
      let _, oib = Inductive.lookup_mind_specif env ind in
      let nc = Array.length oib.mind_consnames in
      if nc = 1 then true else false
  |_ -> false

let inductive_with_one_constr gl c =
  let env = Proofview.Goal.env gl in
  let b = inductive_with_one_constr env c in
  if isInd c
  then begin
      if b then begin
	Pp.msg_info (Pp.str ("Inductive has one constructor"));
	Proofview.tclUNIT()
      end
    else begin
	Pp.msg_info (Pp.str ("Inductive has not one constructor"));
	Proofview.tclUNIT()
	end
    end
  else begin
      Pp.msg_info (Pp.str ("This is not an inductive type"));
      Proofview.tclUNIT()
    end
    


let rec translate modality env c =
  match kind_of_term c with
  | Rel n ->
  (* mkRel n *)
     assert false
  | Var id ->
  (* mkVar id *)
     assert false
  | Sort s -> modality.mod_univ
  | Cast (c, k, t) -> assert false
  | Prod (na, t, u) ->
     let mt = (translate modality env t) in (* Translation of t *)
     let mu = (translate modality env u) in (* Translation of u *)
     mkApp (modality.mod_forall,
	    [| mt ; mkLambda (na, mkApp(modality.mod_univ_to_univ, [|mt|]), mu) |]
	   )
  | Lambda (na, t, u) ->
     let mt = (translate modality env t) in (* Translation of t *)
     let mu = (translate modality env u) in (* Translation of u *)
     mkLambda (na,
	       mkApp(modality.mod_univ_to_univ, [|mt|]),
	       mu)
     (* assert false *)
  | LetIn (na, c, t, u) ->
  (* mkLetIn (na, translate modality env c, translate modality env t, translate modality env u) *)
     assert false
  | App (t, args) ->
     let mt = (translate modality env t) in (* Translation of t *)
     let margs = Array.map (translate modality env) args in (* Translation of arguments *)
     mkApp (mt, margs)
     (* assert false *)
  | Const pc -> assert false
  | Ind (ind,i) ->
     let _, oib = Inductive.lookup_mind_specif env ind in
     let name = Id.to_string oib.mind_typename in
     if ("Unit" = name) then
       modality.mod_unit
     else
       mkApp(modality.mod_O, [|mkIndU (ind,i)|])
  | Construct pc -> assert false
  | Case (ci, c, r, p) -> assert false
  | Fix f -> assert false
  | CoFix f -> assert false
  | Proj (p, c) -> assert false
  | Meta _ -> assert false
  | Evar _ -> assert false
