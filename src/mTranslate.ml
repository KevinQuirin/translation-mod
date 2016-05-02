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

(* (\* Check if the type c is inductive, and if it is, if it has exactly one constructor *\) *)
(* let inductive_with_one_constr env c = *)
(*   match kind_of_term c with *)
(*   |Ind (ind,_) -> *)
(*       let _, oib = Inductive.lookup_mind_specif env ind in *)
(*       let nc = Array.length oib.mind_consnames in *)
(*       if nc = 1 then true else false *)
(*   |_ -> false *)

(* let inductive_with_one_constr gl c = *)
(*   let env = Proofview.Goal.env gl in *)
(*   let b = inductive_with_one_constr env c in *)
(*   if isInd c *)
(*   then begin *)
(*       if b then begin *)
(* 	Pp.msg_info (Pp.str ("Inductive has one constructor")); *)
(* 	Proofview.tclUNIT() *)
(*       end *)
(*     else begin *)
(* 	Pp.msg_info (Pp.str ("Inductive has not one constructor")); *)
(* 	Proofview.tclUNIT() *)
(* 	end *)
(*     end *)
(*   else begin *)
(*       Pp.msg_info (Pp.str ("This is not an inductive type")); *)
(*       Proofview.tclUNIT() *)
(*     end *)
    


let rec translate modal env sigma c =
  match kind_of_term c with
  | Rel n ->
  (mkRel n, sigma)
     (* assert false *)
  | Var id ->
  (mkVar id, sigma)
     (* assert false *)
  | Sort s -> (modal.mod_univ, sigma)
  | Cast (c, k, t) -> assert false
  | Prod (na, t, u) ->
     let (mt, sigma) = (translate modal env sigma t) in (* Translation of t *)
     let (mu, sigma) = (translate modal env sigma u) in (* Translation of u *)
     (mkApp (modal.mod_forall,
	    [| mt ; mkLambda (na, mkApp(modal.mod_univ_to_univ, [|mt|]), mu) |]
	   ), sigma)
  | Lambda (na, t, u) ->
     let (mt,sigma) = (translate modal env sigma t) in (* Translation of t *)
     let (mu,sigma) = (translate modal env sigma u) in (* Translation of u *)
     let mt = mkApp(modal.mod_univ_to_univ, [|mt|]) in (* π1 mt *) 
     (mkLambda (na,mt,mu), sigma)
     (* assert false *)
  | LetIn (na, c, t, u) ->
  (* mkLetIn (na, translate modal env c, translate modal env t, translate modal env u) *)
     assert false
  | App (t, args) ->
     let (mt,sigma) = (translate modal env sigma t) in (* Translation of t *)
     let margs = Array.map fst (Array.map (translate modal env sigma) args) in (* Translation of arguments *)
     (mkApp (mt, margs), sigma)
     (* assert false *)
  | Const pc -> assert false
  | Ind (ind,i) ->
     let _, oib = Inductive.lookup_mind_specif env ind in
     let name = Id.to_string oib.mind_typename in
     if ("Unit" = name) then
       (modal.mod_unit, sigma)
     else
       (mkApp(modal.mod_O, [|mkIndU (ind,i)|]),sigma)
  | Construct pc -> assert false
  | Case (ci, c, r, p) -> assert false
  | Fix f -> assert false
  | CoFix f -> assert false
  | Proj (p, c) -> assert false
  | Meta _ -> assert false
  | Evar _ -> assert false

and translate_type modal env sigma t =
  let (sigma, mt) = translate modal env sigma t in
  (sigma, mt)
