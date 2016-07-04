open Names
open Term
open Declarations
open Environ
open Globnames
open Pp

let trunc_array a n = Array.sub a 0 n
  

let eta_expand_fun f t =
  let f_ = mkApp (Vars.lift 1 f, [|mkRel 1|]) in
  mkLambda(Anonymous,t,f_)

(* let rec is_a_type t = *)
(*   match kind_of_term t with *)
(*   |Sort _ -> true *)
(*   |Cast (c,_,_) -> is_a_type c *)
(*   |Prod _ -> true *)
(*   |LetIn(_,_,_,c) -> is_a_type c *)
(*   |App (f,args) -> ( *)
(*     match kind_of_term f with *)
(*     |Lambda (_,_,c) -> is_a_type c *)
(*     |_ -> false *)
(*   ) *)
(*   |Ind _ -> true *)
(*   |_ -> false *)
	      

let is_a_type env sigma t =
  let sigma, tt = Typing.type_of env sigma t in
  (sigma, is_Type tt)
       
type modality = {
    mod_O : global_reference;
    mod_eta : global_reference;
    mod_univ : global_reference;
    mod_univ_to_univ : global_reference;
    mod_forall : global_reference;
    mod_unit : global_reference;
    mod_paths : global_reference;
  }

type translator = global_reference Refmap.t
exception MissingGlobal of global_reference

type forcing_context = {
    modal : modality;
    (** Underlying modality *)
    translator : translator;
    (** A map associating to all source constant a forced constant *)
  }

let get_inductive fctx ind =
  let gr = IndRef ind in
  let gr_ =
    try Refmap.find gr fctx.translator
    with Not_found -> raise (MissingGlobal gr)
  in
  match gr_ with
  | IndRef ind_ -> ind_
  | _ -> assert false

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

let rec translate env fctx sigma c =
  let modal = fctx.modal in
  match kind_of_term c with
  | Rel n ->
     (mkRel n, sigma)
  | Var id ->
     apply_global env sigma (VarRef id) Univ.Instance.empty fctx
  | Sort s ->
     let (sigma, s') =
       if Sorts.is_prop s then (sigma, Sorts.prop)
       else Evd.new_sort_variable Evd.univ_flexible sigma
     in
     let sigma = Evd.set_leq_sort env sigma s s' in
     let sigma, moduniv = Evarutil.new_global sigma modal.mod_univ in
     (moduniv, sigma)
  | Cast (c, k, t) ->
     let mc, sigma = translate env fctx sigma c in
     let mt, sigma = translate_type env fctx sigma t in
     (mkCast (mc, k, mt), sigma)
  | Prod (na, t, u) ->
     let (mt, sigma) = (translate env fctx sigma t) in (* Translation of t *)
     let (mt1, sigma) = (translate_type env fctx sigma t) in (* Translation of t *)
     let (mu, sigma) = (translate (push_rel (na,None,t) env) fctx sigma u) in (* Translation of u *)
     let sigma, modall = Evarutil.new_global sigma modal.mod_forall in
     (mkApp (modall, [| mt ; mkLambda (na, mt1, mu) |]), sigma)
  | Lambda (na, t, u) ->
     let (mt,sigma) = (translate_type env fctx sigma t) in (* Translation of t *)
     let (mu,sigma) = (translate (push_rel (na,None,t) env) fctx sigma u) in (* Translation of u *)
     (mkLambda (na,mt,mu), sigma)
  | LetIn (na, c, t, u) ->
     (* mkLetIn (na, translate env c, translate env t, translate env u) *)
     assert false
  | App (t,args) when isInd t -> (* e.g. @paths A *)
     let ((ind,i),k) = destInd t in
     translate_ind env fctx sigma ind i k args
  (* | App (t,args) when isConstruct t -> (\* e.g. @idpath A a *\) *)
     (* let (((ind,i),j),k) = destConstruct t in *)
     (* translate_construct modal env fctx sigma ind i j k args *)
  | App (t, args) ->
     let (mt,sigma) = (translate env fctx sigma t) in (* Translation of t *)
     let f u sigma = translate env fctx sigma u in
     let (margs,sigma) = CArray.fold_map' f args sigma in
     (mkApp (mt, margs), sigma)
  (* assert false *)
  | Const (p,u) -> apply_global env sigma (ConstRef p) u fctx
  | Ind ((ind,i),k) ->
     translate_ind env fctx sigma ind i k [||]
  | Construct (((ind,i), u), k) ->
     apply_global env sigma (ConstructRef ((ind,i),u)) k fctx
     (* translate_construct modal env fctx sigma ind i u k [||] *)
  | Case (ci, c, r, p) -> assert false
  | Fix f -> assert false
  | CoFix f -> assert false
  | Proj (p, c) -> assert false
  | Meta _ -> assert false
  | Evar _ -> assert false

and translate_type env fctx sigma t =
  let modal = fctx.modal in
  let (mt,sigma) = translate env fctx sigma t in
  let sigma, modunivtouniv = Evarutil.new_global sigma modal.mod_univ_to_univ in
  let mt = mkApp(modunivtouniv, [|mt|]) in (* π1 mt *) 
  (mt,sigma)

and translate_ind env fctx sigma ind i k args =
  let modal = fctx.modal in
  let _, oib = Inductive.lookup_mind_specif env (ind,i) in
  let name = Id.to_string oib.mind_typename in
  (* Case Unit, translated to Unit *)
  if ("Unit" = name) then
    let sigma, modunit = Evarutil.new_global sigma modal.mod_unit in
    (modunit, sigma)
  (* Case paths, translated to paths *)
  else if ("paths" = name) then
    match args with
    (* FIXME *)
    |[||] -> assert false
    |[|ty|] -> assert false
    |[|ty;te|] ->
      translate env fctx sigma (eta_expand_fun (mkApp (mkIndU ((ind,i),k), [|ty;te|])) ty)
    |[|ty;te1;te2|] ->
      let f u sigma = translate env fctx sigma u in
      let (margs,sigma) = CArray.fold_map' f args sigma in
      let sigma, modpaths = Evarutil.new_global sigma modal.mod_paths in
      (mkApp(modpaths, margs), sigma)
    |_ -> assert false
  else if ("sig" = name) then
    let f u sigma = translate env fctx sigma u in
    let (margs,sigma) = CArray.fold_map' f args sigma in
    let mind = mkApp (mkIndU ((ind,i),k), margs) in
    (*TODO: Add here a mkApp sig_O [|mind|] *)
    (mind,sigma)
  (* Else, we just apply O, and translate recursively *)
  else
    let ind_ = get_inductive fctx (ind,i) in
    let f u sigma = translate env fctx sigma u in
    let (margs,sigma) = CArray.fold_map' f args sigma in
    let ind_ = mkApp(mkIndU (ind_,k), margs) in
    let sigma, modo = Evarutil.new_global sigma modal.mod_O in
    let oind_ = mkApp(modo, [|ind_|]) in
    (oind_,sigma)
    
	
(* and translate_construct modal env fctx sigma ind i j k args = *)
(*   let mib, oib = Inductive.lookup_mind_specif env (ind,i) in *)
(*   let name = Id.to_string oib.mind_typename in *)
(*   let n = mib.mind_nparams_rec in *)
(*   (\* Pp.msg_info (Pp.str ("Inductive "^name^" has "^(string_of_int n)^" params")); *\) *)
(*   if ("Unit" = name) then *)
(*     (mkConstructU (((ind,i),j),k), sigma) *)
(*   else if ("paths" = name) then *)
(*     match args with *)
(*     |[||] -> *)
(*       let (sigma, s) = Evd.new_sort_variable Evd.univ_flexible sigma in *)
(*       let sigma, moduniv = Evarutil.new_global sigma modal.mod_univ in *)
(*       let sigma, modunivtouniv = Evarutil.new_global sigma modal.mod_univ_to_univ in *)
(*       translate env fctx sigma (eta_expand_fun (mkConstructU (((ind,i),j),k)) (mkSort(s))) *)
(*     |[|ty|] -> *)
(*       let mty,sigma = translate env fctx sigma ty in *)
(*       let sigma, moduniv = Evarutil.new_global sigma modal.mod_univ_to_univ in *)
(*       let mty = mkApp (moduniv, [|mty|]) in *)
(*       (mkApp (mkConstructU (((ind,i),j),k), [|mty|]), sigma) *)
(*     |[|ty;te|] -> *)
(*       let mty,sigma = translate env fctx sigma ty in *)
(*       let mte,sigma = translate env fctx sigma te in *)
(*       let sigma, moduniv = Evarutil.new_global sigma modal.mod_univ_to_univ in *)
(*       let mty = mkApp (moduniv, [|mty|]) in *)
(*       (mkApp (mkConstructU (((ind,i),j),k), [|mty;mte|]), sigma) *)
(*     |_ -> assert false *)
(*   else *)
(*     let f u sigma = *)
(*       let sigma, g = is_a_type env sigma u in *)
(*       if g then *)
(* 	let sigma, modunivtouniv = Evarutil.new_global sigma modal.mod_univ_to_univ in *)
(* 	let uu,sigma = translate env fctx sigma u in *)
(* 	(mkApp (modunivtouniv, [|uu|]), sigma) *)
(*       else *)
(* 	translate env fctx sigma u in *)
(*     let (margs,sigma) = CArray.fold_map' f args sigma in *)
(*     let constr = mkConstructU (((ind,i),j),k) in *)
(*     let mconstr = mkApp (constr, margs) in *)
(*     let sigma, modeta = Evarutil.new_global sigma modal.mod_eta in *)
(*     let margs = Array.sub margs 0 n in *)
(*     let mind = mkApp (mkIndU ((ind,i),k), margs) in *)
(*     (mkApp(modeta, [|mind; mconstr|]),sigma) *)
(*       (\* TODO : This only works if the constructor is evaluated with as many arguments as possible, e.g. translating [inl] won't work, but translating [inl A B] will *\) *)

  
let translate_context env fctx sigma ctx =
  let modal = fctx.modal in
  let fold (na, body, t) (sigma, fctx, ctx_) =
    let (sigma, body_) = match body with
    | None -> (sigma, None)
    | Some _ -> assert false
    in
    (* let (ext, tfctx) = extend fctx in *)
    let env = push_rel (na,body,t) env in
    let (t_, sigma) = translate_type env fctx sigma t in
    (* let t_ = it_mkProd_or_LetIn t_ ext in *)
    let decl_ = (na, body_, t_) in
    (* let fctx = add_variable fctx in *)
    (sigma, fctx, decl_ :: ctx_)
  in
  (* let init = if toplevel then [pos_name, None, cat.cat_obj] else [] in *)
  let (sigma, _, ctx_) = List.fold_right fold ctx (sigma, fctx, []) in
  (ctx_, sigma)
