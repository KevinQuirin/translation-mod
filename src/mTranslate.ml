open Names
open Term
open Declarations
open Environ
open Globnames
open Pp

let isConstruct_ c ind =
  match kind_of_term c with
  |Construct ((ind',j),k) ->
    Constr.equal ind (mkIndU(ind',k))
  |_ -> false
  

let eta_expand_fun f t =
  let f_ = mkApp (Vars.lift 1 f, [|mkRel 1|]) in
  mkLambda(Anonymous,t,f_)

let is_a_type env sigma t =
  let sigma, tt = Typing.type_of env sigma t in
  (sigma, is_Type tt)
       
type modality = {
    mod_O : global_reference;
    mod_eta : global_reference;
    mod_univ : global_reference;
    mod_univ_to_univ : global_reference;
    mod_forall : global_reference;
    mod_sig : global_reference;
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

let get_construct fctx constr =  
  let gr = ConstructRef constr in
  let gr_ =
    try Refmap.find gr fctx.translator
    with Not_found -> raise (MissingGlobal gr)
  in
  match gr_ with
  | ConstructRef constr_ -> constr_
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
     let mc, sigma = translate env fctx sigma c in
     let mt, sigma = translate_type env fctx sigma t in
     let mu, sigma = translate env fctx sigma u in
     (mkLetIn (na, mc, mt, mu), sigma)
  | App (t,args) when isInd t -> (* e.g. @paths A *)
     let ((ind,i),k) = destInd t in
     translate_ind env fctx sigma ind i k args
  | App (t,args) when isConstruct t -> (* e.g. @idpath A a *)
     let (((ind,i),j),k) = destConstruct t in
     translate_construct modal env fctx sigma ind i j k args
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
     (* apply_global env sigma (ConstructRef ((ind,i),u)) k fctx *)
     translate_construct modal env fctx sigma ind i u k [||]
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
  let sigma, _ = Typing.type_of env sigma mt in
  (mt,sigma)
    
and translate_ind env fctx sigma ind i k args =
  let modal = fctx.modal in
  let mib, oib = Inductive.lookup_mind_specif env (ind,i) in
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
    |[|ty;te|] -> assert false
    |[|ty;te1;te2|] ->
      let f u sigma = translate env fctx sigma u in
      let (margs,sigma) = CArray.fold_map' f args sigma in
      let sigma, modpaths = Evarutil.new_global sigma modal.mod_paths in
      (mkApp(modpaths, margs), sigma)
    |_ -> assert false
  else if ("sig" = name) then
    match args with
    |[||] -> assert false
    |[|ty|] -> assert false
    |[|ty;tp|] ->
      let f u sigma = translate env fctx sigma u in
      let (margs,sigma) = CArray.fold_map' f args sigma in
      let sigma, modsig = Evarutil.new_global sigma modal.mod_sig in
      (mkApp (modsig, margs),sigma)
    |_ -> assert false


  (* Else, we just apply O, and translate recursively *)
  else
    let nparams = List.length mib.mind_params_ctxt in
    if (Array.length args == nparams)
    then 
      let ind_ = get_inductive fctx (ind,i) in
      let f u sigma = translate env fctx sigma u in
      let (margs,sigma) = CArray.fold_map' f args sigma in
      let (sigma, pi) = Evd.fresh_inductive_instance env sigma ind_ in
      let ind_ = mkApp(mkIndU pi, margs) in
      let sigma, modo = Evarutil.new_global sigma modal.mod_O in
      let oind_ = mkApp(modo, [|ind_|]) in
      (oind_,sigma)
    else
      let a1 = args.(0) in
      let sigma,t = Typing.type_of env sigma a1 in
      translate env fctx sigma (eta_expand_fun (mkApp ((mkIndU ((ind,i),k)), args)) t)
	
and translate_construct modal env fctx sigma ind i j k args =
  let mib, oib = Inductive.lookup_mind_specif env (ind,i) in
  let name = Id.to_string oib.mind_typename in
  let n = mib.mind_nparams_rec in
  if ("Unit" = name) then
    (mkConstructU (((ind,i),j),k), sigma)
  else if ("paths" = name) then
    match args with
    |[||] ->
      let (sigma, s) = Evd.new_sort_variable Evd.univ_flexible sigma in
      let sigma, moduniv = Evarutil.new_global sigma modal.mod_univ in
      let sigma, modunivtouniv = Evarutil.new_global sigma modal.mod_univ_to_univ in
      translate env fctx sigma (eta_expand_fun (mkConstructU (((ind,i),j),k)) (mkSort(s)))
    |[|ty|] ->
      let mty,sigma = translate env fctx sigma ty in
      let sigma, moduniv = Evarutil.new_global sigma modal.mod_univ_to_univ in
      let mty = mkApp (moduniv, [|mty|]) in
      (mkApp (mkConstructU (((ind,i),j),k), [|mty|]), sigma)
    |[|ty;te|] ->
      let mty,sigma = translate_type env fctx sigma ty in
      let mte,sigma = translate env fctx sigma te in
      (* let sigma, moduniv = Evarutil.new_global sigma modal.mod_univ_to_univ in *)
      (* let mty = mkApp (moduniv, [|mty|]) in *)
      (mkApp (mkConstructU (((ind,i),j),k), [|mty;mte|]), sigma)
    |_ -> assert false
  else if ("sig" = name) then
    match args with
    |[||] -> assert false
    |[|ty|] -> assert false
    |[|ty;tp|] -> assert false
    |[|ty;tp;tx|] -> assert false
    |[|ty;tp;tx1;tx2|] ->
      let mtp,sigma =
      	match kind_of_term tp with
      	|Lambda(x,t,u) ->
      	  let mt,sigma = translate_type env fctx sigma t in
      	  let mu,sigma = translate_type env fctx sigma u in
      	  (mkLambda(x,mt,mu),sigma)
	|_ -> assert false
      in
      let mty,sigma = translate_type env fctx sigma ty in
      (* let mtp,sigma = translate env fctx sigma tp in *)
      let mtx1,sigma = translate env fctx sigma tx1 in
      let mtx2,sigma = translate env fctx sigma tx2 in
      (mkApp (mkConstructU (((ind,i),j),k), [|mty;mtp;mtx1;mtx2|]),sigma)
    |_ -> assert false
  else
    let nparams = List.length mib.mind_params_ctxt + oib.mind_consnrealargs.(j-1) in
    if (Array.length args == nparams)
    then
      let ind_ = get_inductive fctx (ind,i) in
      let f u sigma = translate env fctx sigma u in
      let (margs,sigma) = CArray.fold_map' f args sigma in
      let (sigma, pind) = Evd.fresh_inductive_instance env sigma ind_ in
      let ind_ = mkApp(mkIndU pind, Array.sub margs 0 (List.length mib.mind_params_ctxt)) in
      msg_info (Printer.pr_constr ind_);
      let constr_ = get_construct fctx ((ind,i),j) in
      let f u sigma =
	(* match kind_of_term u with *)
	(* |Construct (((ind,i),j'),k) -> *)
	(*   let u_ = get_construct fctx ((ind,i),j') in *)
	(*   (\* let (sigma, pi) = Evd.fresh_constructor_instance env sigma u_ in *\) *)
	(*   (mkConstructU (u_,k) , sigma) *)
	(* |_ -> *)
	  translate env fctx sigma u in
      let (margs,sigma) = CArray.fold_map' f margs sigma in
      let (sigma, pi) = Evd.fresh_constructor_instance env sigma constr_ in
      let constr_ = mkApp(mkConstructU pi, args) in
      msg_info (Printer.pr_constr constr_);
      let sigma, eta = Evarutil.new_global sigma modal.mod_eta in
      let oconstr_ = mkApp(eta, [|ind_; constr_ |]) in
      msg_info (Printer.pr_constr oconstr_);
      (oconstr_,sigma)
    else
      let a1 = args.(0) in
      let sigma,t = Typing.type_of env sigma a1 in
      translate env fctx sigma (eta_expand_fun (mkApp ((mkConstructU (((ind,i),j),k)), args)) t)

    
    (* apply_global env sigma (ConstructRef ((ind,i),j)) k fctx *)
    

  
let translate_context env fctx sigma ctx =
  let modal = fctx.modal in
  let fold (na, body, t) (sigma, fctx, ctx_) =
    let (sigma, body_) = match body with
    | None -> (sigma, None)
    | Some _ -> assert false
    in
    let env = push_rel (na,body,t) env in
    let (t_, sigma) = translate_type env fctx sigma t in
    let decl_ = (na, body_, t_) in
    (sigma, fctx, decl_ :: ctx_)
  in
  let (sigma, _, ctx_) = List.fold_right fold ctx (sigma, fctx, []) in
  (ctx_, sigma)
