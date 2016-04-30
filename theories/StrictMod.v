
Require Import HoTT.
Require Import Modality.


Module Modality_to_strict_modality (Mod: Modalities) <: Modalities.

  Definition Modality := Mod.Modality@{u a}.

  Module Export bar.

    Private Inductive OS (O:Modality@{u a}) (A:Type2le@{i a}) : Type2le@{i a} :=
    |η: A -> OS O A.
    
    Axiom isOmodal : forall (O:Modality@{u a}) (A:Type2le@{i a}), Mod.In@{u a i} O (OS@{u a i} O A).

    (* Axiom isOmodal : forall (O:Modality@{u a}) (A:Type2le@{i a}), IsEquiv (η O A) -> Mod.In@{u a i} O A. *)
    
    Definition O_ind (O:Modality@{u a}) (A:Type2le@{i a}) (B: OS@{u a i} O A -> Type2le@{j a})
               (H: forall x:OS O A, Mod.In O (B x))
      : (forall a:A, B (η O A a)) -> (forall a:OS O A, B a)
      := fun f x =>
           match x with
           |η a => f a
           end.

    Lemma isequiv_η_modal : forall (O:Modality@{u a}) (A:Type2le@{i a}), IsEquiv (η O A) -> Mod.In@{u a i} O A.
    Proof.
      intros O A IE.
      refine (Mod.inO_equiv_inO O _ _ _ (equiv_inv (IsEquiv := IE)) _).
      apply isOmodal.
    Defined.
    
    Definition O_indβ (O:Modality) (A:Type) (B: OS O A -> Type) (H: forall x:OS O A, Mod.In O (B x))
               (f: forall a:A, B (η O A a)) (a:A)
      : O_ind O A B H f (η O A a) = f a
      := 1.
  End bar.

  Definition O_reflector := OS.

  Definition In (O:Modality@{u a}) (A:Type2le@{i a}) := IsEquiv (η O A).

  Definition O_inO (O : Modality@{u a}) (T : Type@{i})
    : In@{u a i} O (O_reflector@{u a i} O T).
  Proof.
    simple refine (isequiv_adjointify _ _ _ _).
    - refine (O_ind O (O_reflector O T) (fun _ => O_reflector O T) _ idmap).
      intro x. apply (isOmodal O T).
    - refine (O_ind _ _ _ _ _).
      intro x. apply Mod.minO_paths. apply isOmodal.
      refine (O_ind _ _ _ _ _).
      intro x. apply Mod.minO_paths. apply isOmodal.
      intro a; reflexivity.
    - intro x; reflexivity.
  Defined.
          
  Definition to := η.

  Definition inO_equiv_inO :
      forall (O : Modality@{u a}) (T : Type@{i}) (U : Type@{j})
             (T_inO : In@{u a i} O T) (f : T -> U) (feq : IsEquiv f),        
        let gei := ((fun x => x) : Type@{i} -> Type@{k}) in
        let gej := ((fun x => x) : Type@{j} -> Type@{k}) in
        In@{u a j} O U.
  Proof.
    intros O T U T_inO f feq; cbn.
    simple refine (isequiv_adjointify _ _ _ _).
    - intro x; cut (OS O T).
      exact (f o (equiv_inv (IsEquiv := T_inO))).
      revert x. refine (O_ind _ _ _ _ _).
      intro; apply isOmodal.
      intro x. apply η.
      exact (equiv_inv (f:=f) x).
    - refine (O_ind _ _ _ _ _).
      intro x. cbn. apply Mod.minO_paths.
      apply isOmodal.
      intro a; cbn.
      apply ap.
      path_via (f (f^-1 a)); [apply ap; apply eissect | apply eisretr].
    - intro a.
      cbn.
      path_via (f (f^-1 a)); [apply ap; apply eissect | apply eisretr].
  Defined.

  Definition hprop_inO
    : Funext -> forall (O : Modality@{u a}) (T : Type@{i}),
        IsHProp (In@{u a i} O T).
  Proof.
    intros H O T; exact _.
  Defined.

  Definition O_ind_internal
  : forall (O : Modality@{u a})
           (A : Type2le@{i a})
           (B : O_reflector@{u a i} O A -> Type2le@{j a})
           (B_inO : forall oa, In@{u a j} O (B oa)),
      let gei := ((fun x => x) : Type@{i} -> Type@{k}) in
      let gej := ((fun x => x) : Type@{j} -> Type@{k}) in
      (forall a, B (to O A a)) -> forall a, B a.
  Proof.
    intros O A B B_inO; cbn.
    intros f z.
    apply O_ind. intro x; apply isequiv_η_modal. exact (B_inO x).
    intro a. apply f.
  Defined.

  Definition O_ind_beta_internal
  : forall (O : Modality@{u a})
           (A : Type@{i}) (B : O_reflector O A -> Type@{j})
           (B_inO : forall oa, In@{u a j} O (B oa))
           (f : forall a : A, B (to O A a)) (a:A),
      O_ind_internal@{u a i j k} O A B B_inO f (to O A a) = f a.
  Proof.
    intros O A B B_inO f a. reflexivity.
  Defined.

  Definition minO_paths
  : forall (O : Modality@{u a})
           (A : Type2le@{i a}) (A_inO : In@{u a i} O A) (z z' : A),
      In@{u a i} O (z = z').
  Proof.
    intros O A mA z z'.
    simple refine (isequiv_adjointify _ _ _ _).
    - intro p.
      refine (equiv_inj (η O A) _). exact mA.
      assert (m:= Mod.minO_paths O (OS O A) (isOmodal O A) (η O A z) (η O A z')).
      revert p.
      refine (O_ind O (z = z') (fun _ => η O A z = η O A z') (fun _ => m) (ap _)).
    - unfold Sect.
      refine (O_ind@{u a i i} _ _ _ _ _).
      intro a. apply Mod.minO_paths. apply isOmodal.
      intro p; destruct p; cbn. apply ap.
      rewrite concat_p1. apply concat_Vp.
    - intro p; destruct p; cbn.
      rewrite concat_p1. apply concat_Vp.
  Defined.
  
  (* Definition O_indO *)
  (*   : forall (O : Modality@{u a}) (A : Type@{i}) *)
  (*       (B : O_reflector@{u a i} O A -> Type@{j}), *)
  (*     (forall a, O_reflector@{u a j} O (B (to O A a))) *)
  (*     -> forall z, O_reflector@{u a j} O (B z). *)
  (* Proof. *)
  (*   intros O A B f z. *)
  (*   refine (O_ind O A (fun z => O_reflector O (B z)) _ f z). *)
  (* Defined. *)

  (* Definition O_indO_beta *)
  (* : forall (O : Modality@{u a}) (A : Type@{i}) *)
  (*          (B : O_reflector@{u a i} O A -> Type@{j}) *)
  (*          (f : forall a, O_reflector@{u a j} O (B (to O A a))) a, *)
  (*     O_indO O A B f (to O A a) = f a. *)
  (* Proof. intros O A B f a. reflexivity. Defined. *)

  (* Definition minO_pathsO *)
  (* : forall (O : Modality@{u a}) (A : Type@{i}) *)
  (*          (z z' : O_reflector@{u a i} O A), *)
  (*     IsEquiv@{i i} (to@{u a i} O (z = z')). *)
  (* Proof. *)
  (*   intros O A z z'. *)
  (*   refine (isequiv_adjointify _ _ _ _). *)
  (*   - exact (O_ind O (z=z') (fun _ => z = z') (fun _ => (minO_paths O (OS O A) (isOmodal O A) z z')) idmap). *)
  (*   - unfold Sect. *)
  (*     refine (O_ind@{u a i i} _ _ _ (fun w => inO_paths@{u a i i} _ _ _ _) _). *)
  (*     intro a; reflexivity. *)
  (*   - intro x; reflexivity. *)
  (* Defined. *)

End Modality_to_strict_modality.

(* Module Equivalence (Mod: Modalities). *)

(*   Export Mod. *)
(*   Context (O1 O2 : Modality). *)
(*   Context `{fs: Funext}. *)
(*   Parameter Equiv_O_reflector : forall A:Type, O_reflector O1 A <~> O_reflector O2 A. *)
(*   Parameter Equiv_In : forall A:Type, In O1 A <~> In O2 A. *)
(*   Parameter Equiv_η : forall A:Type, (Equiv_O_reflector A) o (to O1 A) == (to O2 A). *)
(*   Parameter Equiv_O_ind_internal : forall *)
(*              (A : Type2le@{i a}) *)
(*              (B : O_reflector@{u a i} O2 A -> Type2le@{j a}) *)
(*              (B_inO : forall oa, In@{u a j} O2 (B oa)) *)
(*              (X: forall a, B (to O2 A a)) (a:O_reflector O2 A), *)
(*       transport B (eisretr (Equiv_O_reflector A) a) *)
(*                 (O_ind_internal O1 A (fun a : O_reflector O1 A => B ((Equiv_O_reflector A) a)) *)
(*                                 (fun oa : O_reflector O1 A => (Equiv_In (B ((Equiv_O_reflector A) oa)))^-1 (B_inO ((Equiv_O_reflector A) oa))) *)
(*                                 (fun a : A => transport B (Equiv_η A a)^ (X a))  *)
(*                                 ((Equiv_O_reflector A)^-1 a)) *)
(*       = *)
(*       O_ind_internal O2 A B B_inO X a. *)


(*   (* Definition Equiv_O_ind_beta_internal *) *)
(*   (*   : forall (A : Type@{i}) (B : O_reflector O2 A -> Type@{j}) *) *)
(*   (*       (B_inO : forall oa, In@{u a j} O2 (B oa)) *) *)
(*   (*       (f : forall a : A, B (to O2 A a)) (a:A), *) *)
(*   (*     O_ind_internal O2 A B B_inO f (to O2 A a) = f a. *) *)
(*   (* Proof. *) *)
(*   (*   intros A B B_inO f a. *) *)
(*   (*   refine ((apD (O_ind_internal O2 A B B_inO f) (Equiv_η A a))^ @ _). *) *)
(*   (*   refine (ap _ (Equiv_O_ind_internal _ _ _ _ _)^ @ _). *) *)

(*   (*   refine (ap _ (transport2 B (eisadj (Equiv_O_reflector A) (to O1 A a)) _) @ _). *) *)
(*   (*   cbn. *) *)

    
(*   (*   refine (ap (transport B (Equiv_η A a)) (ap (transport B (eisretr (Equiv_O_reflector A) ((Equiv_O_reflector A) (to O1 A a)))) (apD (O_ind_internal O1 A (B o (Equiv_O_reflector A)) _ (fun a0 : A => transport B (Equiv_η A a0)^ (f a0))) (eissect (Equiv_O_reflector A) (to O1 A a)))^) @ _). *) *)

    
(*   (*   path_via (O_ind_internal O2 A B B_inO f (to O1 A a)). *) *)
(*   (*   refine ((Equiv_O_ind_internal _ _ _ _ _)^ @ _). *) *)
    
    

  
  
(*   Parameter Equiv_O_ind_beta_internal *)
(*     : forall (A : Type@{i}) (B : O_reflector O2 A -> Type@{j}) *)
(*         (B_inO : forall oa, In@{u a j} O2 (B oa)) *)
(*         (f : forall a : A, B (to O2 A a)) (a:A), *)
(*       O_ind_beta_internal O2 A B B_inO f a = *)
(*       (apD (O_ind_internal O2 A B B_inO f) (Equiv_η A a))^ @ *)
(*          (ap (transport B (Equiv_η A a)) (Equiv_O_ind_internal A B B_inO f ((Equiv_O_reflector A) (to O1 A a)))^ @ *)
(*           (ap (transport B (Equiv_η A a)) *)
(*              (ap (transport B (eisretr (Equiv_O_reflector A) ((Equiv_O_reflector A) (to O1 A a)))) *)
(*                 (apD *)
(*                    (O_ind_internal O1 A (fun a0 : O_reflector O1 A => B ((Equiv_O_reflector A) a0)) *)
(*                       (fun oa : O_reflector O1 A => *)
(*                        (Equiv_In (B ((Equiv_O_reflector A) oa)))^-1 (B_inO ((Equiv_O_reflector A) oa))) *)
(*                       (fun a0 : A => transport B (Equiv_η A a0)^ (f a0)))  *)
(*                    (eissect (Equiv_O_reflector A) (to O1 A a))^)^) @ *)
(*            (ap (transport B (Equiv_η A a)) *)
(*               (ap (transport B (eisretr (Equiv_O_reflector A) ((Equiv_O_reflector A) (to O1 A a)))) *)
(*                  (ap *)
(*                     (transport (fun a0 : O_reflector O1 A => B ((Equiv_O_reflector A) a0)) *)
(*                        (eissect (Equiv_O_reflector A) (to O1 A a))^) *)
(*                     (O_ind_beta_internal O1 A (fun a0 : O_reflector O1 A => B ((Equiv_O_reflector A) a0)) *)
(*                        (fun oa : O_reflector O1 A => *)
(*                         (Equiv_In (B ((Equiv_O_reflector A) oa)))^-1 (B_inO ((Equiv_O_reflector A) oa))) *)
(*                        (fun a0 : A => transport B (Equiv_η A a0)^ (f a0)) a))) @ *)
(*             moveR_transport_p B (Equiv_η A a) *)
(*               (transport B (eisretr (Equiv_O_reflector A) ((Equiv_O_reflector A) (to O1 A a))) *)
(*                  (transport (fun a0 : O_reflector O1 A => B ((Equiv_O_reflector A) a0)) *)
(*                     (eissect (Equiv_O_reflector A) (to O1 A a))^  *)
(*                     (transport B (Equiv_η A a)^ (f a))))  *)
(*               (f a) *)
(*               (ap (transport B (eisretr (Equiv_O_reflector A) ((Equiv_O_reflector A) (to O1 A a)))) *)
(*                  (transport_compose B (Equiv_O_reflector A)  *)
(*                     (eissect (Equiv_O_reflector A) (to O1 A a))^  *)
(*                     (transport B (Equiv_η A a)^ (f a))) @ *)
(*                ((transport_pp B (ap (Equiv_O_reflector A) (eissect (Equiv_O_reflector A) (to O1 A a))^) *)
(*                    (eisretr (Equiv_O_reflector A) ((Equiv_O_reflector A) (to O1 A a)))  *)
(*                    (transport B (Equiv_η A a)^ (f a)))^ @ *)
(*                 transport2 B *)
(*                   ((ap_V (Equiv_O_reflector A) (eissect (Equiv_O_reflector A) (to O1 A a)) @@ 1) @ *)
(*                    moveR_Vp (eisretr (Equiv_O_reflector A) ((Equiv_O_reflector A) (to O1 A a))) 1 *)
(*                      (ap (Equiv_O_reflector A) (eissect (Equiv_O_reflector A) (to O1 A a))) *)
(*                      (eisadj (Equiv_O_reflector A) (to O1 A a) @ *)
(*                       (concat_p1 (ap (Equiv_O_reflector A) (eissect (Equiv_O_reflector A) (to O1 A a))))^)) *)
(*                   (transport B (Equiv_η A a)^ (f a))))))). *)

(* End Equivalence. *)
  
Module Equivalence_SMod_Mod (Mod: Modalities).

  Module SMod := Modality_to_strict_modality Mod.

  Let Modality := Mod.Modality.

  Context `{fs: Funext}.

  Lemma Mod_to_SMod (O:Modality) (A:Type)
    : Mod.In O A -> SMod.In O A.
  Proof.
    intro mA.
    simple refine (isequiv_adjointify _ _ _ _).
    - refine (SMod.bar.O_ind _ _ _ _ _). intro; exact mA.
      exact idmap.
    - refine (SMod.bar.O_ind _ _ _ _ _); cbn; [| reflexivity].
      intro x.
      apply Mod.minO_paths. apply SMod.bar.isOmodal.
    - intro x; reflexivity.
  Qed.
  
  Lemma SMod_to_Mod (O:Modality) (A:Type)
    : SMod.In O A -> Mod.In O A.
  Proof.
    apply SMod.bar.isequiv_η_modal.
  Qed.

  Definition Equiv_O_reflector (O:Mod.Modality) (A:Type)
    : SMod.O_reflector O A <~> Mod.O_reflector O A.
  Proof.
    simple refine (BuildEquiv _ _ _ _).
    - apply SMod.O_ind_internal.
      intro x; clear x. apply Mod_to_SMod. apply Mod.O_inO.
      apply Mod.to.
    - simple refine (BuildIsEquiv _ _ _ _ _ _ _).
      + refine (Mod.O_ind_internal O A (fun _ => SMod.O_reflector O A) _ _).
        intro; apply SMod_to_Mod. apply SMod.O_inO.
        exact (SMod.to O A).
      + refine (Mod.O_ind_internal _ _ _ _ _); intro a; cbn.
        apply SMod_to_Mod.
        apply SMod.minO_paths.
        apply Mod_to_SMod. apply Mod.O_inO.
        exact (ap _ (Mod.O_ind_beta_internal _ _ _ _ _ _)).
      + refine (SMod.O_ind_internal _ _ _ _ _); intro a; cbn.
        apply Mod_to_SMod.
        apply Mod.minO_paths.
        apply SMod_to_Mod. apply SMod.O_inO.
        exact (Mod.O_ind_beta_internal _ _ _ _ _ _).
      + refine (SMod.O_ind_internal _ _ _ _ _).
        intro oa.
        refine (SMod.minO_paths _ _ _ _ _).
        refine (SMod.minO_paths _ _ _ _ _).
        apply Mod_to_SMod. apply Mod.O_inO.
        intro a; cbn.
        refine (Mod.O_ind_beta_internal _ _ _ _ _ _).
  Defined.

  Lemma Equiv_In (O:Modality) (A:Type)
    : SMod.In O A <~> Mod.In O A.
  Proof.
    refine (equiv_adjointify (SMod_to_Mod O A) (Mod_to_SMod O A) _ _);
      intro; refine (path_ishprop _ _).
  Defined.
    
  Lemma Equiv_η (O:Mod.Modality) (A:Type)
    : (Equiv_O_reflector O A) o (SMod.to O A) == (Mod.to O A).
  Proof.
    intro x. reflexivity.
  Defined.

  Definition Equiv_O_ind_internal
             (O : Modality@{u a})
             (A : Type2le@{i a})
             (B : Mod.O_reflector@{u a i} O A -> Type2le@{j a})
             (B_inO : forall oa, Mod.In@{u a j} O (B oa))
             (X: forall a, B (Mod.to O A a)) (a:Mod.O_reflector O A)
    : transport B (eisretr (Equiv_O_reflector O A) a)
                (SMod.O_ind_internal O A (fun a : SMod.O_reflector O A => B ((Equiv_O_reflector O A) a))
                                (fun oa : SMod.O_reflector O A => (Equiv_In O (B ((Equiv_O_reflector O A) oa)))^-1 (B_inO ((Equiv_O_reflector O A) oa)))
                                (fun a : A => transport B (Equiv_η O A a)^ (X a)) 
                                ((Equiv_O_reflector O A)^-1 a))
      =
      Mod.O_ind_internal O A B B_inO X a.
  Proof.
    revert a.
    refine (Mod.O_ind_internal _ _ _ _ _).
    intro oa. apply Mod.minO_paths. apply B_inO.
    intro a.
    transparent assert (r: (((Equiv_O_reflector O A)^-1 (Mod.to O A a)) = SMod.to O A a)).
    { cbn. refine (Mod.O_ind_beta_internal _ _ _ _ _ _). }
    refine ((ap _ (apD (SMod.O_ind_internal O A _ _ _) r^))^ @ _). 
    refine (ap _ (transport_compose B (Equiv_O_reflector O A) r^ _) @ _).
    refine ((transport_pp _ _ _ _)^ @ _).
    refine (_ @ (Mod.O_ind_beta_internal _ _ _ _ _ _)^).
    refine (transport2 B (q:=1) _ _).
    subst r. refine ((ap_V _ _) @@ 1 @ _).
    apply moveR_Vp.
    refine ((Mod.O_ind_beta_internal _ _ _ _ _ _) @ _).
    symmetry; apply concat_p1.
  Defined.
    
  Definition Equiv_O_ind_beta_internal
  : forall (O : Modality@{u a})
           (A : Type@{i}) (B : Mod.O_reflector O A -> Type@{j})
           (B_inO : forall oa, Mod.In@{u a j} O (B oa))
           (f : forall a : A, B (Mod.to O A a)) (a:A),
      Mod.O_ind_beta_internal O A B B_inO f a =
      (apD (Mod.O_ind_internal O A B B_inO f) (Equiv_η O A a))^ @
         (ap (transport B (Equiv_η O A a)) (Equiv_O_ind_internal O A B B_inO f ((Equiv_O_reflector O A) (SMod.to O A a)))^ @
          (ap (transport B (Equiv_η O A a))
             (ap (transport B (eisretr (Equiv_O_reflector O A) ((Equiv_O_reflector O A) (SMod.to O A a))))
                (apD
                   (SMod.O_ind_internal O A (fun a0 : SMod.O_reflector O A => B ((Equiv_O_reflector O A) a0))
                      (fun oa : SMod.O_reflector O A =>
                       (Equiv_In O (B ((Equiv_O_reflector O A) oa)))^-1 (B_inO ((Equiv_O_reflector O A) oa)))
                      (fun a0 : A => transport B (Equiv_η O A a0)^ (f a0))) 
                   (eissect (Equiv_O_reflector O A) (SMod.to O A a))^)^) @
           (ap (transport B (Equiv_η O A a))
              (ap (transport B (eisretr (Equiv_O_reflector O A) ((Equiv_O_reflector O A) (SMod.to O A a))))
                 (ap
                    (transport (fun a0 : SMod.O_reflector O A => B ((Equiv_O_reflector O A) a0))
                       (eissect (Equiv_O_reflector O A) (SMod.to O A a))^)
                    (SMod.O_ind_beta_internal O A (fun a0 : SMod.O_reflector O A => B ((Equiv_O_reflector O A) a0))
                       (fun oa : SMod.O_reflector O A =>
                        (Equiv_In O (B ((Equiv_O_reflector O A) oa)))^-1 (B_inO ((Equiv_O_reflector O A) oa)))
                       (fun a0 : A => transport B (Equiv_η O A a0)^ (f a0)) a))) @
            moveR_transport_p B (Equiv_η O A a)
              (transport B (eisretr (Equiv_O_reflector O A) ((Equiv_O_reflector O A) (SMod.to O A a)))
                 (transport (fun a0 : SMod.O_reflector O A => B ((Equiv_O_reflector O A) a0))
                    (eissect (Equiv_O_reflector O A) (SMod.to O A a))^ 
                    (transport B (Equiv_η O A a)^ (f a)))) 
              (f a)
              (ap (transport B (eisretr (Equiv_O_reflector O A) ((Equiv_O_reflector O A) (SMod.to O A a))))
                 (transport_compose B (Equiv_O_reflector O A) 
                    (eissect (Equiv_O_reflector O A) (SMod.to O A a))^ 
                    (transport B (Equiv_η O A a)^ (f a))) @
               ((transport_pp B (ap (Equiv_O_reflector O A) (eissect (Equiv_O_reflector O A) (SMod.to O A a))^)
                   (eisretr (Equiv_O_reflector O A) ((Equiv_O_reflector O A) (SMod.to O A a))) 
                   (transport B (Equiv_η O A a)^ (f a)))^ @
                transport2 B
                  ((ap_V (Equiv_O_reflector O A) (eissect (Equiv_O_reflector O A) (SMod.to O A a)) @@ 1) @
                   moveR_Vp (eisretr (Equiv_O_reflector O A) ((Equiv_O_reflector O A) (SMod.to O A a))) 1
                     (ap (Equiv_O_reflector O A) (eissect (Equiv_O_reflector O A) (SMod.to O A a)))
                     (eisadj (Equiv_O_reflector O A) (SMod.to O A a) @
                      (concat_p1 (ap (Equiv_O_reflector O A) (eissect (Equiv_O_reflector O A) (SMod.to O A a))))^))
                  (transport B (Equiv_η O A a)^ (f a))))))).
  Proof.
    intros O A B B_inO f a.
    Opaque Equiv_O_reflector.
    set (φ := Equiv_O_reflector O A) in *.
    Opaque Equiv_O_ind_internal.
    Opaque SMod.to.
    Opaque SMod.O_ind_internal.
    Opaque SMod.O_reflector.
    Opaque Equiv_In.
    cbn.
    rewrite !concat_1p.
    rewrite !ap_idmap.
    apply moveL_Vp. rewrite concat_p_pp.
    rewrite <- ap_pp.
    Transparent Equiv_O_ind_internal.
    unfold Equiv_O_ind_internal. cbn.
    match goal with
    |[|- Mod.O_ind_internal _ _ _ _ ?FF _ @ ?PP = _]
     => path_via (FF a @ PP)
    end.
    apply whiskerR.
    refine (Mod.O_ind_beta_internal _ _ _ _ _ _).
    rewrite !concat_pp_p. rewrite concat_Vp, concat_p1.
    cbn. apply moveR_Vp. rewrite !concat_p_pp. rewrite <- ap_pp.
    rewrite concat_p_Vp.
    rewrite !concat_pp_p.
    apply moveL_Mp. rewrite <- ap_V. rewrite !concat_p_pp.
    rewrite <- ap_pp.
    apply moveR_pM. fold φ.
    rewrite !concat_pp_p. apply moveL_Vp.
    match goal with
    |[|- _ = (transport2 B ?P1 _ @ (transport2 B ?P2 _)^)]
     => rewrite <- (transport2_V B P2);
         rewrite <- (transport2_p2p B P1 P2^);
         path_via (transport2 B (P1 @ P2^) (f a))
    end.
    rewrite concat_pV, concat_Vp. cbn.
    rewrite concat_1p. apply concat_pV.
  Qed.


End Equivalence_SMod_Mod.

  