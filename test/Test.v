(* -*- coq-prog-name: "/Users/kquiri13/Code/Coq/HoTT8.5/HoTT/hoqtop"; proof-prog-name-ask: nil -*- *)

Require Import MTranslate.Modal.
Require Import HoTT.

Set Universe Polymorphism.
Set Primitive Projections.

(* Set Printing Universes. *)

Definition Univ := Type.
Definition Refl := fun T:Type => T:Univ.
Definition U2U := fun T:Univ => T:Type.
Definition Forall := fun (A:Univ) (B:U2U A -> Univ) => ((forall x:U2U A, U2U (B x)) : Univ).
Definition OUnit := Unit : Univ.

Ltac _modal X id := modal Refl Univ U2U Forall OUnit X as id.

Goal True.
  _modal Bool OBool. cbn in *. unfold Refl in OBool.
  _modal Type OType. cbn in *. unfold Univ in OType.
  _modal (Type -> Type) Of. cbn in Of.
  exact tt.
Qed.

(* Modal Definition foo: Bool using Refl Univ U2U Forall OUnit. *)
(* Proof. *)
(*   unfold U2U, Univ, Refl. cbn. *)
(*   exact true. *)
  
(* Defined. *)
(* (*   refine (exist _ _ _). *) *)
(*   exact (Unit;tt). *)
  
(*   exact true. *)
(* Qed. *)

Module Test (Mod:Modalities) (Acc:Accessible_Modalities Mod).
  Export Mod.
  Module Export Acc_Theory := Accessible_Modalities_Theory Mod Acc.
  Module Export Lex_Theory := Lex_Modalities_Theory Mod.
  Module Export AccLex_Theory := Accessible_Lex_Modalities_Theory Mod Acc.
  Module Export Mod_ReflectiveSubuniverses
  := Modalities_to_ReflectiveSubuniverses Mod.
  Module Export RSU
    := ReflectiveSubuniverses_Theory Mod_ReflectiveSubuniverses.
  
  Context `{lex: forall O:Modality, Lex O}.
  Context `{ua: Univalence}.
  Context `{fs: Funext}.


  (* Let In' (O:Modality) : Type -> Type := In O. *)
  (* Let MType (O:Modality) := {x : Type & In' O x}. *)

  Context {O:Modality}.
  Let Reflector  := fun X => (O_reflector O X; @O_inO O X).
  Let MType := Type_ O.
  Let TypeO := ((MType; inO_typeO O): Type_ O).
  Let U2U  := (pr1:Type_ O -> Type).
  Let Forall  := (fun (A:MType) (B:A.1 -> MType) =>
                                ((forall x:A.1, (B x).1; inO_forall O A.1 (pr1 o B) (pr2 o B))): MType).
  Let OUnit  := ((Unit; inO_unit O) : Type_ O).

  Modal Definition foo :Type using Reflector TypeO U2U Forall OUnit.
  unfold TypeO, U2U, MType. cbn.
  exact OUnit.
  exact tt.
  Defined.
  exact (O_functor O idmap).
  (* exact OUnit. *)
  Print MType. Print Type_.
  Defined.
  
  apply to. exact true.
  Defined.
  exact tt.
  Defined.
  Show Universes.
  exists Type.
  exists Unit.
  (* exact tt. *)
  
                            
  
  Ltac _modal O X id :=
    modal
      (fun A:Type => ((O A; @O_inO O A): MType O))
      ((MType O; inO_typeO O): MType O)
      (pr1:MType O -> Type)
      (fun (A:MType O) (B:A.1 -> MType O) =>
         ((forall x:A.1, (B x).1; inO_forall O A.1 (pr1 o B) (pr2 o B))): MType O)
      ((Unit; inO_unit O) : MType O)
      X
    as id.

  Ltac __modal O X :=
    modal_
      (fun A:Type => ((O A; @O_inO O A): MType O))
      ((MType O; inO_typeO O): MType O)
      (pr1:MType O -> Type)
      (fun (A:MType O) (B:A.1 -> MType O) =>
         ((forall x:A.1, (B x).1; inO_forall O A.1 (pr1 o B) (pr2 o B))): MType O)
      ((Unit; inO_unit O) : MType O)
      X.

      
  Goal forall (O:Modality) (A:Type) (x:A), True.
    intros O A x.
       
    _modal O x Ox.
    (* Set Printing Universes. *)
    _modal O (forall X:Type, X) Ofoo. cbn in *.
    _modal O (fun (X:Type) => X) Ofooo. cbn in *.
    _modal O (forall x:Type, x -> x) Obar.    
    _modal O Empty Oempty. cbn in *.
    _modal O Unit. cbn in *.
    _modal O nat. cbn in *.
    _modal O Type.
    _modal O (Type -> Type). cbn in *. 
    _modal O (forall x:Type, x). cbn in *.
    _modal O (forall x:Type, x -> x).
    _modal O ((fun x:Type => x) Type).
    
    _modal O (forall x:Type, Type -> x).
    _modal O ((fun x:Type => x) Type).
        