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

Modal Definition foo: Bool using Refl Univ U2U Forall OUnit.
Proof.
  unfold U2U, Univ, Refl. cbn.
  exact true.
Abort.
(*
Error: Illegal application: 
The term "U2U" of type "Univ -> Type"
cannot be applied to the term
 "Refl Bool" : "Univ"
This term has type "Univ@{Top.303}" which should be coercible to
 "Univ@{Top.297}".
*)
(* Defined. *)

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

  Let In' (O:Modality) : Type -> Type := In O.
  Let MType (O:Modality) := {x : Type & In' O x}.
  
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

      
  (* Goal forall (O:Modality) (A:Type) (x:A), True. *)
  (*   intros O A x.        *)
  (*   _modal O Empty Oempty. cbn in *. *)
  (*   __modal O Unit. cbn in *. *)
  (*   __modal O nat. cbn in *. *)
  (*   __modal O Type. *)
  (*   __modal O (Type -> Type). cbn in *.  *)
  (*   __modal O (forall x:Type, x). cbn in *. *)
  (*   (* __modal O (forall x:Type, x -> x). *)  *)
  (*   (* __modal O ((fun x:Type => x) Type). *) *)
  (*   (* __modal O (forall x:Type, Type -> x). *) *)
  (*   (* __modal O ((fun x:Type => x) Type). *) *)
  (* Abort. *)

    Context {O:Modality}.
  Let Reflector  := fun X => (O_reflector O X; @O_inO O X).
  (* Let MType := Type_ O. *)
  Let TypeO := ((Type_ O; inO_typeO O): Type_ O).
  Let U2U  := (pr1:Type_ O -> Type).
  Let Forall  := (fun (A:Type_ O) (B:A.1 -> Type_ O) =>
                                ((forall x:A.1, (B x).1; inO_forall O A.1 (pr1 o B) (pr2 o B))): Type_ O).
  Let OUnit  := ((Unit; inO_unit O) : Type_ O).

  
  (* Set Printing All. *)
  (* Set Printing Universes. *)
  Polymorphic Modal Definition foo :Type using Reflector TypeO U2U Forall OUnit.
    unfold TypeO, U2U, MType. cbn.
    apply OUnit.
  Qed.
Check foomodal.  (*
    Anomaly: File "pretyping/evd.ml", line 407, characters 15-21: Assertion failed.
    Please report.
   *)
  Abort.
        