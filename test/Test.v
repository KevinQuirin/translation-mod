(* -*- coq-prog-name: "/Users/kquiri13/Code/Coq/HoTT8.5/HoTT/hoqtop"; proof-prog-name-ask: nil -*- *)

Require Import MTranslate.Modal.
Require Import HoTT.

Set Universe Polymorphism.
Set Primitive Projections.

(* Set Printing Universes. *)

(* Definition TypeO := Type. *)
(* Definition Reflector := fun T:Type => T:TypeO. *)
(* Definition U2U := fun T:TypeO => T:Type. *)
(* Definition Forall := fun (A:TypeO) (B:U2U A -> TypeO) => ((forall x:U2U A, U2U (B x)) : TypeO). *)
(* Definition OUnit := Unit : TypeO. *)
(* Definition OPath := fun (A:TypeO) (x y:A) => ((x = y) : TypeO). *)

(* Ltac _modal X id := modal Reflector TypeO U2U Forall OUnit OPath X as id. *)

(* Goal True. *)
(* Proof. *)
(*   _modal {T:Type & Unit} foo. *)
(*   _modal (Type = Type) bar. *)
(*   _modal (forall x:Unit, x = x) baz. unfold Forall, OUnit, U2U in baz; cbn in baz. *)
(* Abort. *)

(* Modal Definition foo: Bool using Refl Univ U2U Forall OUnit. *)
(* Proof. *)
(*   unfold U2U, Univ, Refl. cbn. *)
(*   exact true. *)
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

  Context {O:Modality}.
  Let Reflector  := fun X => (O_reflector O X; @O_inO O X).
  Let Eta := fun X a => to O X a.
  Let TypeO := ((Type_ O; inO_typeO O): Type_ O).
  Let U2U  := (pr1:Type_ O -> Type).
  Let Forall  := (fun (A:Type_ O) (B:A.1 -> Type_ O) =>
                                ((forall x:A.1, (B x).1; inO_forall O A.1 (pr1 o B) (pr2 o B))): Type_ O).
  Let OUnit := ((Unit; inO_unit O) : Type_ O).
  Let OPath := (fun (A:Type_ O) (x y:A) => (x = y; inO_paths O A.1 x y)).
  
  Ltac _modal X id :=
    modal Reflector Eta TypeO U2U Forall OUnit X OPath as id.

  Ltac __modal X :=
    modal_ Reflector Eta TypeO U2U Forall OUnit OPath X.

  (* Set Printing Universes. *)

  Modal Translate Bool using Reflector Eta TypeO U2U Forall OUnit OPath.

  Modal Definition negb : Bool -> Bool using Reflector Eta TypeO U2U Forall OUnit OPath.
  Proof.
    cbn.
    refine (O_functor _ _). exact negb.
  Defined.
  
  Modal Definition sum : forall (A B:Type), Type using Reflector Eta TypeO U2U Forall OUnit OPath.
  Proof.
    cbn.
    intros A B.
    refine (A -> B; _).
    apply inO_forall. exact fs.
    exact _.
  Defined.

  Modal Definition nat_rec : forall P : Type, P -> (nat -> P -> P) -> nat -> P using Reflector Eta TypeO U2U Forall OUnit OPath.
  Proof.
    intros P p f.
    cbn in *.
    refine (O_rec _).
    intro n; induction n.
    exact p. 
    exact (f (to O nat n) IHn).
  Defined.

  Modal Definition negb : Bool -> Bool using Reflector Eta TypeO U2U Forall OUnit OPath.
  Proof.
    cbn.
    refine (O_functor _ _). exact negb.
  Defined.
  
  Modal Definition foo : negb true = false using Reflector Eta TypeO U2U Forall OUnit OPath.
  Proof.
    cbn. unfold negbmodal.
    unfold O_functor, Eta. cbn.
    simple refine (O_rec_beta _ _).
  Defined.

  Inductive sum_ (A B:TypeO) : Type :=
  |inl_ : A.1 -> sum_ A B
  |inr_ : B.1 -> sum_ A B.

  Modal Definition sum : forall (A B:Type), Type using Reflector Eta TypeO U2U Forall OUnit OPath.
  Proof.
    cbn.
    intros A B. refine (O (sum_ A B); _).
    apply O_inO.
  Defined.
  
  Modal Definition inl : forall (A B:Type), A -> sum A B using Reflector Eta TypeO U2U Forall OUnit OPath.
  Proof.
    cbn. intros A B x.
    apply Eta. apply inl_. exact x.
  Defined.

  Context (X:Type).

    Modal Definition foo : X using Reflector Eta TypeO U2U Forall OUnit OPath.
  
    
    unfold U2U, Forall, OUnit, OPath, Eta. cbn.
  Defined.

  Print foomodal.
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
        