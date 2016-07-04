(* -*- coq-prog-name: "/Users/kquiri13/Code/Coq/HoTT8.5/HoTT/hoqtop"; proof-prog-name-ask: nil; coq-prog-args: bt -*- *)

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

Module Test.
  Export ClT.

  (* Module Export Acc_Theory := Accessible_Modalities_Theory ClM . *)
  (* Module Export Lex_Theory := Lex_Modalities_Theory Mod. *)
  (* Module Export AccLex_Theory := Accessible_Lex_Modalities_Theory Mod Acc. *)
  (* Module Export Mod_ReflectiveSubuniverses *)
  (* := Modalities_to_ReflectiveSubuniverses Mod. *)
  (* Module Export RSU *)
  (*   := ReflectiveSubuniverses_Theory Mod_ReflectiveSubuniverses. *)
  
  (* Context `{lex: forall O:Modality, Lex O}. *)
  Context `{ua: Univalence}.
  Context `{fs: Funext}.

  Context {O:Modality}.
  Definition Reflector  := fun X:Type2le@{i a}
                           => (O_reflector@{u a i} O X; @O_inO@{u a i} O X).
  Definition Eta := fun X a => to O X a.
  Definition TypeO := ((Type_@{u a j i} O; inO_typeO O): Type_@{u a k j} O).
  Definition U2U  := (pr1:Type_@{u a j i} O -> Type@{j}).
  Definition Forall  := (fun (A:Type_@{u a j i} O@{u a}) (B:A.1 -> Type_@{u a j i} O@{u a}) =>
                           ((forall x:A.1, (B x).1; inO_forall O@{u a} A.1 (pr1 o B) (pr2 o B))): Type_@{u a j i} O@{u a}).
  Definition OUnit := (((Unit: Type@{i}); inO_unit O) : Type_@{u a j i} O).
  Definition OPath := (fun (A:Type_ O) (x y:A) => (x = y; inO_paths O A.1 x y)).

  Modal Definition foo : forall (f:Type -> Type), f Unit using Reflector Eta TypeO U2U Forall OUnit OPath.
  
  Ltac _modal X id :=
    modal Reflector Eta TypeO U2U Forall OUnit X OPath as id.

  Ltac __modal X :=
    modal_ Reflector Eta TypeO U2U Forall OUnit OPath X.

  (* Set Printing Universes. *)

  (* Bug1: Modal Translate pour les constantes *)
  Definition U1 := Type : Type.
  Modal Translate U1 using Reflector Eta TypeO U2U Forall OUnit OPath.

  (* Bug2: Pourquoi ça ne marche pas ? *)
  (* Let t := idpath : ((fun _ => TypeO) OUnit).1 = Type_ O. *)
  (* Set Debug Unification. *)
  (* Set Debug Tactic Unification. *)
  (* Set Printing Universes. *)
  (* Check (let x := TypeO in let y := TypeO in  *)
  (*  (Forall (Forall TypeO (fun _ : U2U _ => TypeO)) *)
  (*     (fun f : U2U (Forall TypeO (fun _ : U2U _ => x)) => *)
  (*      OUnit : y.1))). *)
  

cbn.  
Admitted.
Modal Translate Bool using Reflector Eta TypeO U2U Forall OUnit OPath.

  Definition Bool_m_rec (P:Type) (Pt: P) (Pf: P)
    : Bool_m -> P
    := fun b =>
         match b with
         |true_m => Pt
         |false_m => Pf
         end.

  (* Bug3: Conversion test raised an anomaly *)
  Modal Definition negb_m : Bool -> Bool using Reflector Eta TypeO U2U Forall OUnit OPath.
  Proof.
    cbn.
    refine (O_functor _ _).
    
    exact (Bool_m_rec Bool_m false_m true_m).

  (* Bug 4: Modal Translate pour les inductifs avec paramètres *)
  (* Modal Translate sum using Reflector Eta TypeO U2U Forall OUnit OPath. *)
  (* Modal Translate pour nat *)

  Definition foo := forall A, A -> A.
  Modal Translate foo using Reflector Eta TypeO U2U Forall OUnit OPath.
  
  
  Modal Translate nat using Reflector Eta TypeO U2U Forall OUnit OPath.
  