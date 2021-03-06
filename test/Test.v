(* -*- coq-prog-name: "/Users/kquiri13/Code/Coq/HoTT8.5/HoTT/hoqtop"; proof-prog-name-ask: nil; coq-prog-args: ("-indices-matter") -*- *)


Require Import MTranslate.Modal.
Require Import HoTT.

(* Set Universe Polymorphism. *)
(* Set Primitive Projections. *)

Module Modid.

  (* Unset Universe Polymorphism. *)
  Definition Reflector := (fun X => X) : Type@{i} -> Type@{i}.
  Definition Eta := fun (X:Type) (a:X) => a.
  Definition TypeO := Type.
  Definition U2U := (fun X => X) : Type@{i} -> Type@{j}.
  Definition Forall := (fun (A:Type) (B:A -> Type) => forall x:A, B x).
  Definition Sig := (fun (A:Type) (B:A -> Type) =>  {x:A & B x}).
  Definition OUnit := Unit.
  Definition OPath := fun (A:Type@{i}) (x y:A) => (x = y : Type@{i}).


  Modal Translate Bool using Reflector Eta TypeO U2U Forall Sig OUnit OPath.
  Modal Translate nat using Reflector Eta TypeO U2U Forall Sig OUnit OPath.

  Inductive I (A:Type) :=
  |C : A -> I A.

  (* Modal Translate I using Reflector Eta TypeO U2U Forall OUnit OPath. *)

  
  (* Set Printing Universes. *)
  Modal Translate sum using Reflector Eta TypeO U2U Forall Sig OUnit OPath.

  Modal Definition foo : nat + Bool using Reflector Eta TypeO U2U Forall Sig OUnit OPath.
  compute.
  Abort.
  
End Modid.

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
  (* Set Printing Universes. *)
  (* Definition Reflector  := fun X:Type2le@{i a} *)
  (*                          => (O_reflector@{u a i} O X; @O_inO@{u a i} O X). *)
  (* Definition Eta := fun X a => to O X a. *)
  (* Definition TypeO := ((Type_@{u a j i} O; inO_typeO@{i u k k k k k k k k a j} O): Type_@{u a k j} O). *)
  (* Definition U2U  := (pr1:Type_@{u a j i} O -> Type@{j}). *)
  (* Definition Forall := (fun (A:Type_@{u a j i} O@{u a}) (B:A.1 -> Type_@{u a j i} O@{u a}) => *)
  (*                          ((forall x:A.1, (B x).1; inO_forall@{u a i i i i j i} O@{u a} A.1 (pr1 o B) (pr2 o B))): Type_@{u a j i} O@{u a}). *)
  (* Definition OUnit := (((Unit: Type@{i}); inO_unit@{u a i i} O) : Type_@{u a j i} O). *)
  (* Definition OPath := (fun (A:Type_ O) (x y:A) => (x = y; inO_paths O A.1 x y)). *)

  (* Set Printing Universes. *)


  (* Monomorphic Definition U := Type@{i} : Type@{i}. *)
  
  Definition Reflector
    := fun X:Type => (O_reflector O X : Type; @O_inO O X)
               : {T:Type & In O T}.
  Definition Eta := fun X a => to O X a.
  Definition TypeO := ((Type_ O; inO_typeO O): Type_ O).
  Definition U2U  := (pr1:Type_ O -> Type).
  Definition Forall := (fun (A:Type_ O) (B:A.1 -> Type_ O) =>
                          ((forall x:A.1, (B x).1; inO_forall O A.1 (pr1 o B) (pr2 o B))): Type_ O).
  Definition Sig := (fun (A:Type_ O) (B:A.1 -> Type_ O) =>
                       (({x:A.1 & (B x).1}; @inO_sigma O A.1 (pr1 o B) A.2 (pr2 o B))): Type_ O).
  Definition OUnit := (((Unit: Type); inO_unit O) : Type_ O).
  Definition OPath := (fun (A:Type_ O) (x y:A) => (x = y; inO_paths O A.1 x y)).

 
 
  (* Modal Definition foo : forall (f:Type -> Type), f Unit  using Reflector Eta TypeO U2U Forall Sig OUnit OPath. *)

  (* Modal Definition foo : idmap Type using Reflector Eta TypeO U2U Forall Sig OUnit OPath. *)
  (* Proof. *)
  (*   cbn. *)
  (*   exact OUnit. *)
  (* Defined. *)
  
  Ltac _modal X id :=
    modal Reflector Eta TypeO U2U Forall Sig OUnit X OPath as id.

  Ltac __modal X :=
    modal_ Reflector Eta TypeO U2U Forall Sig OUnit OPath X.

  (* Set Printing Universes. *)

  (* Bug1: Modal Translate pour les constantes *)
  Definition U1 := Type : Type.
                            
  Modal Translate U1 using Reflector Eta TypeO U2U Forall Sig OUnit OPath.

  (* Bug2: Pourquoi ça ne marche pas ? *)
  (* Let t := idpath : ((fun _ => TypeO) OUnit).1 = Type_ O. *)
  (* Set Debug Unification. *)
  (* Set Debug Tactic Unification. *)
  (* Set Printing Universes. *)
  (* Check (let x := TypeO in let y := TypeO in  *)
  (*  (Forall Sig (Forall TypeO (fun _ : U2U _ => TypeO)) *)
  (*     (fun f : U2U (Forall TypeO (fun _ : U2U _ => x)) => *)
  (*      OUnit : y.1))). *)
  
  Modal Translate Bool using Reflector Eta TypeO U2U Forall Sig OUnit OPath.
  Modal Translate nat using Reflector Eta TypeO U2U Forall Sig OUnit OPath.
  Modal Translate sum using Reflector Eta TypeO U2U Forall Sig OUnit OPath.
  (* Modal Translate sig using Reflector Eta TypeO U2U Forall Sig OUnit OPath. *)
  (* Modal Translate Unit using Reflector Eta TypeO U2U Forall Sig OUnit OPath. *)
  (* Set Printing All. *)
  (* Set Printing Universes. *)

  Inductive q (A:Type) :=
  |qq : A -> Unit -> q A.
  Modal Translate q using Reflector Eta TypeO U2U Forall Sig OUnit OPath.
  
  Modal Definition fo : q Unit using Reflector Eta TypeO U2U Forall Sig OUnit OPath.
  
  cbn.
  __modal (S 0).
  
  unfold Eta.

 Modal Definition foo : ((tt;tt) : {_ : Unit & Unit}) = (tt;tt) using Reflector Eta TypeO U2U Forall Sig OUnit OPath.
 cbn.
 reflexivity.
  Defined.
 exists (to O Bool_modind true_modind).
 exact (to O Bool_modind true_modind).
 Defined.
  intros x.
  destruct x0. reflexivity.
  apply Eta.
  apply inl_modind.
  compute. exact tt.
  Defined.

  Inductive qux : Type :=
  |bar : qux
  |baz : qux -> qux.

  
  
  Modal Translate qux using Reflector Eta TypeO U2U Forall Sig OUnit OPath.
Modal Definition foo : qux using Reflector Eta TypeO U2U Forall Sig OUnit OPath.
  
  Definition Bool_m_rec (P:Type) (Pt: P) (f: P)
    : Bool_m -> P
    := fun b =>
         match b with
         |true_m => Pt
         |false_m => Pf
         end.

  (* Bug3: Conversion test raised an anomaly *)
  Modal Definition negb_m : Bool -> Bool using Reflector Eta TypeO U2U Forall Sig OUnit OPath.
  Proof.
    cbn.
    refine (O_functor _ _).
    
    exact (Bool_m_rec Bool_m false_m true_m).

  (* Bug 4: Modal Translate pour les inductifs avec paramètres *)
  (* Modal Translate sum using Reflector Eta TypeO U2U Forall Sig OUnit OPath. *)
  (* Modal Translate pour nat *)

  Definition foo := forall A, A -> A.
  Modal Translate foo using Reflector Eta TypeO U2U Forall Sig OUnit OPath.
  
  
  Modal Translate nat using Reflector Eta TypeO U2U Forall Sig OUnit OPath.
  