(* -*- coq-prog-name: "/Users/kquiri13/Code/Coq/HoTT8.5/HoTT/hoqtop"; proof-prog-name-ask: nil -*- *)

Require Import MTranslate.Modal.
Require Import HoTT.

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

  Ltac _modal O X :=
    modal
      (fun A:Type => (O A; @O_inO O A))
      ((MType O; inO_typeO O): MType O)
      (pr1:MType O -> Type)
      (fun (A:MType O) (B:A.1 -> MType O) =>
         ((forall x:A.1, (B x).1; inO_forall O A.1 (pr1 o B) (pr2 o B))): MType O)
      X.
  
      Goal forall (O:Modality) (A:Type), True.
        intros O A.
        _modal O Bool.
        _modal O Type.
        _modal O (Type -> Type). cbn in *. 
        _modal O (forall x:Type, x). cbn in *.
        _modal O (forall x:Type, x -> x).
        _modal O ((fun x:Type => x) Type).
        
        _modal O (forall x:Type, Type -> x).
        _modal O ((fun x:Type => x) Type).
  