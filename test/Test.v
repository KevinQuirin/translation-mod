(* -*- coq-prog-name: "/Users/kquiri13/Code/Coq/HoTT8.5/HoTT/hoqtop"; proof-prog-name-ask: nil -*- *)

Require Import MTranslate.Modal.
Require Import HoTT.

Set Universe Polymorphism.
Set Primitive Projections.

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

  Context `{O:Modality}.
  
  Let Reflector  := O_reflector O.
  Let In'  : Type -> Type := In O.
  Let MType  := {x : Type & In' x}.
  Let U2U  := (pr1:MType -> Type).
  Let Forall  := (fun (A:MType) (B:A.1 -> MType) =>
                                ((forall x:A.1, (B x).1; inO_forall O A.1 (pr1 o B) (pr2 o B))): MType).
  Let OUnit  := ((Unit; inO_unit O) : MType).
  
  Modal Definition foo : forall X:Type, X as foo' using Reflector MType U2U Forall OUnit.

  
  

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
    _modal O Unit OUnit. cbn in *.    
    _modal O Bool OBool. cbn in OBool.
    _modal O x Ox.
    _modal O (forall X:Type, X) Ofoo. cbn in *.
    __modal O (forall x:Type, x -> x).    
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
        