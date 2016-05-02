open Names
open Libnames
open Proofview

val modal_tac : MTranslate.modality -> Constr.t -> unit tactic

val modal_tac_named : MTranslate.modality -> Constr.t -> Id.t -> unit tactic

(* val modal_translate : (reference * reference) -> reference -> Id.t list option -> unit *)

val modal_implement : (reference * reference * reference * reference * reference) -> Id.t -> Constrexpr.constr_expr -> Id.t option -> unit
