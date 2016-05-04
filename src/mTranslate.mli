open Globnames

type modality = {
    mod_O : Constr.t;
    mod_univ : Constr.t;
    mod_univ_to_univ : Constr.t;
    mod_forall : Constr.t;
    mod_unit : Constr.t;
  }

type translator = global_reference Refmap.t

type forcing_context = {
    (* context : forcing_condition list; *)
    (** Forcing contexts are flagging variables of the rel_context in the same
    order. We statically know that variables coming from the introduction of
    a forcing condition come by pairs: the first one is a level, the second one
    a morphism. There is therefore only [Lift] condition for such pairs. *)
    modal : modality;
    (** Underlying category *)
    translator : translator;
    (** A map associating to all source constant a forced constant *)
  }


exception MissingGlobal of global_reference

val translate : modality -> Environ.env -> forcing_context -> Evd.evar_map -> Constr.t -> Constr.t * Evd.evar_map

val translate_type : modality -> Environ.env -> forcing_context -> Evd.evar_map -> Constr.t -> Constr.t * Evd.evar_map
