open Globnames

type modality = {
    mod_O : Constr.t;
    mod_univ : Constr.t;
    mod_univ_to_univ : Constr.t;
    mod_forall : Constr.t;
    mod_unit : Constr.t;
  }

type translator = global_reference Refmap.t

val translate : modality -> Environ.env -> Evd.evar_map -> Constr.t -> Constr.t * Evd.evar_map

val translate_type : modality -> Environ.env -> Evd.evar_map -> Constr.t -> Constr.t * Evd.evar_map
