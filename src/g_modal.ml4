DECLARE PLUGIN "mTranslate"

TACTIC EXTEND modal
| [ "modal" constr(refl) constr(univ) constr(univ_to_univ) constr(forall) constr(unit) constr(c) "as" ident(id)] -> [
  let modality = {
      MTranslate.mod_O = refl;
      MTranslate.mod_univ = univ;
      MTranslate.mod_univ_to_univ = univ_to_univ;
      MTranslate.mod_forall = forall;
      MTranslate.mod_unit = unit;
      }
  in	
  MPlugin.modal_tac_named modality c id
]
| [ "modal_" constr(refl) constr(univ) constr(univ_to_univ) constr(forall) constr(unit) constr(c)] -> [
  let modality = {
      MTranslate.mod_O = refl;
      MTranslate.mod_univ = univ;
      MTranslate.mod_univ_to_univ = univ_to_univ;
      MTranslate.mod_forall = forall;
      MTranslate.mod_unit = unit;
      }
  in	
  MPlugin.modal_tac modality c
]
END

let classify_impl _ = Vernacexpr.(VtStartProof ("Classic",Doesn'tGuaranteeOpacity,[]), VtLater)

VERNAC COMMAND EXTEND ModalImplementation CLASSIFIED BY classify_impl
| [ "Modal" "Definition" ident(id) ":" lconstr(typ) "using" global(refl) global(univ) global(univ_to_univ) global(forall) global(unit) ] ->
  [ MPlugin.modal_implement (refl,univ,univ_to_univ,forall,unit) id typ None ]
| [ "Modal" "Definition" ident(id) ":" lconstr(typ) "as" ident(id') "using" global(refl) global(univ) global(univ_to_univ) global(forall) global(unit) ] ->
  [ MPlugin.modal_implement (refl,univ,univ_to_univ,forall,unit) id typ (Some id') ]
END