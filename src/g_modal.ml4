DECLARE PLUGIN "mTranslate"

TACTIC EXTEND modal
| [ "modal" reference(refl) reference(eta) reference(univ) reference(univ_to_univ) reference(forall) reference(depsum) reference(unit) reference(path) constr(c) "as" ident(id)] -> [
  let modality = {
      MTranslate.mod_O = refl;
      MTranslate.mod_eta = eta;
      MTranslate.mod_univ = univ;
      MTranslate.mod_univ_to_univ = univ_to_univ;
      MTranslate.mod_forall = forall;
      MTranslate.mod_sig = depsum;
      MTranslate.mod_unit = unit;
      MTranslate.mod_paths = path;
      }
  in	
  MPlugin.modal_tac_named modality c id
]
| [ "modal_" reference(refl) reference(eta) reference(univ) reference(univ_to_univ) reference(forall) reference(depsum) reference(unit) reference(path) constr(c)] -> [
  let modality = {
      MTranslate.mod_O = refl;
      MTranslate.mod_eta = eta;	
      MTranslate.mod_univ = univ;
      MTranslate.mod_univ_to_univ = univ_to_univ;
      MTranslate.mod_forall = forall;
      MTranslate.mod_sig = depsum;
      MTranslate.mod_unit = unit;
      MTranslate.mod_paths = path;	
      }
  in	
  MPlugin.modal_tac modality c
]
END


 VERNAC COMMAND EXTEND ModalTranslation CLASSIFIED AS SIDEFF
| [ "Modal" "Translate" global(gr) "using" global(refl) global(eta) global(univ) global(univ_to_univ) global(forall) global(depsum) global(unit) global(path) ] ->
  [ MPlugin.modal_translate (refl,eta,univ,univ_to_univ,forall,depsum,unit,path) gr None ]
| [ "Modal" "Translate" global(gr) "as" ne_ident_list(id) "using" global(refl) global(eta) global(univ) global(univ_to_univ) global(forall) global(depsum) global(unit) global(path)] ->
  [ MPlugin.modal_translate (refl,eta,univ,univ_to_univ,forall,depsum,unit,path) gr (Some id) ]
END


let classify_impl _ = Vernacexpr.(VtStartProof ("Classic",Doesn'tGuaranteeOpacity,[]), VtLater)


VERNAC COMMAND EXTEND ModalImplementation CLASSIFIED BY classify_impl
| [ "Modal" "Definition" ident(id) ":" lconstr(typ) "using" global(refl) global(eta) global(univ) global(univ_to_univ) global(forall) global(depsum) global(unit) global(path)] ->
  [ MPlugin.modal_implement (refl,eta,univ,univ_to_univ,forall,depsum,unit,path) id typ None ]
| [ "Modal" "Definition" ident(id) ":" lconstr(typ) "as" ident(id') "using" global(refl) global(eta) global(univ) global(univ_to_univ) global(forall) global(depsum) global(unit) global(path)] ->
  [ MPlugin.modal_implement (refl,eta,univ,univ_to_univ,forall,depsum,unit,path) id typ (Some id') ]
END
