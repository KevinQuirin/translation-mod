DECLARE PLUGIN "mTranslate"

TACTIC EXTEND number_constr_inductive
| [ "one_constr" "of" constr(c) ] -> [
    Proofview.Goal.enter begin fun gl ->
      MTranslate.inductive_with_one_constr gl c
  end 
]		      
END

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
  MPlugin.force_tac modality c id
]
END