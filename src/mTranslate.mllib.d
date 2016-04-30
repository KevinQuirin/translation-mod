src/mTranslate_MLLIB_DEPENDENCIES:= src/mTranslate src/mPlugin src/g_modal
src/mTranslate.cma:$(addsuffix .cmo,$(src/mTranslate_MLLIB_DEPENDENCIES))
src/mTranslate.cmxa src/mTranslate.cmxs:$(addsuffix .cmx,$(src/mTranslate_MLLIB_DEPENDENCIES))
