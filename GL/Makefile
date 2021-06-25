%.vo : %.v
	coqc $*.v


# NOTE: some of these also depend on Coq files in ../general.
# Build those by "make general" in the current directory.

general :
	cd .. && make general && cd GL

GLS_PSGLS_calcs.vo : GLS_PSGLS_calcs.v ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo

GLS_PSGLS_dec.vo : GLS_PSGLS_dec.v GLS_PSGLS_calcs.vo ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo GLS_PSGLS_list_lems.vo ../general/strong_inductionT.vo GLS_PSGLS_remove_list.vo

GLS_PSGLS_list_lems.vo : GLS_PSGLS_list_lems.v ../general/genT.vo ../general/gen_tacs.vo ../general/List_lemmasT.vo ../general/existsT.vo GLS_PSGLS_calcs.vo

GLS_PSGLS_remove_list.vo : GLS_PSGLS_remove_list.v GLS_PSGLS_calcs.vo ../general/existsT.vo

GLS_additive_cut.vo : GLS_additive_cut.v GLS_PSGLS_calcs.vo ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo GLS_PSGLS_list_lems.vo ../general/strong_inductionT.vo PSGLS_termination_measure.vo PSGLS_termination.vo GLS_exch.vo GLS_wkn.vo GLS_ctr.vo GLS_PSGLS_remove_list.vo GLS_PSGLS_dec.vo GLS_inv_ImpR_ImpL.vo

GLS_ctr.vo : GLS_ctr.v GLS_PSGLS_calcs.vo ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo GLS_PSGLS_list_lems.vo ../general/dd_fc.vo ../general/strong_inductionT.vo GLS_inv_ImpR_ImpL.vo

GLS_exch.vo : GLS_exch.v GLS_PSGLS_calcs.vo ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo GLS_PSGLS_list_lems.vo ../general/strong_inductionT.vo

GLS_inv_ImpR_ImpL.vo : GLS_inv_ImpR_ImpL.v GLS_PSGLS_calcs.vo ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo GLS_PSGLS_list_lems.vo ../general/strong_inductionT.vo GLS_exch.vo GLS_wkn.vo GLS_PSGLS_remove_list.vo GLS_PSGLS_dec.vo

GLS_wkn.vo : GLS_wkn.v GLS_PSGLS_calcs.vo ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo GLS_PSGLS_list_lems.vo ../general/strong_inductionT.vo GLS_PSGLS_dec.vo

PSGLS_termination.vo : PSGLS_termination.v ../general/gen.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/gen_seq.vo ../general/List_lemmasT.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo GLS_PSGLS_list_lems.vo ../general/strong_inductionT.vo GLS_PSGLS_dec.vo PSGLS_termination_measure.vo GLS_PSGLS_remove_list.vo

PSGLS_termination_measure.vo : PSGLS_termination_measure.v GLS_PSGLS_calcs.vo ../general/genT.vo ../general/ddT.vo ../general/gen_tacs.vo ../general/existsT.vo ../general/univ_gen_ext.vo ../general/dd_fc.vo GLS_PSGLS_list_lems.vo GLS_PSGLS_remove_list.vo ../general/List_lemmasT.vo






clean_coq :
	rm -rf  *.vo *.glob *.v~

clean_general :
	cd ../general && rm *.vo *.glob && cd ../GL

clean_GL : clean_coq 

clean_all : clean_general clean_GL

clean_stray :
	rm *~

clean_win : 
	del /f *.vo *.glob
