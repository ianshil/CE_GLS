Instructions for compiling files up to and including GLS_additive_cut.v which contains cut-elimination.
=========================================================================================

1. Run "make general" which compiles all files found in ../general directory.

2. Run "make GLS_additive_cut.vo" which compiles all files in GL up to and including GLS_additive_cut.v.


NOTES
-----

In GL, each file has a specific role:

            GLS_PSGLS_calcs.v  ==>  defines the formal language, as well as the GLS and PSGLS calculi
      GLS_PSGLS_remove_list.v  ==>  defines the operation remove_list on list of formulae
        GLS_PSGLS_list_lems.v  ==>  states useful lemmas about list of formulae
              GLS_PSGLS_dec.v  ==>  shows that the applicability of the rules of GLS and PSGLS is decidable
                   GLS_exch.v  ==>  shows that GLS admits exchange
                    GLS_wkn.v  ==>  shows that GLS admits weakening
          GLS_inv_ImpR_ImpL.v  ==>  shows that the rules ImpR and ImpL are invertible in GLS
                    GLS_ctr.v  ==>  shows that GLS admits contraction
  PSGLS_termination_measure.v  ==>  defines the measure to show the termination of PSGLS
          PSGLS_termination.v  ==>  shows the termination of PSGLS
           GLS_additive_cut.v  ==>  shows that GLS admits cut
  



