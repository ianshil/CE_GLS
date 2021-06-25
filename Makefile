general: \
general/existsT.vo \
general/gstep.vo \
general/rtcT.vo \
general/gen_tacs.vo \
general/gen.vo \
general/genT.vo \
general/ddT.vo \
general/dd_fc.vo \
general/List_lemmasT.vo \
general/swappedT.vo \
general/gen_seq.vo \
general/strong_inductionT.vo \
general/univ_gen_ext.vo


general/gstep.vo: general/gstep.v general/dd_fc.vo general/rtcT.vo
general/rtcT.vo: general/rtcT.v general/genT.vo
general/gen.vo: general/gen.v
general/gen_tacs.vo: general/gen_tacs.v general/List_lemmasT.vo
general/existsT.vo: general/existsT.v
general/genT.vo: general/genT.v general/existsT.vo general/gen.vo
general/ddT.vo: general/ddT.v general/genT.vo 
general/dd_fc.vo: general/dd_fc.v general/ddT.vo
general/List_lemmasT.vo: general/List_lemmasT.v general/existsT.vo general/genT.vo general/gen.vo
general/swappedT.vo: general/swappedT.v general/gen_tacs.vo general/List_lemmasT.vo
general/gen_seq.vo: general/gen_seq.v general/gstep.vo general/swappedT.vo
general/strong_inductionT.vo: general/strong_inductionT.v
general/univ_gen_ext.vo: general/univ_gen_ext.v general/gen.vo general/genT.vo general/gen_tacs.vo general/gen_seq.vo general/List_lemmasT.vo

%.vo : %.v
	#echo doing $*.v >>log
	#dirname $* >>log
	(cd `dirname $*` ; pwd >> log ; coqc `basename $*.v`) 
	#pwd >> log
	# coqc -Q general "" -Q ll "" -Q modal "" -Q tense-lns "" $*.v

clean : 
	rm -rf  *.vo *.glob

clean_general : 
	cd general && rm -rf  *.vo *.glob && cd ..
