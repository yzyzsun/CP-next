COQMKFILENAME=CoqSrc.mk

FILES    = syntax_ott source_inf target_inf
VFILES   = $(foreach i, $(FILES), $(i).v)
VOFILES  = $(foreach i, $(FILES), $(i).vo)

.SECONDARY: $(VFILES)

coq: $(COQMKFILENAME) $(VFILES)
	@$(MAKE) -f CoqSrc.mk

quick:  $(COQMKFILENAME) $(VFILES)
	@$(MAKE) -f CoqSrc.mk quick

%.vo: %.v
	@$(MAKE) -f CoqSrc.mk $*.vo


OTT_LOC  = ../ott

syntax_ott.v: $(OTT_LOC)/source.ott $(OTT_LOC)/target.ott
	ott -i $(OTT_LOC)/source.ott -i $(OTT_LOC)/target.ott -o syntax_ott.v -coq_lngen true -coq_expand_list_types true
	@if grep '<<no parses (' $@ >/dev/null 2>&1 && \
	[ -z "$(DONTSTOP)" ]; then \
		echo; \
	echo "***** OTT PARSE ERROR(S) *****"; \
		grep -n '<<no parses (' $@; \
		$(RM) $@; \
		exit 1; \
	fi >&2


source_inf.v: $(OTT_LOC)/source.ott
	lngen --coq source_inf.v --coq-ott syntax_ott $(OTT_LOC)/source.ott

target_inf.v: $(OTT_LOC)/target.ott
	@echo "metavariables definition are uncommented in $(OTT_LOC)/target.ott to use lngen"
	sed 's/^%//' $(OTT_LOC)/target.ott > $(OTT_LOC)/target_tmp.ott
	lngen --coq target_inf.v --coq-ott syntax_ott $(OTT_LOC)/target_tmp.ott
	rm $(OTT_LOC)/target_tmp.ott


$(COQMKFILENAME): Makefile $(shell ls *.v)
	{ echo "-R . Top" ; ls *.v ; } > _CoqProject
	coq_makefile -arg '-w -deprecated,-fragile-hint-constr' -f _CoqProject -o $(COQMKFILENAME)


coqclean:
	rm -f .*.d *.conf .*.aux *.v-e *.v.d *.vo *.vok *.vos *.glob $(COQMKFILENAME)

ottclean:
	rm -f $(VFILES)

clean: coqclean

all: ottclean coq
