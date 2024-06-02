OTTFILES2 = ../spec/rules.ott ../spec/target.ott
DOCNAME2  = rec_doc

$(DOCNAME2).pdf: $(DOCNAME2).mng $(OTTFILES2)
	ott $(OTTFILES2) -o record.tex \
		-tex_wrap false -tex_show_meta false \
		-tex_filter $(DOCNAME2).mng $(DOCNAME2).tex
	latexmk -pdf $(DOCNAME2)

.PHONY: clean
clean:
	latexmk -c
	rm -f *.tex
