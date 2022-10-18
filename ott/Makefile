OTTFILES1 = fiplus.ott compilation.ott
DOCNAME1  = doc

OTTFILES2 = fiplus.ott record.ott
DOCNAME2  = rec_doc

$(DOCNAME1).pdf: $(DOCNAME1).mng $(OTTFILES1)
	ott $(OTTFILES1) -o ott.tex \
		-tex_wrap false -tex_show_meta false \
		-tex_filter $(DOCNAME1).mng $(DOCNAME1).tex
	latexmk -pdf $(DOCNAME1)

$(DOCNAME2).pdf: $(DOCNAME2).mng $(OTTFILES2)
	ott $(OTTFILES2) -o record.tex \
		-tex_wrap false -tex_show_meta false \
		-tex_filter $(DOCNAME2).mng $(DOCNAME2).tex
	latexmk -pdf $(DOCNAME2)

.PHONY: clean
clean:
	latexmk -c
	rm -f *.tex
