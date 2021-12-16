OTTFILES = lambdai.ott minijs.ott
DOCNAME  = doc

$(DOCNAME).pdf: $(DOCNAME).mng $(OTTFILES)
	ott $(OTTFILES) -o ott.tex \
		-tex_wrap false -tex_show_meta false \
		-tex_filter $(DOCNAME).mng $(DOCNAME).tex
	latexmk -pdf $(DOCNAME)

.PHONY: clean
clean:
	latexmk -c
	rm -f *.tex
