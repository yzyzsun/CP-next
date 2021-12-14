doc.pdf: doc.mng lambdai.ott
	ott -i lambdai.ott -o lambdai.tex \
		-tex_wrap false -tex_show_meta false \
		-tex_filter doc.mng doc.tex
	latexmk -pdf doc

.PHONY: clean
clean:
	latexmk -c
	rm -f *.tex
