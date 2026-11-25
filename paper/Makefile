# Build the paper: `make` (needs pdflatex + bibtex, e.g. TeX Live), or `latexmk -pdf realfp.tex`.
realfp.pdf: realfp.tex refs.bib
	pdflatex -interaction=nonstopmode realfp.tex
	bibtex realfp
	pdflatex -interaction=nonstopmode realfp.tex
	pdflatex -interaction=nonstopmode realfp.tex

# Check every Lean snippet used in the paper (from a built checkout).
snippets:
	cd ../RealFPMathlib && lake lean ../paper/snippets/PaperSnippets.lean

clean:
	rm -f *.aux *.bbl *.blg *.log *.out *.toc *.fls *.fdb_latexmk

.PHONY: snippets clean
