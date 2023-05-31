.PHONY: all clean

BIBS=$(shell ls *.bib)
DEPENDS=$(shell ls *.tex)
NAME=proof
all: fast

debug: $(NAME).tex $(DEPENDS) $(BIBS)
	pdflatex -draftmode -file-line-error $(NAME).tex $(DEPENDS)
	bibtex $(NAME)
	pdflatex -draftmode -interaction=batchmode $(NAME).tex $(DEPENDS)
	pdflatex -interaction=batchmode $(NAME).tex $(DEPENDS)

fast: $(NAME).tex $(DEPENDS) $(BIBS)
	pdflatex -draftmode -interaction=batchmode $(NAME).tex $(DEPENDS)
	bibtex $(NAME)
	pdflatex -draftmode -interaction=batchmode $(NAME).tex $(DEPENDS)
	pdflatex -interaction=batchmode $(NAME).tex $(DEPENDS)

open:
	pkill Preview || true && open $(NAME).pdf

clean:
	rm -rf *.aux *.blg *.log *.pdf *.toc *.snm *.out *.nav *.dvi *.lb *.fdb_latexmk *.fls *.bbl tags auto
