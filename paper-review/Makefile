.PHONY : clean cleanpdfs cleandist all

TARGET=report

all: report.pdf slides.pdf

slides: slides.pdf

report.pdf: $(wildcard *.tex) $(wildcard *.bib)
	- pdflatex -halt-on-error -shell-escape $(TARGET)
	- bibtex  $(TARGET)
	- pdflatex -halt-on-error -shell-escape $(TARGET)
	pdflatex -halt-on-error -shell-escape $(TARGET)

slides.pdf: $(wildcard *.tex)
	pdflatex -halt-on-error -shell-escape slides.tex

clean:
	rm -f *.eps
	rm -f *.aux *.log *.out *.bbl *.blg *~ *.bak *.ps
	rm -f *.brf *.lof *.lot *.toc *.glo *.ist
	rm -f *.nav *.snm *.vrb
	rm -rf _minted-* .auctex-auto

cleanpdfs:
	rm -f $(TARGET).pdf
	rm -f slides.pdf

cleandist: clean cleanpdfs
