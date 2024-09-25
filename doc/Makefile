FILE=resolute-copland

.PHONY: all clean

all: $(FILE).pdf

$(FILE).pdf: $(FILE).tex
	pdflatex $(FILE)
	bibtex $(FILE)
	pdflatex $(FILE)
	pdflatex $(FILE)

clean:
	rm -f *.aux *.bbl *.blg *.log *.out *.pdf
