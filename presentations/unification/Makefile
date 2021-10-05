PANDOC_FLAGS = -r markdown+emoji --mathjax -s --citeproc --slide-level 2

all: uni.html

%.html: %.pdc %.bib style-extra.css
	pandoc $(PANDOC_FLAGS) -w revealjs $< -o $@

%.tex: %.pdc %.bib
	pandoc $(PANDOC_FLAGS) -w beamer $< -o $@

%.pdf: %.tex
	latexmk -xelatex $<
