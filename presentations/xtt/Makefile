PANDOC_FLAGS = -r markdown+emoji --mathjax -s --citeproc --slide-level 2

all: xtt.html

%.html: %.pdc style-extra.css
	pandoc $(PANDOC_FLAGS) -w revealjs $< -o $@

%.tex: %.pdc
	pandoc $(PANDOC_FLAGS) -w beamer $< -o $@

%.pdf: %.tex
	latexmk -xelatex $<
