all: vision-paper cryptoeconomics-paper implementation-overview-paper whitepaper

vision-paper: src/vision-paper.md
	pandoc --pdf-engine xelatex --biblio src/vision-paper.bib --csl aux/ieee.csl --template=aux/template.latex --mathjax --toc --number-sections --filter pandoc-include --citeproc -f markdown -o rendered/vision-paper.pdf src/vision-paper.md

cryptoeconomics-paper: src/cryptoeconomics-paper.md
	pandoc --pdf-engine xelatex --biblio src/cryptoeconomics-paper.bib --csl aux/ieee.csl --template=aux/template.latex --mathjax --toc --number-sections --filter pandoc-include --citeproc -f markdown -o rendered/cryptoeconomics-paper.pdf src/cryptoeconomics-paper.md

implementation-overview-paper: src/implementation-overview-paper.md
	pandoc --pdf-engine xelatex --biblio src/implementation-overview-paper.bib --csl aux/ieee.csl --template=aux/template.latex --mathjax --toc --number-sections --filter pandoc-include --citeproc -f markdown -o rendered/implementation-overview-paper.pdf src/implementation-overview-paper.md

whitepaper: src/whitepaper.md
	pandoc --pdf-engine xelatex --biblio src/whitepaper.bib --csl aux/ieee.csl --template=aux/template.latex --mathjax --toc --number-sections --filter pandoc-include --citeproc -f markdown -o rendered/whitepaper.pdf src/whitepaper.md

spellcheck:
	find ./src -type f -name "*.md" -exec aspell -p ./misc/aspell_dict -x -d en_US -c {} \;

.PHONY: all vision-paper cryptoeconomics-paper implementation-overview-paper whitepaper spellcheck
