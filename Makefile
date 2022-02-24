cargo = $(env) cargo

serve:
	mdbook serve

build:
	mdbook build

dev-deps:
	$(cargo) install mdbook
	$(cargo) install mdbook-mermaid
	$(cargo) install mdbook-linkcheck
	$(cargo) install --git "https://github.com/lzanini/mdbook-katex"

.PHONY: build serve dev-deps
