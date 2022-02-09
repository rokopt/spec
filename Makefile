cargo = $(env) cargo

serve:
	mdbook serve

build:
	mdbook build

dev-deps:
	$(cargo) install mdbook
	$(cargo) install mdbook-mermaid
	$(cargo) install mdbook-linkcheck

.PHONY: build serve dev-deps
