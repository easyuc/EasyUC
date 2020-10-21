default: main

main: main.native

%.native: 
	ocamlbuild -use-ocamlfind $@
	mv $@ dsl-test

.PHONY: default
