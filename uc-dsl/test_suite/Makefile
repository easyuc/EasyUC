default: main

main: main.native

%.native: 
	ocamlbuild -use-ocamlfind $@
	mv $@ $ dsl_test

.PHONY: default
