default: test_main

test_main: test_main.native

%.native: 
	ocamlbuild -use-ocamlfind $@
	mv $@ dsl-test

.PHONY: default
