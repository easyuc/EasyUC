- - - - the rest of this file is in flux - - - -

to build makeTestCase:
ocamlbuild -use-ocamlfind makeTestCase.byte

to make a test case out of a /tests/testfile.uc :
./makeTestCase.byte testfile

to build tests:
ocamlbuild -use-ocamlfind tests.byte

to run tests:
./tests.byte


