The UC DSL uses some of the EasyCrypt's libraries.

If you want to run EasyCrypt inside utop, you might want to run
commands in utop_ec.txt

In order to compile, it is necessary to add a symbolic link "ECsrc"
pointing to the EC source directory.

If there is already a _build directory, first delete it.

--- not clear this is relevant anymore? ---
Furthermore, the file ecVersion.ml.in needs to be copied to
ecVersion.ml, so that both are contained in the EC /src/ directory.
---

(When building EasyCrypt itself, this is done by its makefile, we
don't have a makefile.) In order for the interface between the UC DSL
and EC to work there are two paths that need to be setup in
dlEcInterface.ml.

* ecTheoriesDir points to the directory that contains theories that
  come with EasyCrypt:

* ucTheoriesDir points to the directory that contains "user-defined"
  types and operators that are imported/required by UC DSL code.

The build configuration for ocamlbuild is contained in _tags and
myocamlbuild.ml files.

to build dlCheck:
ocamlbuild -use-ocamlfind dlCheck.byte

to run checks on a UC DSL file:
./dlCheck.byte filename.uc

to build makeTestCase:
ocamlbuild -use-ocamlfind makeTestCase.byte

to make a test case out of a /tests/testfile.uc :
./makeTestCase.byte testfile

to build tests:
ocamlbuild -use-ocamlfind tests.byte

to run tests:
./tests.byte


