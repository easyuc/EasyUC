                        Building the UC DSL Tool

To build the UC DSL tool ucdsl, first configure the tool by running

./configure

telling it the full pathname of the EasyCrypt distribution. If you
installed EasyCrypt using opam, it will be something like

/pathto/.opam/default/lib/easycrypt

Next, run

./build

to build the tool and copy the binary to ../bin/ucdsl.

To clean up the build state, you can run

./build-cleanup

(If you get to a state where ocamlbuild is complaining, running
./build-cleanup and then ./build often fixes the problem.)

You may want to add ../bin/ucdsl to your shell's search PATH.  Run
`ucdsl -help` for information about how to invoke the tool.

- - - - the rest of this file is in flux - - - -

to build makeTestCase:
ocamlbuild -use-ocamlfind makeTestCase.byte

to make a test case out of a /tests/testfile.uc :
./makeTestCase.byte testfile

to build tests:
ocamlbuild -use-ocamlfind tests.byte

to run tests:
./tests.byte


