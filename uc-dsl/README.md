UC Domain Specific Language
====================================================================

This directory contains a prototype of the implementation of a domain
specific language (DSL) for expressing functionalities (protocols and
ideal functionalities) and simulators. The DSL will allow crypto
theorists to easily write and understand functionalities and
simulators.

The DSL design was driven by the expression of functionalities and
simulators in our EasyCrypt architecture for UC.  But it allows
expression at a much higher level, avoiding all the message-routing
boilerplate.

DSL type-checking will catch errors like badly formed messages (e.g.,
ones with bad source addresses) or simulators that interfere with
communication between environment and adversary. When DSL code is
translated into EasyCrypt's procedural programming language,
message-routing boilerplate will be automatically generated.

As an example, the file [`case-study.uc`](case-study.uc) contains the
definitions of the functionalities and simulators of our SMC (secure
message transmission) case study. It makes use of the definitions
in [an EasyCrypt theory](KeysExponentsAndPlainTexts.ec).

The OCaml code for a lexer and parser of the DSL can be found in the
subdirectory [`src`](src). The software is still under development.  A
translator into EasyCrypt is yet to be written.

Building the UC DSL Tool
--------------------------------------------------------------------

To build the UC DSL tool `ucdsl`, first configure the tool by running

     ./configure

telling it the full pathname of the EasyCrypt distribution. If you
installed EasyCrypt using `opam`, it will be something like

     /pathto/.opam/default/lib/easycrypt

Next, run

     ./build

to build the tool and copy the binary to `bin/ucdsl`.

To clean up the build state, you can run

     ./build-cleanup

(If you get to a state where `ocamlbuild` is complaining, running
`./build-cleanup` and then `./build` often fixes the problem.)

You may want to add `/pathto/bin/ucdsl` to your shell's search path.  Run
`ucdsl -help` for information about how to invoke the tool.

Files
--------------------------------------------------------------------

The file:

* `_tags` contains the `ocamlbuild` tags for the project (`ocamlbuild`
  is used by the `build` script).

* `.merlin` contains the configuration file for Merlin, a plugin
  to `emacs` and `vim` for assisting in the editing of OCaml code
  (e.g., learning the types of expressions).
