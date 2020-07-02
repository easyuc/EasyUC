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
translator into EasyCrypt is yet to be written. To build the DSL tool,
`ucdsl`, see the instructions in the subdirectory `src`. The
executable will then be in the `bin` subdirectory. Run `ucdsl -help`
for information about how to invoke the tool.
