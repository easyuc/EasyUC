UC DSL Source Directory
================================================================================

The subdirectory `ECsrc` contains a copy of the EasyCrypt source
(`src`) directory.

The files in this directory beginning with `ec` are EasyCrypt source
files that have been modified from the originals. The original
files can be found in `ECsrc/modified-for-ucdsl`.

Program Structure
--------------------------------------------------------------------------------

* `ucdsl.ml` - UC DSL's main file

* `ucConfig.ml.in` - source for configuration module, which `build` script
  turns into configuration module by making substitutions
  
* `UcConfig` - configuration module

* `UcUtils` - module with utility defintions

* `UcMessage` - module for error and warning messages

* `UcState` - module for the UC DSL global state

* `EcScope` - modification of EasyCrypt's scope module

* `EcCommands` - modification of EasyCrypt's commands module

* `UcEcInterface` - module providing interface with EasyCrypt

* `UcSpec` - module defining specification parse trees

* `UcTypedSpec` - module definining typed specifications

* `ucLexer.mll` - UC DSL lexer, turned into `UcLexer` module by
  `mllex`

* `ucParser.mly` - UC DSL parser, turned into `UcParser` module by
  `menhir`

* `UcParseFile` - module for parsing a file

* `UcTypecheck` - module for typechecking a specification

* `UcParseAndTypecheckFile` - module for parsing and then typechecking
  a file

* `UcTypecheckTypesExprs` - module for typechecking types and expressions

* `UcTypesExprsErrorMessages` - module for formatting error messages
  issued when typechecking types and expressions

Script for Comparing EasyCrypt Files with Originals
--------------------------------------------------------------------------------

The bash shell script `ec-diff` can be used to (run it with no
arguments):

* check whether any files in `ECsrc`, `ECsrc/phl` and `ECsrc/system` are
  different from the corresponding files of the current EasyCrypt `src`
  directory

* check whether the original versions of the `ec`* files in this
  directory that were saved in `ECsrc/modified-for-ucdsl` are the same
  as the corresponding files in the current EasyCrypt `src` directory

* do a diff of each of these `ec`* files with their original version
