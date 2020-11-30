UC DSL Source Directory
================================================================================

The subdirectory `ECsrc` contains a copy of the EasyCrypt source
(`src`) directory.

The files in this directory beginning with `ec` are EasyCrypt source
files that have been modified from the originals. The original
files can be found in `ECsrc/modified-for-ucdsl`.

Program Structure
--------------------------------------------------------------------------------

* [`ucdsl.ml`](ucdsl.ml) - UC DSL's main file

* [`ucConfig.ml.in`](ucConfig.ml.in) - source for configuration
  module, which `build` script turns into configuration module by
  making substitutions
  
* `UcUtils` ([`ucUtils.mli`](ucUtils.mli),
  [`ucUtils.ml`](ucUtils.ml)) - module with utility defintions

* `UcMessage` ([`ucMessage.mli`](`ucMessage.mli`),
  [`ucMessage.ml`](`ucMessage.ml`)) - module for error and warning
  messages

* `UcState` ([`ucState.mli`](ucState.mli),
  [`ucState.ml`](ucState.ml)) - module for the UC DSL global state

* `EcScope` ([`ecScope.mli`](ecScope.mli),
  [`ecScope.ml`](ecScope.ml)) - modification of EasyCrypt's scope
  module

* `EcCommands` ([`ecCommands.mli`](ecCommands.mli),
  [`ecCommands.ml`](ecCommands.ml)) - modification of EasyCrypt's
  commands module

* `UcEcInterface` ([`ucEcInterface.mli`](ucEcInterface.mli),
  [`ucEcInterface.ml`](ucEcInterface.ml)) - module providing
  interface with EasyCrypt

* `UcSpec` ([`ucSpec.ml`](ucSpec.ml)) -
  module defining specification parse trees

* `UcTypedSpec` ([`ucTypedSpec.ml`](ucTypedSpec.ml)) - module
  defining typed specifications

* [`ucLexer.mll`](ucLexer.mll) - UC DSL lexer, turned into `UcLexer`
  module by `mllex`

* [`ucParser.mly`](ucParser.mly) - UC DSL parser, turned into
  `UcParser` module by `menhir`

* `UcParseFile` ([`ucParseFile.mli`](ucParseFile.mli),
  [`ucParseFile.ml`](ucParseFile.ml)) - module for parsing a file

* `UcTypecheck` ([`ucTypecheck.mli`](ucTypecheck.mli),
  [`ucTypecheck.ml`](ucTypecheck.ml)) - module for typechecking a
  specification

* `UcParseAndTypecheckFile`
  ([`ucParseAndTypecheckFile.mli`](ucParseAndTypecheckFile.mli),
  [`ucParseAndTypecheckFile.ml`](ucParseAndTypecheckFile.ml)) -
  module for parsing and then typechecking a file

* `UcTransTypesExprs`
  ([`ucTransTypesExprs.mli`](ucTransTypesExprs.mli),
  [`ucTransTypesExprs.ml`](ucTransTypesExprs.ml)) - module for
  translating (and checking) types and expressions from concrete to
  abstract syntax

* `UcTypesExprsErrorMessages`
  ([`ucTypesExprsErrorMessages.mli`](ucTypesExprsErrorMessages.mli),
  [`ucTypesExprsErrorMessages.ml`](ucTypesExprsErrorMessages.ml)) -
  module for formatting error messages issued when translating types
  and expressions

Script for Comparing EasyCrypt Files with Originals
--------------------------------------------------------------------------------

The bash shell script [`ec-diff`](ec-diff) can be used to (run it with
no arguments):

* check whether any files in `ECsrc`, `ECsrc/phl` and `ECsrc/system` are
  different from the corresponding files of the current EasyCrypt `src`
  directory

* check whether the original versions of the `ec`* files in this
  directory that were saved in `ECsrc/modified-for-ucdsl` are the same
  as the corresponding files in the current EasyCrypt `src` directory

* do a diff of each of these `ec`* files with their original version
