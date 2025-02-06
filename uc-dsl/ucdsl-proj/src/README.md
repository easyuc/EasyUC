UC DSL Source Directory
================================================================================

The subdirectory `ECsrc` contains a copy of the EasyCrypt source
(`src`) directory.

Program Structure
--------------------------------------------------------------------------------

* [`ucdsl.ml`](ucdsl.ml) - UC DSL's main file

* [`ucConfig.ml.in`](ucConfig.ml.in) - source for configuration
  module, which `build` script turns into configuration module
  (`ucConfig.ml`) by making substitutions
  
* `UcUtils` ([`ucUtils.mli`](ucUtils.mli),
  [`ucUtils.ml`](ucUtils.ml)) - module with utility defintions

* `UcMessage` ([`ucMessage.mli`](`ucMessage.mli`),
  [`ucMessage.ml`](`ucMessage.ml`)) - module for error and warning
  messages

* `UcState` ([`ucState.mli`](ucState.mli),
  [`ucState.ml`](ucState.ml)) - module for the UC DSL global state

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

* `UcInterpreter` ([`ucInterpreter.mli`](ucInterpreter.mli),
   [`ucInterpreter.ml`](ucInterpreter.ml)) - module implementing
  the semantics of the interpreter

* `UcInterpreterClient` ([`ucInterpreterClient.mli`](ucInterpreterClient.mli),
   [`ucInterpreterClient.ml`](ucInterpreterClient.ml)) - module implementing
  the client of the interpreter, which lets a user run the interpreter,
  either interactively via Proof General or in batch mode

* `UcEcFormEval` ([`ucEcFormEval.mli`](ucEcFormEval.mli),
   [`ucEcFormEval.ml`](ucEcFormEval.ml)) - module used by
   the interpreter to leverage EasyCrypt's proof engine for
   proving/disproving formulas and simplifying formulas

* `UcEasyCryptCommentMacros`
   ([`ucEasyCryptCommentMacros.mli`](ucEasyCryptCommentMacros.mli),
   [`ucEasyCryptCommentMacros.ml`](ucEasyCryptCommentMacros.ml)) -
   module implementing EasyCrypt comment macros

* `UcEasyCryptCommentMacrosTest
   ([`ucEasyCryptCommentMacrosTest.ml`](ucEasyCryptCommentMacrosTest.ml) -
   module for testing the EasyCrypt comments macros implementation
