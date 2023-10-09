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
ones with bad source addresses), attempts to send two messages in
sequence (without first getting control back), or simulators that
interfere with communication between the environment and adversary. We
are working on implementing a translator that will turn DSL code into
code in EasyCrypt's procedural programming language, automatically
generating message-routing boilerplate.  Security proofs will then be
carried out in EasyCrypt using the sequence of games approach.

Some examples are in the [`examples`](examples) subdirectory,
including the files in the subdirectory
[`smc-case-study`](examples/smc-case-study), which contains the
definitions of the functionalities and simulators of our SMC (secure
message transmission) case study.

The OCaml code for a lexer, parser, typechecker and interpreter for
the DSL can be found in the subdirectory
[`ucdsl-proj`](ucdsl-proj). It builds upon the EasyCrypt
implementation, and is distributed under the same software license.
The software is still under development. The translator into EasyCrypt
is yet to be written.

Building the UC DSL Tool
--------------------------------------------------------------------

The following instructions assume you have already installed the OCaml
Package Manager [opam](https://opam.ocaml.org),
[OCaml](https://ocaml.org), [Dune](https://dune.build), [OCaml
Batteries](https://ocaml-batteries-team.github.io/batteries-included/hdoc2/),
[Bisect_ppx](https://github.com/aantron/bisect_ppx)
[EasyCrypt](https://github.com/EasyCrypt/easycrypt) and [Proof
General](https://proofgeneral.github.io).  The easiest approach is to
start by installing `opam` and then [installing
EasyCrypt](https://github.com/EasyCrypt/easycrypt).  Then you must
only install `Bisect_ppx`, via the `opam` command: `opam install
bisect_ppx`.

Here are some more gentle [instructions for installing EasyCrypt and
getting the Emacs text editor to work with
it using Proof General](https://alleystoughton.us/easycrypt-installation.html).
In particular, these instructions explain how to tell Emacs
where to find the EasyCrypt executable on macOS.

To build the UC DSL tool `ucdsl`, first configure the tool by running

```
./configure
```

telling it the full pathname of the EasyCrypt `theories` directory.

Next, run

```
./build
```

to build the tool and copy the binary to `bin/ucdsl`.

Alternatively, run

```
./build-coverage
```

to build the tool with code coverage instrumentation turned on
and copy the binary to `bin/ucdsl`.

If you want to install `ucdsl` in the `opam` `bin` directory, you
can run

```
./install-opam
```

To clean up the build state, you can run

```
./build-cleanup
```

You may want to add `/pathto/bin/ucdsl` to your shell's search path.
Run`ucdsl -help` for information about how to invoke the tool.

Running UC DSL from the Command Line
--------------------------------------------------------------------

When run from the command line, `ucdsl` must be invoked on a single UC
DSL (`.uc`) file, which it will parse and typecheck. Error messages
and warning are output to the standard error output, and the final
exit status will be 0 if there are no errors, and 1 otherwise.

When one UC DSL file requires (`uc_require`s) another UC DSL file,
this makes the definitions of that file, plus those of all the
EasyCrypt theories and `.uc` files required (directly, or indirectly) by
that file available *with* explicit qualification.

Requiring an EasyCrypt theory makes the definitions of that theory,
plus those of all the EasyCrypt theories required (directly or
indirectly) by that theory, available. If a `+` is used, the
definitions of the theory itself are also made available *without*
qualification; but that does not apply to the definitions of
EasyCrypt theories indirectly required by that theory.

The `-units` command line option checks that a `.uc` file, and all the
files that are recursively `uc_required` when it is processed, are
*units*, where a unit is either:

* has one ideal functionality, no real functionalities and no
  simulators, and has no extraneous interfaces; or

* has one real functionality, one ideal functionality, one simulator,
  and no extraneous interfaces, where the real and ideal
  functionalities share the same composite direct interface, the
  simulator uses the ideal functionality's basic adversarial interface
  (which is not allowed to be a component of the real functionality's
  composite adversarial interface (if any)); the above implies that the
  simulator simulates the real functionality.

The search path for `.uc` and `.ec` files includes the current directory,
and can be extended with the `-include` (`-I`) option. E.g., `-I foo`
means to also search in subdirectory `foo`.

Emacs Major Mode for Editing UC DSL Files
--------------------------------------------------------------------

In the [`emacs`](emacs) subdirectory, there is a simple
[Emacs](https://www.gnu.org/software/emacs/) major mode for editing UC
DSL (`.uc`) files. Copy the file `ucdsl-mode.el` to Emacs's
`site-lisp` directory, and put the code

```
(require 'ucdsl-mode)
(add-to-list 'auto-mode-alist '("\\.uc\\'" . ucdsl-mode))
```

in your Emacs initialization file (typically `.emacs` in your
home directory).

The major mode provides simple syntax highlighting. To run the
`ucdsl` command on a `.uc` file, run `M-x compile`. `M-x next-error`
(bound to ``C-x` ``) takes you to the next error in the `*compilation*`
buffer, showing you the location of the error in your source file.

UC DSL Interpreter
--------------------------------------------------------------------

The UC DSL interpreter can (like EasyCrypt) be run either in batch
mode or interactively. Interpretation is guided by a script, placed in
a `.uci` file. In a script, one can load a `.uc` file. This checks
that this file, and all the UC DSL files that are recursively
`uc_required`, are units.  One can then enter a real functionality
expression, which is automatically turned into real and ideal worlds.
One can then select a world, and experiment with it by sending
messages, playing the role of the UC environment or
adversary. Assertions in the script can be used to check that an
excected message is output to the UC environment or adversary at some
stage of execution, or that failure happens at some stage, returning
control to the environment.

Scripts are developed in Emacs, with `ucdsl` running in interactive
mode as a client of [Proof
General](https://proofgeneral.github.io). This allows one to step
forward and backward in an interpretation script, much as one steps
forward and backward in an EasyCrypt proof. Once developed, a `.uci`
file can be checked in batch mode, by invoking `ucdsl` with the
`-batch` command line option. In batch mode, any errors or warnings
are output to the standard error output. If there are no errors,
the final exit status will be 0, otherwise it will be 1.

To set up Proof General to be able to work with `ucdsl`, you should carry
out the following steps:

* First, go to the Proof General subdirectory of your Emacs `elpa`
directory, which will be called something like
`.emacs.d/elpa/proof-general-20211217.1753` in your home directory.

* In this directory, create a new subdirectory, `ucInterpreter`. Copy
the file `ucInterpreter.el` of the [`emacs`](emacs) directory to
`ucInterpreter`.

* In the `generic` subdirectory, add following triple
to the existing `proof-site.el` file, putting this next to the triples
for proof assistants including `EasyCrypt` in the definition of
`proof-assistant-table-default`:

```
(ucInterpreter "UCInterpreter" "uci")
```

* Then (editing this file in Emacs) byte compile it using the command
`byte-compile-file` (run `M-x` `byte-compile-file` `RET` (return),
complete the filename, and type `RET`).

* Finally, on macOS, if you are running the application version of
Emacs, you will need to tell Emacs where to find the `ucdsl`
executable. Follow the approach detailed in [instructions for
installing EasyCrypt and getting the Emacs text editor to work with it
using Proof
General](https://alleystoughton.us/easycrypt-installation.html),
adding the path to `ucdsl` to the definition of `exec-path` and the
setting of the `PATH` variable.

Now you will be able to edit and interactively execute `.uci`
interpreter scripts using Proof General.

To learn how to use the interpreter, read and experiment with the
script `testing.uci` in [`smc2`](examples/smc2).

Unit Testing
--------------------------------------------------------------------

The subdirectory [`testing`](testing) contains a unit testing
framework, including a suite of test cases. This suite can
be used to check code coverage (see the above instructions for
building `ucdsl` with code coverage instrumentation turned on).

UC DSL Prelude
--------------------------------------------------------------------

The subdirectory [`prelude`](prelude) contains the files of the UC
DSL Prelude, which are first on the search path when `ucdsl` runs.
The file `UCBasicTypes.ec` is automatically `ec_required` last
when processing UC DSL files.

UC DSL Development
--------------------------------------------------------------------

To edit the source in Emacs, you'll want to install the following
`opam` packages:

```
opam install tuareg
opam install merlin
```

You'll also want to install the following Emacs packages, using the
Emacs package manager, [MELPA](https://melpa.org/#/). In Emacs, run
`package-refresh-contents`, and then use `package-install` to install
`tuareg`, `auto-complete` and `merlin`.

Finally, add

```
(require 'merlin)

(autoload 'merlin-mode "merlin" nil t nil)
(add-hook 'tuareg-mode-hook 'merlin-mode t)
```

to your `.emacs` file.
