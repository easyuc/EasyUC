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
interfere with communication between the environment and adversary. When
DSL code is translated into EasyCrypt's procedural programming
language, message-routing boilerplate will be automatically generated.

Some examples are in the [`examples`](examples) subdirectory,
including the files in the subdirectory
[`smc-case-study`](examples/smc-case-study), which contains the
definitions of the functionalities and simulators of our SMC (secure
message transmission) case study.

The OCaml code for a lexer, parser and typechecker for the DSL can be
found in the subdirectory [`ucdsl-proj`](ucdsl-proj). It builds upon
the EasyCrypt implementation, and is distributed under the same
software license.  The software is still under development.  A
debugger is being written, and the translator into EasyCrypt is yet
to be written.

Building the UC DSL Tool
--------------------------------------------------------------------

The following instructions assume you have already installed the OCaml
Package Manager [opam](https://opam.ocaml.org),
[OCaml](https://ocaml.org), [Dune](https://dune.build), [OCaml
Batteries](https://ocaml-batteries-team.github.io/batteries-included/hdoc2/),
[Bisect_ppx](https://github.com/aantron/bisect_ppx) and
[EasyCrypt](https://github.com/EasyCrypt/easycrypt).  The easiest
approach is to start by installing `opam` and then [installing
EasyCrypt](https://github.com/EasyCrypt/easycrypt).  Then you must
only install `Bisect_ppx`, via the `opam` command: `opam install
bisect_ppx`.

Here are some more gentle [instructions for installing EasyCrypt and
getting the Emacs text editor to work with
it](https://alleystoughton.us/easycrypt-installation.html).

The UC DSL source is compatible with `why3` (installed as part of the
EasyCrypt installation) version 1.6.0. (Note that running `ucdsl`
doesn't actually run `why3` or even rely on `why3` being
configured. But because the DSL's implementation is built on that of
EasyCrypt, the build process may fail if the wrong version of `why3`
is installed.)

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

You may want to add `/pathto/bin/ucdsl` to your shell's search path.  Run
`ucdsl -help` for information about how to invoke the tool.

To edit the source in Emacs, you'll want to install the following
`opam` packages:

```
opam install tuareg
opam install merlin
```

You'll also want to install the following Emacs packages, using the Emacs
package manager, [MELPA](https://melpa.org/#/).  If you haven't
already added

```
(require 'package)
(add-to-list 'package-archives '("melpa" . "https://melpa.org/packages/") t)
(package-initialize)
```

to your `.emacs` customization file, you should do so. In Emacs, run
`package-refresh-contents`, and then use `package-install` to install
`tuareg`, `auto-complete` and `merlin`.

Finally, add

```
(require 'merlin)

(autoload 'merlin-mode "merlin" nil t nil)
(add-hook 'tuareg-mode-hook 'merlin-mode t)
```

to your `.emacs` file.

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
