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

Some examples are in the [`examples`](examples) subdirectory,
including the file [`case-study.uc`](examples/case-study.uc) contains
the definitions of the functionalities and simulators of our SMC
(secure message transmission) case study.

The OCaml code for a lexer and parser of the DSL can be found in the
subdirectory [`src`](src). The software is still under development.  A
translator into EasyCrypt is yet to be written.

Building the UC DSL Tool
--------------------------------------------------------------------

The following instructions assume you have already installed
[OCaml](https://ocaml.org), the OCaml Package Manager
[`opam`](https://opam.ocaml.org), and
[EasyCrypt](https://github.com/EasyCrypt/easycrypt).

To build the UC DSL tool `ucdsl`, first configure the tool by running

> ./configure

telling it the full pathname of the EasyCrypt distribution. If you
installed EasyCrypt using `opam`, it will be something like

> /pathto/.opam/default/lib/easycrypt

Next, run

> ./build

to build the tool and copy the binary to `bin/ucdsl`.

To clean up the build state, you can run

> ./build-cleanup

(If you get to a state where `ocamlbuild` is complaining, running
`./build-cleanup` and then `./build` often fixes the problem.)

You may want to add `/pathto/bin/ucdsl` to your shell's search path.  Run
`ucdsl -help` for information about how to invoke the tool.

Emacs Major Mode for editing UC DSL files
--------------------------------------------------------------------

In the [`emacs`](emacs) subdirectory, there is a simple Emacs major
mode for editing UC DSL (`.uc`) files. Copy the file `ucdsl-mode.el`
to Emacs's `site-lisp` directory, and put the code

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

Files
--------------------------------------------------------------------

The file:

* `.merlin` contains the configuration file for
  [Merlin](https://github.com/ocaml/merlin), a plugin to `emacs` and
  `vim` for assisting in the editing of OCaml code (e.g., learning the
  types of expressions).

* `_tags` contains the `ocamlbuild` tags for the project (`ocamlbuild`
  is used by the `build` script).

* `myocamlbuild.ml` is the project's `ocamlbuild` plugin, customizing
  its behavior.
