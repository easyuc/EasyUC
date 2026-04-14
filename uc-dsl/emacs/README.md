Emacs Lisp Code
================================================================================

See [README.md](../README.md) for how to use the Emacs Lisp files
`ucdsl-mode.el` and `ucdsl-interpreter.el`.

The file `easycrypt-syntax.el` can replace the file of the same
name in the EasyCrypt Proof General code. This will allow
EasyCrypt lemma names beginning with `_`, which EasyUC uses. Put this
file in the EasyCrypt subdirectory of the Proof General code,
and byte compile it. (The directory will be something like
`.emacs.d/elpa/proof-general-20211217.1753/easycrypt` of your
home directory.)
