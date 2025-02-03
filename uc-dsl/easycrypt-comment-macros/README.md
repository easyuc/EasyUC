EasyCrypt Comment Macros Examples
====================================================================

This directory contains some examples of EasyCrypt files
containing EasyCrypt comment macros.

Run the executable
```
../ucdsl-proj/_build/default/src/ucEasyCryptCommentMacrosTest.exe
```
to see how the macros work. This is called `<exec>` below.

Running
```
<exec> ec-comment-mac-examp.ec
```
scans and checks the file, and prints out the macros found.

Running
```
<exec> ec-comment-mac-examp.ec Foo hi bye hello-goodbye
```
applies the macro `Foo` to the arguments `hi`, `bye` and `hello-goodbye`,
printing the result.

See the file `ucEasyCryptCommentMacros.mli` for documentation.
