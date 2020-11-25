UC DSL Unit Testing Framework
====================================================================

This directory contains the implementation of a framework for carrying
out unit tests of the UC DSL tool, as well as a comprehensive suite of
unit tests.

The testing tool, `dsl-test`, is invoked with the name of a directory
containing unit tests. This directory hierarchy (the directory, its
subdirectories, their subdirectories, etc.) will be searched for unit
tests, which are then executed. When `dsl-test` is invoked, it will
describe its actions with levels of verbosity controlled by
command-line arguments (see below). It will also generate a log file,
`log`, in the current directory.

* Unit tests are directories containing a file `TEST` (see below for
  its structure). The unit test directory may also contain supporting
  `.uc` and `.ec` files, as well as subdirectories, all of which
  `dsl-test` ignores.

* `README` files in the directory hierarchy are ignored by
  `dsl-test`. These files begin with six characters of `README`, in
  any case (even a mixture of lower- and uppercase). Occurrences of
  `log` are also ignored.

* Levels of the directory hierarchy above the unit testing directories
  may only contain `log`, `README` files, and subdirectories. A
  directory containing other files will be ignored (and flagged as an
  error).

Unit Test Directories
--------------------------------------------------------------------

A unit test directory contains a file `TEST`, along with supporting
`.uc` and `.ec` files, and optional subdirectories. `TEST` contains:

* an informal description of the test;

* the arguments that should be supplied to the `ucdsl` executable when
the test is run;

* the expected outcome of running `ucdsl` with those arguments.

Every `TEST` file has three fields: `description`, `args` and
`outcome`, which may come in any order.

Spaces and tabs may be freely inserted in `TEST` files. Newline
characters may be freely inserted as well, with a few exceptions
detailed below.  Comments may be freely inserted (with a few
exceptions, detailed below), and are equivalent to spaces (' ').
'(\*' marks the beginning of a comment, and '\*)' marks the comment's
end.  Nested comments are allowed.

### Description

As the name suggests, description should contain an information
explanation of the purpose of the test.  This will be output and
logged by `dsl-test` in verbose mode only.  The syntax of the
description field is as follows:

```
description
The description of the test goes here, the symbols '(*', '*)' have no
special significance, here.  The description field ends with a line
consisting of only '.'  ('.\n').
.
```

The text of the description field begins *after* the newline
terminating the line containing `description` (possibly surrounded by
spaces or tabs) and runs up to and including the newline that precedes
the terminating '.' (the text does not include that '.').

### Args

The args field gives the arguments that will be supplied to `ucdsl`
when it is invoked. Its syntax is

```
args : <args>
```

where <args> consists of a sequence of words (nonempty sequences of
non-whitespace characters), separated by spaces or tabs. The args
field is terminated with a newline character.

E.g.,

```
args : -I foo goo.uc
```

says to run the command


```
ucdsl -I foo goo.ec
```

(which tells `ucdsl` to include the subdirectory `foo` on the
search path for `.uc` and `.ec` files).

### Outcome

The outcome field describes the expected outcome of running
the test. Its syntax is

```
outcome : <status>
...error...
or... warning...
messages...
.
```

where <status> is `success` (meaning `ucdsl` is expected to exit with
status 0) or `failure` (meaning `ucdsl` is expected to exit with a
nonzero status).

As with the description field, what comes after the
newline following <status> up to the newline preceding the line
consisting of only '.' is the text of the field. It should exactly
match (including occurrences of whitespace characters) the error and
warning messages output by `ucdsl`.

Here is an example outcome field:

```
outcome: failure
[error: testDuplicateMessageId.uc: from line 3 columns 5 to 6]

duplicate message name: m
.
```

A test *passes* if and only if the exit status of `ucdsl` matches
the status of the outcome field *and* the messages issued by
`ucdsl` match the text of the outcome field.


Building the Testing Tool
--------------------------------------------------------------------

To build `dsl-test` using the supplied `Makefile`, simply issue
the command:

```
make
```

You may want to add `/pathto/dsl-test` to your shell's search path.

Running the Testing Tool
--------------------------------------------------------------------

Before running `dsl-test`, you should ensure that `ucdsl` is on your
shell's search path.

The expected arguments to `dsl-test` are indicated by the following
usage message:

```
Usage: dsl-test [verbosity option] dir
       dsl-test -debug file
  -verbose Verbosity option: enables verbose mode
  -quiet Verbosity option: enables quiet mode
  -debug Prints debug information of a TEST file
  -help  Display this list of options
  --help  Display this list of options
```

To run `dsl-test` on <dir-name>, one executes one of the following
commands, depending on the desired degree of verbosity:

```
dsl-test <dir-name>
dsl-test -quiet <dir-name>
dsl-test -verbose <dir-name>
```

The `-quiet` option generates the log, `log`, in the current
directory, but is otherwise silent. The `-verbose` option outputs the
test descriptions both on the standard output and in the log. The exit
status of `dsl-test` tells you whether all tests passed and no other
error were encountered (an exit status of 0 means yes, and a non-zero
exit status means no).

### Conflict files

When a unit test fails, a `CONFLICT` file is created in the test's
directory. Consult the `CONFLICT` file to see what the problem was.
When `ucdsl` issues messages that didn't match the text of the
test's outcome field, those messages are listed in the `CONFLICT`
file.

Resolving the conflict may involve updating the `TEST` file or
supporting `.uc` and `.ec` files, and/or changing `ucdsl` to fix a
bug. Once the conflict has been resolved, you must remove the
`CONFLICT` file (but see `dsl-test-suite`, below). When `dsl-test`
encounters a unit test directory with a `CONFLICT` file, it issues an
error message but otherwise ignores the unit test.

### To debug the syntax of a `TEST` file, you may use the `-debug`
option:

```
dsl-test -debug TEST
```

(replace `TEST` by another filename, as needed).

Examples
--------------------------------------------------------------------

The subdirectory `sample_tests' contains a few tests. To run these
tests simply use one of

```
dsl-test sample_tests
dsl-test -quiet sample_tests
dsl-test -verbose sample_tests
```

In all the cases, a log file with name 'log' is created in the current
working directory.

The subdirectory `testing_tests` contains unit tests for `dsl-test`
itself.

Unit Test Suite
--------------------------------------------------------------------

The unit test suite for `ucdsl` is in the subdirectory [`tests`](tests).
To run `dsl-test` on the test suite, run one of

```
./dsl-test-suite
./dsl-test-suite -quiet
./dsl-test-suite -verbose
```

depending upon what verbosity level you want `dsl-test` to employ.
`dsl-test-suite` removes all `log`, `.coverage` and `CONFLICT` files
before running `dsl-test`. When `dsl-test-suite` finishes, if `ucdsl`
was built with code coverage instrumentation, you can find the code
coverage report in the subdirectory `_coverage`; open `index.html`
with your web browser.

To remove all the `log`, `CONFLICT` and `.coverage` (generated
when `ucdsl` was built with code coverage instrumentation) files,
run the command

```
./dsl-test-suite-cleanup
```

Feedback
--------------------------------------------------------------------

Please contact Alley Stoughton (stough@bu.edu) or Gollamudi Tarakaram
(gtr@brandeis.edu) with any feedback, e.g., with feature requests or
to report bugs.
