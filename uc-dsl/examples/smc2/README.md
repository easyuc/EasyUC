Two Way Secure Message Communication
=====================================================================

The files in this directory express two way secure message
communication (SMC) out of ordinary SMC and the forwarding ideal
functionality. This is a two party functionality letting the clients
of the two parties securely exchange a pair of messages: first one
from the first to the second, followed by one from the second to the
first.

The supporting EasyCrypt code is in the subdirectory `supporting`.
From the command line or when compiling in Emacs in UC DSL mode, you
will thus need to include the command line option `-I supporting`. But
when running the UC DSL interpreter inside Proof General, `supporting`
is automatically included in the load path because of the
setting for `ucdsl-interpreter-mode` in `.dir-locals.el`.

Read and experiment with the interpretation script
[testing.uci](testing.uci) to learn how to use the UC DSL interpreter.
