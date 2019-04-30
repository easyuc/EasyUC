Experiments with Universal Composability in EasyCrypt
====================================================================

This repository contains experiments in formalizing Universally
Composable (UC) Security using the
[EasyCrypt](https://www.easycrypt.info/trac/) proof assistant. This is
joint work between

* Ran Canetti (canetti@bu.edu)
* [Alley Stoughton](http://alleystoughton.us) (stough@bu.edu)
* Mayank Varia (varia@bu.edu)

In our architecture, functionalities (real protocols, or ideal
functionalities) have hierarchical addresses, and we build
abstractions that route messages to their destinations, modeling
the coroutine-style communication of UC.

Secure Message Communication
--------------------------------------------------------------------

In our [first full example](../master/smc), we formalized the proof of
the UC security of secure message communication using a one-time pad
that's agreed using Diffie-Hellman key exchange. Our goal in this
example was to test our EasyCrypt UC architecture, illustrating how
instances of UC's composition operation and theorem may be formalized
in EasyCrypt.
