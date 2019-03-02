Experiments with Universal Composability in EasyCrypt
====================================================================

This repository contains experiments in formalizing Ran Canetti's
Universally Composable (UC) Security using the
[EasyCrypt](https://www.easycrypt.info/trac/) proof assistant. This is
joint work between [Alley Stoughton](http://alleystoughton.us)
(stough@bu.edu), Ran Canetti (canetti@bu.edu) and Mayank
Varia (varia@bu.edu).

Secure Message Communication
--------------------------------------------------------------------

In our [first full example](../master/smc), we formalized the proof of
the UC security of secure message communication using a one-time pad
that's agreed using Diffie-Hellman key exchange. Our goal in this
example was to illustrate how instances of UC's composition operation
and theorem may be formalized in EasyCrypt. We used manual message
routing to model the coroutine-style communication of UC.

The proof is complete (but still being cleaned up), giving us
confidence that our EasyCrypt UC architecture is sound. But it
involved heavy use of manual symbolic execution, guided by case
analysis. Consequently, in order for this approach to scale-up to
realistic protocols, various improvements will be necessary.

