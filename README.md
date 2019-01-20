Experiments with Universal Composability in EasyCrypt
====================================================================

This repository contains experiments in formalizing Ran Canetti's
Universally Composable (UC) Security using the
[EasyCrypt](https://www.easycrypt.info/trac/) proof assistant. This is
joint work between [Alley Stoughton](http://alleystoughton.us)
(stough@bu.edu), Ran Canetti (canetti@bu.edu) and Mayank
Varia (varia@bu.edu).

Initial Experiment
--------------------------------------------------------------------

Our [initial experiment](../master/nesvd-2017) was formalizing and
proving the UC security of Diffie-Hellman key exchange, as reported at
[2017 New England Systems Verification
Day](http://svd.csail.mit.edu/2017/). This was very preliminary work,
but shows how we were using manual action distribution to model the
coroutine-style communication of UC.

Secure Message Transmission
--------------------------------------------------------------------

In our [first full example](../master/smc), we are in the process of
formalizing UC security of secure message transmission using a
one-time pad that's agreed using Diffie-Hellman key exchange. Our goal
in this example is to illustrate how instances of UC's composition
operation and theorem may be formalized in EasyCrypt. As in our
initial experiment, we are using manual message routing to model the
coroutine-style communication of UC.

The case study is almost complete, and is giving us confidence that
our architecture is sound. But it is involving heavy use of manual
symbolic execution, guided by case analysis. Consequently, in order
for this approach to scale-up to realistic protocols, various
improvements will be necessary.

