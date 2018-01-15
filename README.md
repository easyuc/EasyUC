Experiments with Universal Composability in EasyCrypt
====================================================================

This repository contains experiments in formalizing Ran Canetti's
Universal Composability (UC) using the
[EasyCrypt](https://www.easycrypt.info/trac/) proof assistant. This is
joint work between [Alley Stoughton](http://alleystoughton.us)
(alley.stoughton@icloud.com), Ran Canetti (canetti@bu.edu) and Mayank
Varia (varia@bu.edu).

Initial Experiment
--------------------------------------------------------------------

Our [first experiment](../master/nesvd-2017) was formalizing and
proving the UC security of Diffie-Hellman key exchange, as reported at
[2017 New England Systems Verification
Day](http://svd.csail.mit.edu/2017/). This is very preliminary work,
but shows how we are using manual action distribution to model the
coroutine-style communication of UC.
