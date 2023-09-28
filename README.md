Experiments with Universal Composability in EasyCrypt
====================================================================

This repository contains experiments in formalizing Universally
Composable (UC) Security using the
[EasyCrypt](https://www.easycrypt.info/trac/) proof assistant. This is
joint work between researchers

* Ran Canetti (canetti@bu.edu)
* Tomislav Petrovic (tomislav@bu.edu)
* [Alley Stoughton](http://alleystoughton.us) (stough@bu.edu)
* Mayank Varia (varia@bu.edu)

with the assistance of

* Megan Chen (megchen@bu.edu)
* Gollamudi Tarakaram (Brandeis University, gtr@brandeis.edu)

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

This work is described in the extended version of the CSF 2019 paper,
[EasyUC: Using EasyCrypt to Mechanize Proofs of Universally Composable
Security](https://eprint.iacr.org/2019/582).

UC Domain Specific Language
--------------------------------------------------------------------

We have designed and implemented a parser, typechecker and interpreter
for a [domain specific language (DSL)](../master/uc-dsl) for
expressing functionalities (protocols and ideal functionalities) and
simulators. The DSL will allow crypto theorists to easily write and
understand functionalities and simulators.  Its design was driven by
the expression of functionalities and simulators in our EasyCrypt
architecture for UC.  But it allows expression at a much higher level,
avoiding all the message-routing boilerplate.  DSL type-checking
prevents errors like badly formed messages (e.g., ones with bad source
addresses), simulators that interfere with communication between
environment and adversary, or violations of the coroutine model
(trying to send two message in sequence, without control having first
returned).  We are working toward a translator from the DSL into
EasyCrypt, where the sequence of games security proofs will still be
mechanized.
