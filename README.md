Experiments with Universal Composability in EasyCrypt
====================================================================

This repository contains experiments in formalizing Universally
Composable (UC) Security using the
[EasyCrypt](https://www.easycrypt.info/trac/) proof assistant. This is
joint work between Boston University faculty

* Ran Canetti (canetti@bu.edu)
* Assaf Kfoury (kfoury@bu.edu)
* [Alley Stoughton](http://alleystoughton.us) (stough@bu.edu)
* Mayank Varia (varia@bu.edu)

with the assistance of research students

* Tarakaram Gollamudi (Brandeis University, gtr@brandeis.edu)
* Tomislav Petrovic (tomislav@bu.edu)

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

We have designed and implemented a prototype parser and typechecker
for a [domain specific language (DSL)](../master/uc-dsl) for
expressing functionalities (protocols and ideal functionalities) and
simulators. The DSL will allow crypto theorists to easily write and
understand functionalities and simulators.  The DSL design was driven
by the expression of functionalities and simulators in our EasyCrypt
architecture for UC.  But it allows expression at a much higher level,
avoiding all the message-routing boilerplate.  DSL type-checking will
catch errors like badly formed messages (e.g., ones with bad source
addresses) or simulators that interfere with communication between
environment and adversary. When DSL code is translated into
EasyCrypt's procedural programming language, message-routing
boilerplate will be automatically generated.
