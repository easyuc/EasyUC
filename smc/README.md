Secure Message Communication
====================================================================

We formalized the proof of the UC security of secure message
communication (SMC) using a one-time pad that's agreed using
Diffie-Hellman key exchange. Our goal in this example was to test our
EasyCrypt UC architecture, illustrating how instances of UC's
composition operation and theorem may be formalized in EasyCrypt.

The proof is complete, giving us confidence that our EasyCrypt UC
architecture is sound. But there is much work to be done before
the method can scale-up to realistic protocols.

* It involved heavy use of manual symbolic program evaluation, guided
  by case analysis. There is a pressing need for better EasyCrypt
  support for symbolic evaluation.

* We need to generalize from proving a single instance of the UC
  composition theorem to either proving this theorem in EasyCrypt's
  metatheory (e.g., in Coq), or being able to automatically generate
  the EasyCrypt proofs of needed instances of the theorem (so support
  for composition could be added without extending EasyCrypt's trusted
  computing base).

* Writing functionalities, simulators, etc., directly in EasyCrypt is
  somewhat tedious and error prone. We plan to develop a domain specific
  language for expressing functionalities, simulators, etc., with the
  short term goal of automatically translating DSL program to actual
  EasyCrypt code.

Auxiliary Theories
--------------------------------------------------------------------

* [`ListAux.ec` - auxiliary lemmas on lists](ListAux.ec)
* [`FSetAux.ec` - auxiliary lemmas on finite sets](FSetAux.ec)

Supplementary Theories
--------------------------------------------------------------------

* [`ListPO.ec` - prefix ordering on lists](ListPO.ec)
* [`RedundantHashing.eca` - redundant hashing (eager/lazy random
   sampling)](RedundantHashing.eca)

UC Architecture
--------------------------------------------------------------------
* [`UCCore.eca` - core definitions of UC architecture](UCCore.eca)

Proof of UC Security of SMC
--------------------------------------------------------------------

* [`DDH.ec` - Decisional Diffie-Hellman assumption](DDH.ec)
* [`UCCoreDiffieHellman.ec` - specialization of UC core definitions
   to DDH](UCCoreDiffieHellman.ec)
* [`Forward.ec` - forwarding functionality](Forward.ec)
* [`KeyExchange.ec` - Diffie-Hellman key exchange](KeyExchange.ec)
* [`SMC.ec` - secure message communication](SMC.ec)

Scripts
--------------------------------------------------------------------

* [`check-all-scripts` - shell script for running EasyCrypt on
   all EasyCrypt scripts](check-all-scripts)
