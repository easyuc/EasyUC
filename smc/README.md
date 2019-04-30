Secure Message Communication
====================================================================

We formalized the proof of the UC security of secure message
communication (SMC) using a one-time pad that's agreed using
Diffie-Hellman key exchange. Our goal in this example was to test our
EasyCrypt UC architecture, illustrating how instances of UC's
composition operation and theorem may be formalized in EasyCrypt.

The proof is complete, giving us confidence that our EasyCrypt UC
architecture is sound. But it involved heavy use of manual symbolic
execution, guided by case analysis. Consequently, in order for this
approach to scale-up to realistic protocols, various improvements will
be necessary.



Auxiliary Theories
--------------------------------------------------------------------

* [`ListAux.ec` - auxiliary lemmas on lists](ListAux.ec)
* [`FSetAux.ec` - auxiliary lemmas on finite sets](FSetAux.ec)

Supplementary Theories
--------------------------------------------------------------------

* [`ListPO.ec` - prefix ordering on lists](ListPO.ec)
* [`RedundantHashing.eca` - redundant hashing (eager/lazy random
   sampling](RedundantHashing.eca)

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
   all scripts](check-all-scripts)
