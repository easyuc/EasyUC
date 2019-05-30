Secure Message Communication
====================================================================

We formalized the proof of the UC security of secure message
communication (SMC) using a one-time pad that's agreed using
Diffie-Hellman key exchange.

* We first proved the security of Diffie-Hellman key exchange,
  reducing it to the Decisional Diffie-Hellman assumption for a
  constructed DDH adversary. This proof makes uses of EasyCrypt's
  eager/lazy random sampling facilities, because, in the real and
  ideal functionalities, the DDH exponents are chosen in the middle of
  the functionalities' execution.

* We then use the security of Diffie-Hellman key exchange to prove the
  security of secure message communication using a one-time pad agreed
  by the parties using D-H key exchange. This involves proving an
  instance of the UC composition theorem, as well as making use of
  the transitivity of UC security.

Our goal in this case study was to test our EasyCrypt UC architecture,
illustrating how instances of UC's composition operation and theorem
may be formalized in EasyCrypt.

The proof is complete, giving us confidence that our EasyCrypt UC
architecture is sound. But there is much work to be done before
the method can scale-up to realistic protocols. Most importantly:

* Proving relationships between structurally dissimilar programs
  involved heavy use of manual symbolic program evaluation, guided by
  case analysis - essentially running programs using repeated
  applications of the EasyCrypt tactics `sp` (for pushing assignments
  into the precondition), `inline` (for inlining procedures) and
  `rcondt`/`rcondf` (for reducing conditionals/while loops for which
  the truth/falsity of their boolean expressions can be established).  There is
  a pressing need for better EasyCrypt support for symbolic
  evaluation.

* We need to generalize from proving single instances of the UC
  composition theorem to either proving the theorem in EasyCrypt's
  metatheory (e.g., in Coq), or being able to automatically generate
  the EasyCrypt proofs of needed instances of the theorem (so support
  for composition could be provided without extending EasyCrypt's trusted
  computing base).

* Writing functionalities, simulators, etc., directly in EasyCrypt is
  somewhat tedious and error prone. We plan to develop a domain
  specific language for expressing functionalities, etc., with the
  short term goal of automatically translating DSL programs to actual
  EasyCrypt code.

This work is described in the extended version of the CSF 2019 paper,
[EasyUC: Using EasyCrypt to Mechanize Proofs of Universally Composable
Security](https://eprint.iacr.org/2019/582).

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
