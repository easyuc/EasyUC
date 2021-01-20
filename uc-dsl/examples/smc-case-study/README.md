Expression of SMC (Secure Message Communication) Case Study in UC DSL
=====================================================================

The files in this directory express the secure message communication
case study of our paper [EasyUC: Using EasyCrypt to Mechanize Proofs
of Universally Composable Security](https://eprint.iacr.org/2019/582)
using the UC DSL:

* [`KeysExponentsAndPlaintexts.ec` - supporting EasyCrypt definitions
   of keys, exponents and plaintexts](KeysExponentsAndPlaintexts.ec)
* [`Forwarding.uc` - Forwarding ideal functionality](Forwarding.uc)
* [`KeyExchange.uc` - Real and ideal functionalities plus a simulator
   for Diffie-Hellman key-exchange](KeyExchange.uc)
* [`SMC.uc` - Real and ideal functionalities plus a simulator for
   secure message communication](SMC.uc)
   
This development is split into *units*, and can thus be checked using the
`-units` command line option to `ucdsl`. A *unit* either

* has one ideal functionality, no real functionalities and no
  simulators, and has no extraneous interfaces; or

* has one real functionality, one ideal functionality, one simulator,
  and no extraneous interfaces, where the real and ideal
  functionalities share the same (composite) direct interface, and the
  simulator uses the ideal functionality's adversarial (basic)
  interface (the above implies that the simulator simulates the real
  functionality).

There are extensive comments in the above files, which provide a
good example-based introduction to the meaning and usage of the UC DSL.
