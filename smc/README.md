Secure Message Communication
====================================================================

We formalized the proof of the UC security of secure message
communication using a one-time pad that's agreed using Diffie-Hellman
key exchange. Our goal in this example was to test our EasyCrypt UC
architecture, illustrating how instances of UC's composition operation
and theorem may be formalized in EasyCrypt.

The proof is complete, giving us confidence that our EasyCrypt UC
architecture is sound. But it involved heavy use of manual symbolic
execution, guided by case analysis. Consequently, in order for this
approach to scale-up to realistic protocols, various improvements will
be necessary.



Auxiliary Theories
--------------------------------------------------------------------

* [`ListAux.ec` - ](ListAux.ec)
* [`FSetAux.ec` - ](FSetAux.ec)

Supplementary Theories
--------------------------------------------------------------------

* [`ListPO.ec` - ](ListPO.ec)
* [`UCCore.eca` - ](UCCore.eca)
* [`RedundantHashing.eca` - ](RedundantHashing.eca)

* [`DDH.ec` - ](DDH.ec)
* [`UCCoreDiffieHellman.ec` - ](UCCoreDiffieHellman.ec)
* [`Forward.ec` - ](Forward.ec)
* [`KeyExchange.ec` - ](KeyExchange.ec)
* [`SMC.ec` - ](SMC.ec)

Scripts
--------------------------------------------------------------------

* [`check-all-scripts` - shell script for running EasyCrypt on
   all scripts](check-all-scripts)
