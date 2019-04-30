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

