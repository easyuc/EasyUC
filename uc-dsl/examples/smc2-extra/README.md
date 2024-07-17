Two Way Secure Message Communication with Extra Features
=====================================================================

The files in this directory augment the two way secure message
communication (SMC2) example with two features that are
somewhat artificial, but are useful for understanding how the
UC DSL works.

(First understand how SMC2 works before studying this example.)

The real functionality has an extra party, Pt3, plus two
instances Fwd3 and Fwd4 of a private forwarding functionality
(see supporting/PrivateForwarding.uc).

The private forwarding ideal functionality (a singleton unit) has no
adversarial interface: it models how some pairs of functionality
parties may be able to communication with the adversary not knowing
(not even getting pinged).

At the beginning of the execution of the real functionality, Pt1 uses
Fwd3 to send the SMC2 client ports pt1 and pt2 (as encoded) to Pt3
(the adversary does not mediate this). Pt3 is corrupted, though, and
sends this universe value to the adversary. Once the adversary tells
it to continue, it uses Fwd4 to return control to Pt1 (again, not
mediated by the adversary).

After that, the behavior of the real functionality continues just as
in SMC2. The ideal functionality for this version is unchanged, but
the simulator is modified to match the behavior of the real
functionality.

See SMC2.uc, supporting/PrivateForwarding.uc and testing.uci for
the details.
