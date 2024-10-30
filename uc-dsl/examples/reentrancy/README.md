Reentrant Two Party Functionality for Joint Computation
=====================================================================

The files in this directory define a reentrant two party
functionality for jointly carrying out a computation involving inputs
to the two parties. Unlike in the SMC2 example, the parties' clients
only learn each other's identities (ports) when they receive their
outputs to the computation.

The file [`FwdSched.uc`](FwdSched.uc) defines a version of forwarding
of universe values in which the adversary learns nothing of the values
being forwarded or the ports involved, but is purely in change of
scheduling. The file [`Comp.ec`](Comp.ec) contains EasyCrypt
definitions on which the main file [`Comp.uc`](Comp.uc) relies.
The parties of the real functionality have adversarial interfaces,
and can suspend their operation, giving control to the adversary,
which may later resume them.

The flow of control in this example is fundamentally reentrant: the
adversary gives control to the environment which reenters the real
functionality by giving an input to the party that doesn't yet
have its input. There is no other way for both parties to get their
inputs.

The ideal functionality is much simpler than the real functionality.
It only tells its simulator when inputs arrive from its clients, but
not what those inputs are, or what the client ports are. Once both
inputs have arrived, it lets the simulator tell it the order in which
the outputs to the computation should be sent to the party's clients.
The simulator can only make these decisions based on its interaction
with the adversary, which thinks it's making scheduling decisions in
the real world.

The simulator is rather complex, because of the reentrancy, and has to
keep track of abstract versions of the states of the two parties and
the two forwarders.

Read and experiment with the interpretation script
[Comp-testing.uci](Comp-testing.uci) to see how scheduling choices
made by the adversary affect execution in the real and ideal
worlds. In particular, note how the script transfers control back and
forth between the environment and adversary.

There is also a simple one party functionality [Main.uc](Main.uc) that
uses `Comp`, supplying concrete inputs and checking that it gets the
expected responses.  See [Main-testing.uci](Main-testing.uci)
and [Main-testing-idealish.uci](Main-testing-idealish.uci)
for experiments involving it (the former using the real functionality
for `Comp`, and the latter using the ideal functionality).
