(* UCBasicTypes.ec *)

(* Exports standard theories, encoding and partial decoding pairs
   (EPDPs), the type univ plus a number of EPDPs with target univ, and
   prefix ordering on lists.

   Defines addresses, ports and messages.

   When the UC DSL typechecker processes a .uc file, it
   requires/imports this theory last, after all other ec_requires, so
   that UC DSL specifications may use its types and operators without
   qualification. There is no need to directly use the structure of
   ports in UC DSL specifications, although this is not
   prohibited. (Thus there is no need to use the type addr of
   addresses at all.) On the other hand, using the type msg of
   messages would be pointless, but harmless.

   The UC DSL interpreter works with ports and addresses, but the
   messages that it propagates are symbolic, and have nothing to do
   with values of type msg.

   When a UC DSL unit is translated by the UC DSL translator into an
   EasyCrypt theory, that theory will require/import this theory last,
   after the other ec_requires of the unit. *)

(* standard theories *)

require export AllCore List FSet Distr DBool.

(* prefix ordering on lists *)

require export UCListPO.  (* uses for addresses *)

(* defines encoding and partial decoding pairs (EPDPs) *)

require export UCEncoding.

(* defines type univ = bool list, plus a number of EPDPs and EPDP
   combinators with target univ *)

require export UCUniv.

(* real functionalities (protocols) and ideal functionalities
   (collectively, "functionalities") have addresses, which are lists
   of integers

   if a real functionality has address alpha, its parameters will have
   sub-addresses alpha ++ [1], alpha ++ [2], etc., ordered by
   parameter number; and its subfunctionalities will have
   sub-addresses alpha ++ [n + 1], alpha ++ [n + 2], etc., ordered by
   the lexicographic ordering of the names of the subfunctionalities,
   and were n is the number of functionality parameters

   ideal functionalities, adversaries and simulators have addresses,
   but no (proper) sub-addresses

   [] is the root address of the environment

   a functionality will always have a non-empty address

   the adversary and any simulators will share the same non-empty address,
   which will be incomparable with the address of any functionality

   these addresses are assigned at the beginning of an *experiment*,
   in which the environment experiments with a functionality and
   adversary/simulators *)

type addr = int list.

op epdp_addr_univ : (addr, univ) epdp = epdp_list_univ epdp_int_univ.

lemma valid_epdp_addr_univ : valid_epdp epdp_addr_univ.
proof.
rewrite valid_epdp_list_univ valid_epdp_int_univ.
qed.

hint simplify [eqtrue] valid_epdp_addr_univ.
hint rewrite epdp : valid_epdp_addr_univ.

(* ports - pairs of functionality addresses and port indices; messages
   have source and destination ports, and they have modes: direct
   or adversarial

   port indices are used to implement several intra-address naming
   schemes

   a direct message coming to a real functionality with address alpha
   (its source port's address must not be a sub-address of alpha) will
   result in failure (which propagates to the environment - this is
   the uniform response to an error) if the address of its destination
   port is not alpha; otherwise, the port index of the destination
   port says which component of the composite direct interface (a
   basic direct interface) the message is a member of (these port
   indices are numbered beginning at 1, and are assigned to the
   components of the composite interface according to the the
   lexacographic ordering of their names) -- and this will in turn
   determine which party of the real functionality handles the message

   an adversarial message coming to a real functionality with address
   alpha (its source port's address should be the address of the
   adversary, and the sorce port's port index identifies the sending
   simulator or the notional part of the adversary) is handled
   analogously, but for adversarial interfaces instead of direct ones,
   if the functionality implements a composite adversarial interface;
   otherwise this results in failure; but if the address of the
   message's destination port is a proper sub-address of alpha, the
   message is routed to the appropriate parameter or subfunctionality
   (and results in failure if the sub-address is bad); thus the same
   port index will have a different meaning for a direct versus
   adversarial message

   when a direct message propagages out of a parameter or
   subfuctionality of a real functionality with address alpha, its
   destination port must be one of the internal ports of that real
   functionality, otherwise failure results; the internal ports have
   the form (alpha, 1), (alpha, 2), etc., numbered according to the
   lexicographic ordering of the names of the parties -- this
   determines which party will receive the message

   when an adversarial message propagates out of a parameter or
   subfuctionality of a real functionality with address alpha, its
   destination address should be that of the adversary, and it will be
   propagated to the the functionality's parent, and so on, until it
   can be passed to the adversary; the port index of the message is
   called an adversarial port index, and says which simulator it
   should be consumed by, with the default being that it goes all the
   way to the adversary; messages can flow through simulators until
   they find their home

   when a direct message is sent by a party of a real functionality
   with address alpha, only two possibilities are allowed:

     * the address of the destination port must not be a sub-address of
       alpha or [], and the source port must be (alpha, i), where
       i is the port index corresponding to the component of the
       real functionality's composite direct interface that the
       sending party serves

     * the address of the destination port must be the address of
       one of the parameters or subfunctionalities of the real
       functionality, and the port index of the destination port
       must identify the component of the composite direct interface
       implemented by the parameter or subfunctionality that the message
       is a member of; in this case, the source port of the message
       will be the internal port of the sending party

   in the UC DSL, two two kind of messages are send using different
   syntax; in the first case, the destination port is a value of type
   port, but in the second case parameter/subfunctionality is
   described by name, and the destination port computed from it by the
   UC DSL implementation

   when an adversarial message is sent by a party of a real
   functionality with address alpha, it must have a destination port
   whose address is that of the adversary, and the port index of the
   destination port will say which notional part of the adversary
   should handle it (it will never be the port index of a simulator);
   in this case, the source port will be (alpha, i), where i is the
   port index corresponding to the component of the real
   functionality's composite adversarial interface that the sending party
   serves

   an ideal functionality with address alpha handles direct messages
   analogouly to how a real functionality would (although without the
   internal working of a real functionality)

   an ideal functionality with address alpha can send adversarial
   messages to/from to its simulator (if it comes from a triple unit)
   or the adversay (if it comes from a singleton unit); when sending
   message, the source port index will be 1; and incoming messages
   should have 

   a simulator learns the address of its ideal functionality upon
   reception of the first message from it; after that, it responds to
   messages intended for the real functionality (or one of its
   parameters or subfunctionalities), responding as would the real
   functionality, spoofing source addresses

   the root port of the environment is ([], 0), and the root port of
   the adversary has port index 0; all simulators allow these ports to
   communicate freely via adversarial messages *)

type port = addr * int.

op epdp_port_univ : (port, univ) epdp =
  epdp_pair_univ (epdp_list_univ epdp_int_univ) epdp_int_univ.

lemma valid_epdp_port_univ : valid_epdp epdp_port_univ.
proof.
rewrite valid_epdp_pair_univ 1:valid_epdp_list_univ valid_epdp_int_univ.
qed.

hint simplify [eqtrue] valid_epdp_port_univ.
hint rewrite epdp : valid_epdp_port_univ.

(* envport takes in the address, self, of a functionality, the
   address, adv, of the adversary (self and adv should be nonempty and
   incomparable), and a port pt, and tests whether pt's address is
   neither a sub-address of the functionality or the adversary, and pt
   is not the root port of the environment

   in UC DSL, envport is a keyword, and so cannot be used as an
   ordinary identifier. in DSL specs, it has type port -> bool, but
   during the interpretation process, or in the generated EasyCrypt
   code, the real envport is first supplied the addresses of the
   functionality in question and the adversary *)

op envport (self adv : addr, pt : port) : bool =
  ! self <= pt.`1 /\ ! adv <= pt.`1  /\ pt <> ([], 0).

(* the rest of the theory is about the messages that are propagated by
   the abstractions of UCCore.ec and the EasyCrypt code generated from
   UC DSL functionalities and simulators *)

(* messages have modes:

     * direct (corresponding to direct interfaces in the DSL) - used
       for communication between the environment and functionalities,
       and between subfunctionalities and parent functionalities

     * adversarial (corresponding to adversarial interfaces in the
       DSL) - communication between functionalties and
       adversaries/simulators, communication between different
       adversaries/simulators, and communication between environments
       and adversaries/simulators *)

type mode = [
  | Dir  (* direct *)
  | Adv  (* adversarial *)
].

lemma not_dir (mod : mode) :
  mod <> Dir <=> mod = Adv.
proof. by case mod. qed.

lemma not_adv (mod : mode) :
  mod <> Adv <=> mod = Dir.
proof. by case mod. qed.

(* a message has the form (mod, pt1, pt2, tag, u), for a mode mod, a
   destination port pt1, a source port pt2, an integer tag, and a
   universe value u (into which we must encode message arguments,
   using EPDPs into univ)

   we assign the tags so that all the messages of all components of a
   composite interface have distinct tags; thus the tags can be
   thought of as message paths, and used to reject a messages whose
   destination port index is inconsistent with the tag and the
   composite interface implemented by the real functionality at
   the destination port's address - an example is below

   note that the UC DSL typechecker allows message arguments of
   types for which there is no EPDP into univ; such specifications
   cannot be translated into EasyCrypt code *)

type msg = mode * port * port * int * univ.

(* consider this example from uc-dsl/examples/smc-case-study/SMC.uc

direct SMCPt1 {  (* Party 1 *)
  in pt1@smc_req(pt2 : port, t : text)
}

direct SMCPt2 {  (* Party 2 *)
  out smc_rsp(pt1 : port, t : text)@pt2
}

direct SMCDir {
  Pt1 : SMCPt1  (* Party 1 *)
  Pt2 : SMCPt2  (* Party 2 *)
}

So we assign these port indices:

Pt1: 1
Pt2: 2

And we assign tags:

SMCDir.Pt1.smc_req: 1
SMCDir.Pt2.smc_rsp: 2

In the UC DSL interpreter,

pt1@SMCDir.Pt1.smc_req(pt2, t)$func

abbreviates

pt1@SMCDir.Pt1.smc_req(pt2, t)@(func, 1)

Suppose, func is the address of SMCReal (which implements SMCDir) and
we have the message

pt1@SMCDir.Pt1.smc_req(pt2, t)@(func, 2)

In the interpreter, the port index of Pt1 is inconsistent with the
destination port index 2, and so this message would result in failure.

In raw EC, we would have

(Dir, pt1, (func, 2), 1, <encoding-of> (pt2, t))

Because the tag is 1, this allows the generated EasyCrypt code
to reject this message, because SMCReal implements SMCDir, and
the message with tag 1 comes from the component with port index 1 *)
