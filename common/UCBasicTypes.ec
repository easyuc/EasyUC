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

prover [""].  (* no use of SMT *)

(* standard theories *)

require export AllCore List FSet Distr DBool StdOrder.

(* auxiliary lemmas on lists *)

require import UCListAux.

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

   addresses are used for message routing (see below)

   if a real functionality has address alpha, its parameters (if any)
   will have sub-addresses alpha ++ [1], alpha ++ [2], etc., ordered
   by parameter number; and its subfunctionalities will have
   sub-addresses alpha ++ [n + 1], alpha ++ [n + 2], etc., ordered by
   the lexicographic ordering of the names of the subfunctionalities,
   and where n is the number of functionality parameters

   ideal functionalities, adversaries and simulators have addresses,
   but no (proper) sub-addresses

   [] is the root address of the environment

   a functionality will always have a non-empty address

   the adversary and any simulators will share the same address [0],
   which will be incomparable with the address of any functionality

   the address of the functionality is assigned at the beginning of an
   *experiment*, in which the environment experiments with either a
   real functionality and the adversary, or an ideal functionality and
   a nonempty list of simulators plus the adversary (S1 * S2 * ... *
   Sn * Adv) *)

type addr = int list.

op nosmt [opaque] epdp_addr_univ
     : (addr, univ) epdp = epdp_list_univ epdp_int_univ.

lemma valid_epdp_addr_univ : valid_epdp epdp_addr_univ.
proof.
rewrite /epdp_addr_univ !epdp.
qed.

hint simplify valid_epdp_addr_univ.
hint rewrite epdp : valid_epdp_addr_univ.

op env_root_addr : addr = [].   (* root address of environment *)
op adv : addr           = [0].  (* address of adversary *)

(* ports - pairs of functionality addresses and port indices; messages
   (see type below) have source and destination ports, and they have
   modes (see type below): direct or adversarial

   port indices are used to implement several intra-address naming
   schemes

   a direct message coming to a real functionality with address alpha
   (its source port's address must not be a sub-address of alpha) will
   result in failure (which propagates to the environment - this is
   the uniform response to an error) if the address of its destination
   port is not alpha; otherwise, the port index of the destination
   port says which component of the composite direct interface the
   message is a member of (these port indices are numbered beginning
   at 1, and are assigned to the components of the composite interface
   according to the the lexacographic ordering of their names) -- and
   this will in turn determine which party of the real functionality
   handles the message (the one that serves the given basic direct
   interface)

   an adversarial message coming to a real functionality with address
   alpha (its source port's address should be the address of the
   adversary, and the sorce port's port index identifies the sending
   simulator or the notional part of the adversary) is handled
   analogously, but for adversarial interfaces instead of direct ones
   (assuming the functionality implements a composite adversarial
   interface; otherwise it's an error); but if the address of the
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
   determines which party will receive the message; the source port of
   such a message will look like (alpha ++ [n], i), where alpha ++ [n]
   is the address of the parameter or subfunctionality, and the port
   index i will identify the component of the direct interface
   implemented by the parameter or subfunctionality that the message
   is a member of (using the same numbering as described above)

   when an adversarial message propagates out of a parameter or
   subfuctionality of a real functionality with address alpha, its
   destination address should be that of the adversary, and it will be
   propagated to the the functionality's parent, and so on, until it
   can be passed to the adversary; the port index of the message is
   called an adversarial port index, and says which simulator it
   should be consumed by, with the default being that it goes all the
   way to the adversary (messages flow through simulators until
   they find their home); the source port of such a message will
   have an address that is a sub-address of the address of the
   parameter or subfuctionality

   when a direct message is sent by a party of a real functionality
   with address alpha, only two possibilities are allowed:

     * the address of the destination port is not a sub-address of
       alpha (or []), and the source port must be (alpha, i), where i
       is the port index corresponding to the component of the real
       functionality's composite direct interface that the sending
       party serves

     * the address of the destination port must be the address of
       one of the parameters or subfunctionalities of the real
       functionality, and the port index of the destination port
       must identify the component of the composite direct interface
       implemented by the parameter or subfunctionality that the message
       is a member of; in this case, the source port of the message
       will be the internal port of the sending party

   in the UC DSL, these two kind of messages are sent using different
   syntax; in the first case, the destination port is a value of type
   port, but in the second case parameter/subfunctionality is
   described by name, and the destination port is computed from it by
   the UC DSL implementation

   when an adversarial message is sent by a party of a real
   functionality with address alpha, it must have a destination port
   whose address is that of the adversary, and the port index of the
   destination port will say which notional part of the adversary
   should handle it (it will never be the port index of a simulator);
   in this case, the source port will be (alpha, i), where i is the
   port index corresponding to the component of the real
   functionality's composite adversarial interface that the sending party
   serves (but adversarial messages can also propagate out of
   real functionalities from their parameters or subfunctionalities,
   as described above)

   an ideal functionality with address alpha handles direct messages
   analogouly to how a real functionality would (although without the
   internal working of a real functionality)

   an ideal functionality with address alpha can send adversarial
   messages to/from to its simulator (if it comes from a triple unit)
   or the adversay (if it comes from a singleton unit); when sending a
   message, the source port will be (alpha, 1), and incoming messages
   should have this destination port

   a simulator learns the address of its ideal functionality upon
   reception of the first message from it; after that, it responds to
   adversarial messages intended for the real functionality (or one of
   its parameters or subfunctionalities), responding as would the real
   functionality, spoofing source addresses

   the root port of the environment is ([], 0), and the root port of
   the adversary has port index 0; all simulators allow these ports to
   communicate freely via adversarial messages

   the environment is either experimenting with a real functionality
   and the adversary (the real world), or an ideal functionality and a
   nonempty list of simulators followed by the adversary (S1 * S2 *
   ... * Sn * Adv) (the ideal world); in the latter case, each
   simulator has a distinct adversarial port index, which its ideal
   functionality will use to communicate with it; messages from ideal
   functionalities flow from left to right through the list of
   simulators, looking for their home, or going all the way to the
   adversary (messages can also originate from parties of real
   functionalities, in which case they always go all the way to the
   adversary); messages going from right to left are handled by the
   appropriate simulator (pretending to be a real functionality), or
   go from the first simulator (S1) to the ideal functionality; when a
   simulator responds to its ideal functionality, this message may
   actually be handled by a simulator to its left (which is simulating
   a real functionality one of whose parameters is the ideal
   functionality)

   an environment could trivially tell the real and ideal worlds apart
   if it could send adversarial messages to the simulators - as these
   messages would go to the adversary in the real world; in UCCore.ec,
   we use *input guards* - sets of adversarial port indices - to
   limit the destination ports of adversarial messages generated by
   the environment *)

type port = addr * int.

op nosmt [opaque] epdp_port_univ : (port, univ) epdp =
  epdp_pair_univ (epdp_list_univ epdp_int_univ) epdp_int_univ.

lemma valid_epdp_port_univ : valid_epdp epdp_port_univ.
proof.
rewrite /epdp_port_univ !epdp.
qed.

hint simplify valid_epdp_port_univ.
hint rewrite epdp : valid_epdp_port_univ.

op env_root_port : port = ([], 0).
op adv_root_port : port = (adv, 0).

(* envport takes in the address, self, of a functionality (which
   should be incomparable with the address, adv ([0]), of the
   adversary, and a port pt, and tests whether pt's address is neither
   a sub-address of the functionality or the adversary, and pt is not
   the root port of the environment

   in UC DSL, envport is a keyword, and so cannot be used as an
   ordinary identifier. in DSL specs, it has type port -> bool, but
   during the interpretation process, or in the generated EasyCrypt
   code, the real envport is first supplied the address of the
   functionality in question *)

op envport (self : addr, pt : port) : bool =
  ! self <= pt.`1 /\ ! adv <= pt.`1  /\ pt <> ([], 0).

lemma envport_inc_env_root_addr (func : addr, i : int) :
  i <> 0 => inc func adv => envport func (env_root_addr, i).
proof.
move => ne0_i inc_func_adv.
rewrite /envport /env_root_addr ne0_i /=.
split.
case (func <= []) => [le_func_nil | //].
have : func <= adv by rewrite (le_trans []) // ge_nil.
have // := inc_nle_l func adv _.
  trivial.
case (adv <= []) => [le_adv_nil | //].
have : adv <= func by rewrite (le_trans []) // ge_nil.
have // := inc_nle_r func adv _.
  trivial.
qed.

(* lemmas to help the UC DSL interpreter *)

lemma extend_addr_by_sing (xs ys : addr, i : int) :
  (xs ++ ys) ++ [i] = xs ++ (ys ++ [i]).
proof.
by rewrite catA.
qed.

hint rewrite ucdsl_interpreter_hints : extend_addr_by_sing.

lemma envport_ext_func (func xs ys : addr, i : int) :
  inc func adv => ! xs <= ys =>
  envport (func ++ xs) (func ++ ys, i).
proof.
rewrite /envport /= => inc_func_adv -> /=.
split.
by rewrite (inc_le1_not_rl func).
rewrite negb_and.
left.
case (func ++ ys = []) => [func_concat_ys_eq_nil | //].
have // : func ++ ys <> [].
  rewrite nonnil_cat_nonnil_l //.
  have // := inc_non_nil func adv _.
  trivial.
qed.

lemma envport_ext_l_func (func xs : addr, i : int) :
  inc func adv => xs <> [] =>
  envport (func ++ xs) (func, i).
proof.
move => inc_func_adv ne_nil_xs.
by rewrite -{2}(cats0 func) envport_ext_func // le_nil_iff.
qed.

(* lemma inc_nle_l (xs ys : 'a list) : inc xs ys => ! xs <= ys.
   lemma inc_nle_r (xs ys : 'a list) : inc xs ys => ! ys <= xs
   lemma inc_nlt_l (xs ys : 'a list) : inc xs ys => ! xs < ys.
   lemma inc_nlt_r (xs ys : 'a list) : inc xs ys => ! ys < xs *)

lemma inc_ext_nle_r (func adv xs : addr) :
  inc func adv => ! adv <= func ++ xs.
proof.
move => inc_func_adv.
by rewrite inc_nle_r 1:inc_extl.
qed.

lemma inc_ne (func : addr) :
  inc func adv => func <> adv.
proof.
move => inc_func_adv.
case (func = adv) => [->> | //].
by rewrite not_inc_same in inc_func_adv.
qed.

lemma inc_ne_ext_l (func xs : addr) :
  inc func adv => func ++ xs <> adv.
proof.
move => inc_func_adv.
case (func ++ xs = adv) => [adv_eq | //].
move : inc_func_adv.
by rewrite -adv_eq inc_pre_r.
qed.

lemma envport_ne_func (func : addr, pt : port) :
  envport func pt => pt.`1 <> func.
proof.
rewrite /envport.
move => [#] nle_func_pt_1 _ _.
move : nle_func_pt_1.
by case (pt.`1 = func).
qed.

lemma envport_not_gt_func (func : addr, pt : port) :
  envport func pt => ! func < pt.`1.
proof.
rewrite /envport => [#] func_not_le_pt_1 _ _.
move : func_not_le_pt_1.
rewrite implybNN => func_not_lt_pt_1.
by rewrite ltW.
qed.

hint rewrite ucdsl_interpreter_hints :
  envport_ext_func envport_ext_l_func
  envport_ne_func envport_not_gt_func
  inc_ext_nle_r inc_ext_nle_r inc_ne_ext_l
  inc_ne inc_nle_r inc_nle_l inc_nlt_l inc_nlt_r.

(* the rest of the theory is about the messages that are propagated by
   the abstractions of UCCore.ec and the EasyCrypt code generated from
   UC DSL functionalities and simulators *)

(* messages have modes:

     * direct (corresponding to direct interfaces in the DSL) - used
       for communication between the environment and functionalities,
       and between subfunctionalities and parent functionalities

     * adversarial (corresponding to adversarial interfaces in the
       DSL, plus extra messages used in environment <-> adversary
       communication) - communication between functionalties and
       adversaries/simulators, communication between different
       adversaries/simulators, and communication between environments
       and the adversary *)

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
   destination port pt1, a source port pt2, a tag tag, and a universe
   value u (into which we must encode message arguments, using EPDPs
   into univ)

   note that the UC DSL typechecker allows message arguments of
   types for which there is no EPDP into univ; such specifications
   cannot be translated into EasyCrypt code *)

(* the representaton of an OCaml string with ints representing
   characters

   below in examples, we'll write "SMC", "smc_req", etc., even though
   these are not literally values of type string *)

type string = int list.

type tag = [
  | TagNoInter       (* communication not involving messages of an
                        interface *)
  | TagComposite of  (* message is to/from composite interface *)
      string &       (* unit root file name *)
      string         (* message name *)
  | TagBasic     of  (* message is to/from basic interface *)
      string &       (* unit root file name *)
      string         (* message name *)
].

op tag_to_choice3 (tag : tag)
     : (unit, string * string, string * string) choice3 =
  match tag with
  | TagNoInter            => Choice3_1 ()
  | TagComposite root msg => Choice3_2 (root, msg)
  | TagBasic root msg     => Choice3_3 (root, msg)
  end.

op choice3_to_tag
   (ch3 : (unit, string * string, string * string) choice3) =
  match ch3 with
  | Choice3_1 _ => TagNoInter
  | Choice3_2 p => TagComposite p.`1 p.`2
  | Choice3_3 p => TagBasic p.`1 p.`2
  end.

op nosmt [opaque] epdp_tag_choice3
     : (tag, (unit, string * string, string * string) choice3) epdp =
  epdp_bijection tag_to_choice3 choice3_to_tag.

lemma valid_epdp_tag_choice3 : valid_epdp epdp_tag_choice3.
proof.
rewrite /epdp_tag_choice3 !epdp.
by case.
by case; case.
qed.

hint rewrite epdp : valid_epdp_tag_choice3.

op nosmt [opaque] epdp_tag_univ : (tag, univ) epdp =
  epdp_comp
  (epdp_choice3_univ
   epdp_unit_univ 
   (epdp_pair_univ (epdp_list_univ epdp_int_univ)
    (epdp_list_univ epdp_int_univ))
   (epdp_pair_univ (epdp_list_univ epdp_int_univ)
    (epdp_list_univ epdp_int_univ)))
  epdp_tag_choice3.

lemma valid_epdp_tag_univ : valid_epdp epdp_tag_univ.
proof.  
rewrite /epdp_tag_univ !epdp.
qed.

hint rewrite epdp : valid_epdp_tag_univ.
hint simplify valid_epdp_tag_univ.

type msg = mode * port * port * tag * univ.

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

So we assign these port indices to components of the composite direct
interface:

Pt1: 1
Pt2: 2

In the UC DSL interpreter,

pt1@SMC.SMCDir.Pt1.smc_req(pt2, t)$func

abbreviates

pt1@SMC.SMCDir.Pt1.smc_req(pt2, t)@((func, 1))

And in the EasyCrypt translation we would have

(Dir, pt1, (func, 1), TagComposite "SMC" "smc_req",
 <encoding-of> (pt2, t))

Because the root is "SMC", the mode is Dir, and SMCDir is the
composite direct interface of the unit, then implicitly this is the
message's composite direct interface. The sub-interface, Pt1, is
implicit in the destination (because the direction in DirIn) port
index, 1. And the message is "smc_req".

If we take

(Dir, pt1, (func, 2), TagComposite "SMC" "smc_req",
 <encoding-of> (pt2, t))

this would correspond to 

pt1@SMC.SMCDir.Pt2.smc_req(pt2, t)@((func, 1))

which is invalid.

- - -

Consider SMCReal, which has

  subfun Fwd = Forwarding.Forw

as a subfunctionality. If func is the address of (this instance) of
SMCReal, then the address of Fwd will be (func ++ [1]). The internal
ports of parties Pt1 and Pt2 of SMCReal will be (func, 1) and (func,
2), respectively. Suppose Fwd is sending a fw_rsp message to Pt2 with
arguments (pt1, pt2, epdp_text_key.`enc t ^^ k).  In the EasyCrypt
encoding, this will look like

(Dir, (func ++ 1, 1), (func, 2), TagComposite "Forwarding" "fw_rsp",
 <encoding-of> (pt1, pt2, epdp_text_key.`enc t ^^ k))

And in the interpreter syntax, this looks like

((func ++ 1, 1))@
Forwarding.FwDir.D.fw_rsp((func, 1), (pt1, pt2, epdp_text_key.`enc t ^^ k))
@((func, 2))

- - -

An adversarial message to SMCIdeal could look like

(Adv, (adv, adv_pi), (func, 1), TagBasic "SMC" "sim_rsp",
 <encoding-of> ())

In the interpreter syntax, this looks like

((adv, adv_pi))@SMC.SMC2Sim.sim_rsp()@((func, 1))

Here, the destination port index is always 1, because SMCIdeal is
an ideal functionality.

- - -

A message from the root port of the environment to the root port
of the adversary would look like

(Adv, ([], 0), (adv, 0), TagNoInter, u)

for whatever the list of booleans u is.

In the interpreter syntax, this would be abstracted by

(([], 0))@_@((adv, 0))

*)
