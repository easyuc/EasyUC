(* UCBasicTypes.ec *)

(* Exports standard theories, encoding and partial decoding pairs
   (EPDPs), the type univ plus a number of EPDPs with target univ;
   defines addresses, ports and messages *)

(* standard theories *)

require export AllCore List FSet Distr DBool.

(* prefix ordering on lists *)

require import UCListPO.  (* only needed to define envport, below;
                             we require export in UCCore.ec *)

(* defines encoding and partial decoding pairs (EPDPs) *)

require export UCEncoding.

(* defines type univ = bool list, plus a number of EPDPs and EPDP
   combinators with target univ *)

require export UCUniv.

(* real protocols and ideal functionalities (collectively,
   "functionalities") have hierarchical addresses

   if a functionality has address alpha, it is also responsible for all
   sub-functionalities with addresses beta >= alpha (in the prefix
   partial ordering)

   adversaries are also modeled as functionalities - but with no
   sub-addresses/sub-functionalties; simulators are functionalities
   parameterized by adversaries

   [] is the root address of the environment *)

type addr = int list.

op epdp_addr_univ : (addr, univ) epdp = epdp_list_univ epdp_int_univ.

lemma valid_epdp_addr_univ : valid_epdp epdp_addr_univ.
proof.
rewrite valid_epdp_list_univ valid_epdp_int_univ.
qed.

hint simplify [eqtrue] valid_epdp_addr_univ.
hint rewrite epdp : valid_epdp_addr_univ.

(* ports - pairs of functionality addresses and port indices

   a functionality's ports are divided between its different parties

   adversaries can handle multiple port indices, and each simulator
   has a single, distinct port index

   ([], 0) is the root port of the environment *)

type port = addr * int.

op epdp_port_univ : (port, univ) epdp =
  epdp_pair_univ epdp_addr_univ epdp_int_univ.

lemma valid_epdp_port_univ : valid_epdp epdp_port_univ.
proof.
rewrite valid_epdp_pair_univ 1:valid_epdp_list_univ valid_epdp_int_univ.
qed.

hint simplify [eqtrue] valid_epdp_port_univ.
hint rewrite epdp : valid_epdp_port_univ.

(* in UC DSL, envport is a keyword, and so cannot be used as an
   ordinary identifier. in DSL specs, it has type port -> bool, but in
   the generated EasyCrypt code it has type _addr -> addr -> bool, and
   is applied to the address of the functionality and adversary - in
   addition to the port expression *)

op envport (self adv : addr, pt : port) : bool =
  ! self <= pt.`1 /\ ! adv <= pt.`1  /\ pt <> ([], 0).

(* messages have modes:

     * direct - supplying functionality inputs, consuming their
         outputs

     * adversarial - communication between functionalties and
         adversaries/simulators, communication between different
         adversaries/simulators, and communication between
         environments and adversaries/simulators *)

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
   destination port pt1, a source port pt2, an integer tag (used to
   ensure certain messages are distinct), and a universe value u *)

type msg = mode * port * port * int * univ.
