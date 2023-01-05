(* UCBasicTypes.ec *)

(* Exports standard theories, encoding and partial decoding pairs
   (EPDPs), the type univ plus a number of EPDPs with target univ;
   defines addresses and ports *)

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

   port indices are used to implement naming schemes for messages
   (see UCCore.ec) with identical destination addresses

   when a direct message comes to a real functionality, the message's
   destination port index is used to determine which party it should
   be sent to

   when an adversarial message comes to a real functionality, the
   message's destination port index is used to determine which party
   it should be sent to (the same port may correspond to different
   parties in direct and adversarial messages)

   adversaries can handle multiple port indices, corresponding to
   different ideal functionalities or real functionality parties

   each simulator handles a single port index, distinct from those
   of all other simulators *)

type port = addr * int.

op epdp_port_univ : (port, univ) epdp =
  epdp_pair_univ (epdp_list_univ epdp_int_univ) epdp_int_univ.

lemma valid_epdp_port_univ : valid_epdp epdp_port_univ.
proof.
rewrite valid_epdp_pair_univ 1:valid_epdp_list_univ valid_epdp_int_univ.
qed.

hint simplify [eqtrue] valid_epdp_port_univ.
hint rewrite epdp : valid_epdp_port_univ.

(* in UC DSL, envport is a keyword, and so cannot be used as an
   ordinary identifier. in DSL specs, it has type port -> bool, but in
   the generated EasyCrypt code it has type addr -> addr -> bool, and
   is applied to the address of the functionality and adversary - in
   addition to the port expression *)

op envport (self adv : addr, pt : port) : bool =
  ! self <= pt.`1 /\ ! adv <= pt.`1  /\ pt <> ([], 0).
