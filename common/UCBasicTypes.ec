(* UCBasicTypes.ec *)

(* Defines encoding and partial decoding pairs (EPDPs), the type
   univ plus a number of EPDPs with target univ, addresses
   and ports *)

require import AllCore List.

(* defines encoding and partial decoding pairs (EPDPs) *)

require export UCEncoding.

(* defines type univ = bool list, plus a number of EPDPs and EPDP
   combinators with target univ *)

require export UCUniv.

(* real protocols and ideal functionalities (collectively,
   "functionalities") have hierarchical addresses

   if a functionality has address alpha, it is also responsible for all
   sub-functionalities with addresses beta >= alpha (in the prefix
   partial ordering of UCListPO)

   adversaries are also modeled as functionalities - but with no
   sub-addresses/sub-functionalties; simulators are functionalities
   parameterized by adversaries

   [] is the root address of the environment *)

type _addr = int list.  (* begins with _, as not exposed to UC DSL *)

op epdp_addr_univ : (_addr, univ) epdp = epdp_list_univ epdp_int_univ.

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

type port = _addr * int.

op epdp_port_univ : (port, univ) epdp =
  epdp_pair_univ epdp_addr_univ epdp_int_univ.

lemma valid_epdp_port_univ : valid_epdp epdp_port_univ.
proof.
rewrite epdp_sub epdp.
qed.

hint simplify [eqtrue] valid_epdp_port_univ.
hint rewrite epdp : valid_epdp_port_univ.
