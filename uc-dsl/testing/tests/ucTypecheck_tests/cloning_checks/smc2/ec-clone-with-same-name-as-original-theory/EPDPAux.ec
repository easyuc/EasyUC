(* EPDPAux.ec *)

(************************* Auxiliary EPDP Definitions *************************)

prover [""].  (* no use of SMT provers *)

require import AllCore.
require import UCBasicTypes.

(* EPDP between port * port and univ *)

op [opaque smt_opaque] epdp_port_port_univ : (port * port, univ) epdp =
  epdp_pair_univ epdp_port_univ epdp_port_univ.

lemma valid_epdp_port_port_univ :
  valid_epdp epdp_port_port_univ.
proof.
by rewrite /epdp_port_port_univ.
qed.

hint simplify valid_epdp_port_port_univ.
