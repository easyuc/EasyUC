(* UCBasicTypes.ec

   a stripped-down, more abstract version of the real UCBasicTypes.ec

   will be automatically ec_required last when processing UC DSL
   files, so port will be in the top-level environment *)

(* standard theories *)

require export AllCore List FSet Distr DBool.

(* defines encoding and partial decoding pairs (EPDPs) *)

require export UCEncoding.

(* defines type univ = bool list, plus a number of EPDP and EPDP
   combinators with target univ *)

require export UCUniv.

type port.  (* we don't expose the structure of ports *)
type addr.
(* axiomatized EPDP for ports - in the real UCBasicTypes.ec, this is
   given a concrete definition, with a lemma rather than an axiom *)

op epdp_port_univ : (port, univ) epdp.  (* port *)

axiom valid_epdp_port_univ : valid_epdp epdp_port_univ.

hint simplify [eqtrue] valid_epdp_port_univ.
hint rewrite epdp : valid_epdp_port_univ.
