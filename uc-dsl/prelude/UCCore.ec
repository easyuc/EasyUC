(* UCCore.ec

   a stripped-down and more abstract version of the real UCCore.ec

   will be automatically ec_required last when processing UC DSL
   files, so port will be in the top-level environment *)

(* defines encoding and partial decoding pairs (EPDPs) *)

require export Encoding.

(* defines type univ = bool list, plus a number of EPDP and EPDP
   combinators with target univ *)

require export Univ.

type port.  (* we don't expose the structure of ports *)

(* axiomatized EPDP for ports - in the real UCCore.ec, this is given a
   concrete defintion, with a lemma rather than an axiom *)

op epdp_port_univ : (port, univ) epdp.  (* port *)

axiom valid_epdp_port_univ : valid_epdp epdp_port_univ.
