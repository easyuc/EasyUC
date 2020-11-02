(* UCCore.ec

   a stripped-down and more abstract version of the real UCCore.ec

   will be automatically ec_required last when processing UC DSL
   files *)

(* defines encoding and partial decoding pairs (EPDPs) *)

require export Encoding.

(* defines type univ = bool list, plus a number of EPDP and EPDP
   combinators with target univ *)

require export Univ.

type port.  (* we don't expose the structure of ports *)
