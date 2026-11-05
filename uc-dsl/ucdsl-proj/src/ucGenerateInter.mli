(* UcGenerateInter module interface *)

open EcScope
open UcTypedSpec

(* if it : inter_tyd corresponds to the interface named by root
   and id, then

     gen_int scope root id of_comp_if_basic in_tyd

   generates the EasyCrypt code for root/id/in_tyd, where the boolean
   of_comp_if_basic is irrelevant when in_tyd is a composite
   interface, but when in_tyd is a basic interface, specifies whether
   it is a basic interface used (only) by a composite interface *)

val gen_int : scope -> string -> string -> bool -> inter_tyd -> string
