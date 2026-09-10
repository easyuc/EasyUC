(* UcGenerateInter module interface *)

open EcScope
open UcTypedSpec

(* if it : inter_tyd corresponds to the interface named by root
   and id, then gen_int scope root id it generates the EasyCrypt
   code for it *)

val gen_int : scope -> string -> string -> inter_tyd -> string
