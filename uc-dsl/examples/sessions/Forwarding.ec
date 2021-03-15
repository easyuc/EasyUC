(* Forwarding.ec *)

(* Definition of the Sessions Type for Forwarding.uc *)

require import AllCore UCBasicTypes.
require export SmtMap.

type inst = univ.  (* instance at port *)

type iport = port * inst.  (* port plus instance *)

type sessions = (int, iport * iport * univ) SmtMap.fmap.

op init : sessions = SmtMap.empty.
