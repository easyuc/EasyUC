(* Forwarding.ec *)

(* Definition of the Sessions Type for Forwarding.uc *)

require import AllCore UCBasicTypes.
require export SmtMap.

type sessions = (int, port * port * univ) SmtMap.fmap.

op init : sessions = SmtMap.empty.
