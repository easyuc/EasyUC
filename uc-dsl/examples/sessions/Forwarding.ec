(* Forwarding.ec *)

(* Definitions Supporting Forwarding.uc *)

require import AllCore UCBasicTypes.
require export Sessions.

(* limit on number of sessions *)

op maxssn : int.

axiom ge0_maxssn : 0 < maxssn.  (* at least one session is allowed *)
