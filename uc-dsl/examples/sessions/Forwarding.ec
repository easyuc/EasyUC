(* Forwarding.ec *)

(* Definitions Supporting Forwarding.uc *)

require import AllCore UCBasicTypes.

type subs = univ.  (* subsession *)

type session = subs * port * port.  (* session *)

type fwd_state = [
  | Wait  of univ  (* value to be forwarded *)
  | Final of bool  (* corruption status *)
].
