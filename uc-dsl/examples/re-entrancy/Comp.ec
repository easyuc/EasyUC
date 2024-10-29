(* supporting defintions for Comp.uc *)

require import UCBasicTypes.

(* computation performed by first party on its input n1 from the
   environment *)

op f : int -> int.

(* computation performed by second party on its input n2 from the
   environment *)

op g : int -> int.

(* h m1 m2 is used by a party to compute its output to the
   environment, where m1 is its own input and m2 is the result of the
   computation performed by the other party on its input *)

op h : int -> int -> int.

(* epdp allowing us to forward pairs of ports and integers *)

op epdp_port_int_univ : (port * int, univ) epdp =
  epdp_pair_univ epdp_port_univ epdp_int_univ.

lemma valid_epdp_port_int_univ :
  valid_epdp epdp_port_int_univ.
proof.
by rewrite /epdp_port_int_univ.
qed.

hint simplify valid_epdp_port_int_univ.

(* types used by the ideal functionality and simulator *)

type party_name = [Pt1 | Pt2].  (* party names *)

(* simulator's view of a party's state - see party states of
   real functionality for comparison *)

type sim_party_state = [
  | SPS_Init
  | SPS_PendingFwdWaitAdvOrOtherFwd
  | SPS_PendingFwdWaitAdv
  | SPS_WaitAdvOrOtherFwd
  | SPS_WaitAdvOrInput
  | SPS_PendingOutputWaitAdv
  | SPS_Final
].

(* simulator's view of the state of a forwarder - see states of
   FwdSched in FwdSched.uc for comparison *)

type sim_fwd_state = [
  | SFS_Init
  | SFS_WaitOK
  | SFS_Final
].
