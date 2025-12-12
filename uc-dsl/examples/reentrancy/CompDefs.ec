(* supporting defintions for Comp.uc *)

require import UCBasicTypes.

(* computation performed by first party on its input n1 from the
   environment *)

op [opaque] f : int -> int = fun (x : int) => `|x| + 1.

(* computation performed by second party on its input n2 from the
   environment *)

op [opaque] g : int -> int = fun (x : int) => `|x| - 1.

(* h m1 m2 is used by a party to compute its output to the
   environment, where m1 is its own input and m2 is the result of the
   computation performed by the other party on its input *)

op [opaque] h : int -> int -> int = fun (x y : int) => x + y.

lemma h_g_simp (x y : int) :
  h x (g y) = x + `|y| - 1.
proof.
rewrite /h /g /#.
qed.

lemma h_f_simp (x y : int) :
  h x (f y) = x + `|y| + 1.
proof.
rewrite /h /g /#.
qed.

hint simplify h_g_simp, h_f_simp.

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

op party_name_to_bool (pn : party_name) : bool =
  with pn = Pt1 => true
  with pn = Pt2 => false.

op bool_to_party_name (b : bool) : party_name =
  if b then Pt1 else Pt2.

(* epdp allowing us to forward party names *)

op epdp_party_name_univ : (party_name, univ) epdp =
  epdp_comp epdp_bool_univ
  (epdp_bijection party_name_to_bool bool_to_party_name).

lemma valid_epdp_party_name_univ :
  valid_epdp epdp_party_name_univ.
proof.
rewrite /epdp_party_name_univ !epdp.
move => pn; by case pn.
move => b; by case b.
qed.

hint simplify valid_epdp_party_name_univ.

(* simulator's view of a party's state - see party states of
   real functionality for comparison *)

type sim_party_state = [
  | SPS_Init
  | SPS_PendingFwdWaitAdvOrOtherFwd
  | SPS_PendingFwdWaitAdv
  | SPS_WaitOtherFwd
  | SPS_WaitInput
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
