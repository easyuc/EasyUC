(* Forward.ec *)

(* Forwarding Functionality *)

(* This functionality implements authenticated forwarding (Fauth),
   where the adversary is asked to approve the forwarding of a value,
   but may not corrupt either the value or its destination/source *)

prover quorum=2 ["Alt-Ergo" "Z3"].

require import AllCore List ListPO.
require import UCCoreDiffieHellman.

(* theory parameters *)

(* port index of adversary that functionality communicates with *)

op adv_pi : int.

axiom fwd_pi_uniq : uniq [adv_pi; 0].

(* end theory parameters *)

(* request sent to port index 1 of forwarding functionality: pt1 is
   asking to forward u to pt2 *)

op fw_req (func : addr, pt1 pt2 : port, u : univ) : msg =
     (Dir, (func, 1), pt1, UnivPair (UnivPort pt2) u).

op dec_fw_req (m : msg) : (addr * port * port * univ) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Adv \/ pt1.`2 <> 1 \/ ! is_univ_pair v) ?
        None :
        let (v1, v2) = oget (dec_univ_pair v)
        in (! is_univ_port v1) ?
           None :
           Some (pt1.`1, pt2, oget (dec_univ_port v1), v2).

lemma enc_dec_fw_req (func : addr, pt1 pt2 : port, u : univ) :
  dec_fw_req (fw_req func pt1 pt2 u) = Some (func, pt1, pt2, u).
proof.
by rewrite /dec_fw_req /fw_req /= (is_univ_pair (UnivPort pt2) u)
           /= enc_dec_univ_pair oget_some /= (is_univ_port pt2) /=
           enc_dec_univ_port.
qed.

lemma dec_enc_fw_req (m : msg, func : addr, pt1 pt2 : port, u : univ) :
  dec_fw_req m = Some (func, pt1, pt2, u) =>
  fw_req func pt1 pt2 u = m.
proof.
case m => mod pt1' pt2' u'.
rewrite /dec_fw_req /fw_req /=.
case (mod = Adv \/ pt1'.`2 <> 1 \/ ! is_univ_pair u') => //.
rewrite !negb_or /= not_adv.
move => [#] -> pt1'_2 iup_u'.
have [] p : exists (p : univ * univ), dec_univ_pair u' = Some p.
  exists (oget (dec_univ_pair u')); by rewrite -some_oget.
case p => v1 v2 /dec_enc_univ_pair -> /=.
rewrite enc_dec_univ_pair oget_some /=.
case (is_univ_port v1) => // iupt_v1.
have [] pt3 : exists pt3, dec_univ_port v1 = Some pt3.
  exists (oget (dec_univ_port v1)); by rewrite -some_oget.
move => /dec_enc_univ_port => -> /=.
rewrite enc_dec_univ_port oget_some /#.
qed.

op is_fw_req (m : msg) : bool =
     dec_fw_req m <> None.

lemma is_fw_req (func : addr, pt1 pt2 : port, u : univ) :
  is_fw_req (fw_req func pt1 pt2 u).
proof.
by rewrite /is_fw_req enc_dec_fw_req.
qed.

lemma dest_good_fw_req (m : msg) :
  is_fw_req m =>
  (oget (dec_fw_req m)).`1 = m.`2.`1 /\ m.`2.`2 = 1.
proof.
move => ifr_m.
have [] x : exists (x : addr * port * port * univ),
  dec_fw_req m = Some x.
  exists (oget (dec_fw_req m)); by rewrite -some_oget.
case x => x1 x2 x3 x4 /dec_enc_fw_req <-.
by rewrite enc_dec_fw_req oget_some /fw_req.
qed.

lemma not_is_fw_req_suff (m : msg) :
  m.`1 = Adv \/ m.`2.`2 <> 1 => ! is_fw_req m.
proof.
rewrite /is_fw_req /dec_fw_req.
case (m) => mod pt1 pt2 u.
case pt1 => addr1 n1 /=.
smt().
qed.

(* response sent from port index 1 of forwarding functionality to pt2,
   completing the forwarding of u that was requested by pt1 *)

op fw_rsp (func : addr, pt1 pt2 : port, u : univ) : msg =
     (Dir, pt2, (func, 1), UnivPair (UnivPort pt1) u).

op dec_fw_rsp (m : msg) : (addr * port * port * univ) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Adv \/ pt2.`2 <> 1 \/ ! is_univ_pair v) ?
        None :
        let (v1, v2) = oget (dec_univ_pair v)
        in (! is_univ_port v1) ?
           None :
           Some (pt2.`1, oget (dec_univ_port v1), pt1, v2).

lemma enc_dec_fw_rsp (func : addr, pt1 pt2 : port, u : univ) :
  dec_fw_rsp (fw_rsp func pt1 pt2 u) = Some (func, pt1, pt2, u).
proof.
by rewrite /dec_fw_rsp /fw_rsp /= (is_univ_pair (UnivPort pt1) u) /=
           (enc_dec_univ_pair (UnivPort pt1) u) /= oget_some /=
           (is_univ_port pt1) /= enc_dec_univ_port.
qed.

lemma dec_enc_fw_rsp (m : msg, func : addr, pt1 pt2 : port, u : univ) :
  dec_fw_rsp m = Some (func, pt1, pt2, u) =>
  fw_rsp func pt1 pt2 u = m.
proof.
case m => mod pt1' pt2' u'.
rewrite /dec_fw_rsp /fw_rsp /=.
case (mod = Adv \/ pt2'.`2 <> 1 \/ ! is_univ_pair u') => //.
rewrite !negb_or /= not_adv.
move => [#] -> pt2'_2 iup_u'.
have [] p : exists (p : univ * univ), dec_univ_pair u' = Some p.
  exists (oget (dec_univ_pair u')); by rewrite -some_oget.
case p => v1 v2 /dec_enc_univ_pair -> /=.
rewrite enc_dec_univ_pair oget_some /=.
case (is_univ_port v1) => // iupt_v1.
have [] pt3 : exists pt3, dec_univ_port v1 = Some pt3.
  exists (oget (dec_univ_port v1)); by rewrite -some_oget.
move => /dec_enc_univ_port => -> /=.
rewrite enc_dec_univ_port oget_some /#.
qed.

op is_fw_rsp (m : msg) : bool =
     dec_fw_rsp m <> None.

lemma is_fw_rsp (func : addr, pt1 pt2 : port, u : univ) :
  is_fw_rsp (fw_rsp func pt1 pt2 u).
proof.
by rewrite /is_fw_rsp enc_dec_fw_rsp.
qed.

lemma dest_good_fw_rsp (m : msg) :
  is_fw_rsp m => (oget (dec_fw_rsp m)).`3 = m.`2.
proof.
move => ifr_m.
have [] x : exists (x : addr * port * port * univ),
  dec_fw_rsp m = Some x.
  exists (oget (dec_fw_rsp m)); by rewrite -some_oget.
case x => x1 x2 x3 x4 /dec_enc_fw_rsp <-.
by rewrite enc_dec_fw_rsp oget_some /fw_rsp.
qed.

(* message from forwarding functionality to adversary, letting it
   observe that the functionality is proposing to forward u to
   pt2 on behalf of pt1 *)

op fw_obs (func adv : addr, pt1 pt2 : port, u : univ) : msg =
     (Adv, (adv, adv_pi), (func, 1),
      univ_triple (UnivPort pt1) (UnivPort pt2) u).

op dec_fw_obs (m : msg) : (addr * addr * port * port * univ) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Dir \/ pt1.`2 <> adv_pi \/ pt2.`2 <> 1 \/
         ! is_univ_triple v) ?
        None :
        let (v1, v2, v3) = oget (dec_univ_triple v)
        in (! is_univ_port v1 \/ ! is_univ_port v2) ?
           None :
           Some (pt2.`1, pt1.`1,
                 oget (dec_univ_port v1),
                 oget (dec_univ_port v2),
                 v3).

lemma enc_dec_fw_obs (func adv : addr, pt1 pt2 : port, u : univ) :
  dec_fw_obs (fw_obs func adv pt1 pt2 u) = Some (func, adv, pt1, pt2, u).
proof.
by rewrite /fw_obs /dec_fw_obs /=
           (is_univ_triple (UnivPort pt2) (UnivPort pt2) u) /=
           enc_dec_univ_triple oget_some /= (is_univ_port pt1) /=
           !enc_dec_univ_port.
qed.

lemma dec_enc_fw_obs (m : msg, func adv : addr, pt1 pt2 : port, u : univ) :
  dec_fw_obs m = Some (func, adv, pt1, pt2, u) =>
  fw_obs func adv pt1 pt2 u = m.
proof.
case m => mod pt1' pt2' u'.
rewrite /dec_fw_obs /fw_obs /=.
case (mod = Dir \/ pt1'.`2 <> adv_pi \/ pt2'.`2 <> 1 \/
      ! is_univ_triple u') => //.
rewrite !negb_or not_dir /=.
move => [#] -> pt1'_2 pt2'_2 iut_u'.
have [] t : exists (t : univ * univ * univ), dec_univ_triple u' = Some t.
  exists (oget (dec_univ_triple u')); by rewrite -some_oget.
case t => v1 v2 v3 /dec_enc_univ_triple -> /=.
rewrite enc_dec_univ_triple oget_some /=.
case (! is_univ_port v1 \/ ! is_univ_port v2) => //.
rewrite negb_or /=.
move => [#] iupt_v1 iupt_v2 [#] pt2'_1 pt1'_1 odupt_v1 odupt_v2 ->.
have : dec_univ_port v1 = Some pt1
  by rewrite -odupt_v1 -some_oget.
move => /dec_enc_univ_port ->.
have : dec_univ_port v2 = Some pt2
  by rewrite -odupt_v2 -some_oget.
move => /dec_enc_univ_port -> /#.
qed.

op is_fw_obs (m : msg) : bool =
     dec_fw_obs m <> None.

lemma is_fw_obs (func adv : addr, pt1 pt2 : port, u : univ) :
  is_fw_obs (fw_obs func adv pt1 pt2 u).
proof.
by rewrite /is_fw_obs enc_dec_fw_obs.
qed.

(* message from adversary telling forwarding functionality it may
   proceed with forwarding *)

op fw_ok (func adv : addr) : msg =
     (Adv, (func, 1), (adv, adv_pi), UnivUnit).

op dec_fw_ok (m : msg) : (addr * addr) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Dir \/ pt1.`2 <> 1 \/ pt2.`2 <> adv_pi \/
         v <> UnivUnit) ?
        None :
        Some (pt1.`1, pt2.`1).

lemma enc_dec_fw_ok (func adv : addr) :
  dec_fw_ok (fw_ok func adv) = Some (func, adv).
proof.
by rewrite /dec_fw_ok /fw_ok.
qed.

lemma dec_enc_fw_ok (m : msg, func adv) :
  dec_fw_ok m = Some (func, adv) =>
  fw_ok func adv = m.
proof.
case m => mod pt1' pt2' u'.
rewrite /dec_fw_ok /fw_ok /=.
case (mod = Dir \/ pt1'.`2 <> 1 \/ pt2'.`2 <> adv_pi \/ u' <> UnivUnit) => //.
rewrite !negb_or not_dir /#.
qed.

op is_fw_ok (m : msg) : bool =
     dec_fw_ok m <> None.

lemma is_fw_ok (func adv : addr) :
  is_fw_ok (fw_ok func adv).
proof. done. qed.

lemma dest_good_fw_ok (m : msg) :
  is_fw_ok m => (oget (dec_fw_ok m)).`1 = m.`2.`1 /\
  m.`2.`2 = 1.
proof.
move => ifo_m.
have [] x : exists (x : addr * addr), dec_fw_ok m = Some x.
  exists (oget (dec_fw_ok m)); by rewrite -some_oget.
case x => x1 x2 /dec_enc_fw_ok <-.
by rewrite enc_dec_fw_ok.
qed.

type fw_state = [
    FwStateInit
  | FwStateWait  of port & port & univ
  | FwStateFinal of port & port & univ
].

module Forw : FUNC = {
  var self, adv : addr
  var st : fw_state

  proc init(self_ adv_ : addr) : unit = {
    self <- self_; adv <- adv_; st <- FwStateInit;
  }

  proc invoke(m : msg) : msg option = {
    var pt1, pt2 : port; var u : univ;
    var addr1, addr2 : addr;
    var r : msg option <- None;
    match st with
      FwStateInit => {
        match dec_fw_req m with
          Some x => {
            (addr1, pt1, pt2, u) <- x;
            if (self = addr1 /\
                ! self <= pt1.`1 /\ ! self <= pt2.`1 /\
                ! adv <= pt1.`1 /\ ! adv <= pt2.`1) {
              r <- Some (fw_obs self adv pt1 pt2 u);
              st <- FwStateWait pt1 pt2 u;
            }
          }
        | None => { }
        end;
      }
    | FwStateWait pt1 pt2 u => {
        match dec_fw_ok m with
          Some x => {
            (addr1, addr2) <- x;
            if (addr1 = self) {
              r <- Some (fw_rsp self pt1 pt2 u);
              st <- FwStateFinal pt1 pt2 u;
            }
          }
        | None => { }
        end;
      }
    | FwStateFinal _ _ _ => { }
    end;
    return r;
  }
}.

(* termination metric and proof *)

op term_metric_max : int = 2.

(* FIXME when better glob type

   print glob Forw:
   1: Forw.st : fw_state
   2: Forw.adv : addr
   3: Forw.self : addr *)

op term_metric (g : glob Forw) : int =
     match g.`1 with
       FwStateInit        => 2
     | FwStateWait _ _ _  => 1
     | FwStateFinal _ _ _ => 0
     end.

lemma ge0_term_metric (g : glob Forw) : 0 <= term_metric g.
proof.
smt().
qed.

lemma init :
  equiv
  [Forw.init ~ Forw.init :
   ={self_, adv_} ==> ={res, glob Forw}].
proof.
proc; auto.
qed.

lemma term_init :
  equiv
  [Forw.init ~ Forw.init :
   ={self_, adv_} ==>
   ={res, glob Forw} /\
   term_metric (glob Forw){1} = term_metric_max].
proof.
proc; auto.
qed.

lemma term_invoke (n : int) :
  equiv
  [Forw.invoke ~ Forw.invoke :
   ={m, glob Forw} /\
   term_metric (glob Forw){1} = n ==>
   ={res, glob Forw} /\
   (res{1} = None \/ term_metric (glob Forw){1} < n)].
proof.
proc; sp 1 1.
match => //.
match => // x y.
sp 1 1.
if; first move => |> &1 &2 -> //.
auto => |> &1 &2 -> //.
auto.
move => pt1 pt2 u pt1' pt2' u'.
match => // x y.
sp 1 1.
if.
(*FIXME - use better crush*)
move => &1 &2 [#] *.
move : H7 H1 H2 H H0 H10.
move => -> -> /= -> <- [#] -> _ -> //.
auto.
auto.
qed.
