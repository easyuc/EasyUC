(* KeyExchange.ec *)

(* Diffie-Hellman Key Exchange *)

prover quorum=2 ["Alt-Ergo" "Z3"].

require import AllCore List FSet SmtMap Distr ListAux ListPO.
require import UCCoreDiffieHellman.
require Forward RedundantHashing.

(* theory parameters *)

(* port index of adversary that forwarding functionalities communicate
   with *)

op adv_fw_pi : int.

(* port index of adversary for key exchange simulator *)

op ke_sim_adv_pi : int.

axiom ke_pi_uniq : uniq [ke_sim_adv_pi; adv_fw_pi; 0].

(* end theory parameters *)

(* request sent to port index 1 of key exchange functionality: pt1
   wants to exchange a key with pt2 *)

op ke_req1 (func : addr, pt1 pt2 : port) : msg =
     (Dir, (func, 1), pt1, UnivPort pt2).

op dec_ke_req1 (m : msg) : (addr * port * port) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Adv \/ pt1.`2 <> 1 \/ ! is_univ_port v) ?
        None :
        Some (pt1.`1, pt2, oget (dec_univ_port v)).

lemma enc_dec_ke_req1 (func : addr, pt1 pt2 : port) :
  dec_ke_req1 (ke_req1 func pt1 pt2) = Some (func, pt1, pt2).
proof. done. qed.

op is_ke_req1 (m : msg) : bool =
     dec_ke_req1 m <> None.

lemma is_ke_req1 (func : addr, pt1 pt2 : port) :
  is_ke_req1 (ke_req1 func pt1 pt2).
proof. done. qed.

(* response sent from port index 2 of key exchange functionality to
   pt2, completing first phase of key exchange initiated by pt1 *)

op ke_rsp1 (func : addr, pt1 pt2 : port, x : key) : msg =
     (Dir, pt2, (func, 2), UnivPair (UnivPort pt1, UnivBase (BaseKey x))).

op dec_ke_rsp1 (m : msg) : (addr * port * port * key) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Adv \/ pt2.`2 <> 2 \/ ! is_univ_pair v) ?
        None :
        let (v1, v2) = oget (dec_univ_pair v)
        in (! is_univ_port v1 \/ ! is_univ_base v2) ?
           None :
           let b = oget (dec_univ_base v2)
           in (! is_base_key b) ?
              None :
              Some (pt2.`1, oget (dec_univ_port v1), pt1,
                    oget (dec_base_key b)).

lemma enc_dec_ke_rsp1 (func : addr, pt1 pt2 : port, x : key) :
  dec_ke_rsp1 (ke_rsp1 func pt1 pt2 x) = Some (func, pt1, pt2, x).
proof.
by rewrite /ke_rsp1 /dec_ke_rsp1 /=
           (is_univ_pair (UnivPort pt1, UnivBase (BaseKey x))) /=
           oget_some /= (is_univ_port pt1) /= oget_some.
qed.

op is_ke_rsp1 (m : msg) : bool =
     dec_ke_rsp1 m <> None.

lemma is_ke_rsp1 (func : addr, pt1 pt2 : port, x : key) :
  is_ke_rsp1 (ke_rsp1 func pt1 pt2 x).
proof.
by rewrite /is_ke_rsp1 enc_dec_ke_rsp1.
qed.

lemma dest_good_ke_rsp1 (m : msg) :
  is_ke_rsp1 m => (oget (dec_ke_rsp1 m)).`3 = m.`2.
proof.
rewrite /is_ke_rsp1 /dec_ke_rsp1 /=.
case m => x1 x2 x3 x4 /=.
case (x1 = Adv \/ x3.`2 <> 2 \/ ! is_univ_pair x4) => //=.
rewrite !negb_or /= not_adv.
case x4; first 7 smt().
move => [z1 z2] [#] _ _.
rewrite is_univ_pair /= oget_some /=.
case (! is_univ_port z1 \/ ! is_univ_base z2) => //=.
rewrite negb_or /=.
by case (! is_base_key (oget (dec_univ_base z2))).
qed.

(* request sent to port index 2 of key exchange functionality by pt2 to
   initiate phase 2 of key exchange with pt1 *)

op ke_req2 (func : addr, pt2 : port) : msg =
     (Dir, (func, 2), pt2, UnivUnit).

op dec_ke_req2 (m : msg) : (addr * port) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Adv \/ pt1.`2 <> 2 \/ v <> UnivUnit) ?
        None :
        Some (pt1.`1, pt2).

lemma enc_dec_ke_req2 (func : addr, pt2 : port) :
  dec_ke_req2 (ke_req2 func pt2) = Some (func, pt2).
proof. done. qed.

op is_ke_req2 (m : msg) : bool =
     dec_ke_req2 m <> None.

lemma is_ke_req2 (func : addr, pt2 : port) :
  is_ke_req2 (ke_req2 func pt2).
proof. done. qed.

(* response sent from port index 1 of key exchange functionality to
   pt1, completing second phase of key exchange with pt2 initiated by
   itself *)

op ke_rsp2 (func : addr, pt1 : port, x : key) : msg =
     (Dir, pt1, (func, 1), UnivBase (BaseKey x)).

op dec_ke_rsp2 (m : msg) : (addr * port * key) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Adv \/ pt2.`2 <> 1 \/ ! is_univ_base v) ?
        None :
        let bse = oget (dec_univ_base v)
        in (! is_base_key bse) ?
           None :
           Some (pt2.`1, pt1, oget (dec_base_key bse)).

lemma enc_dec_ke_rsp2 (func : addr, pt1 : port, x : key) :
  dec_ke_rsp2 (ke_rsp2 func pt1 x) = Some (func, pt1, x).
proof.
by rewrite /ke_rsp2 /dec_ke_rsp2 /= (is_univ_base (BaseKey x)) /=
           oget_some (is_base_key x).
qed.

op is_ke_rsp2 (m : msg) : bool =
     dec_ke_rsp2 m <> None.

lemma is_ke_rsp2 (func : addr, pt1 : port, x : key) :
  is_ke_rsp2 (ke_rsp2 func pt1 x).
proof.
by rewrite /is_ke_rsp2 enc_dec_ke_rsp2.
qed.

lemma dest_good_ke_rsp2 (m : msg) :
  is_ke_rsp2 m => (oget (dec_ke_rsp2 m)).`2 = m.`2.
proof.
rewrite /is_ke_rsp2 /dec_ke_rsp2 /=.
case m => x1 x2 x3 x4 /=.
case (x1 = Adv \/ x3.`2 <> 1 \/ ! is_univ_base x4) => //= H1.
by case (is_base_key (oget (dec_univ_base x4))).
qed.

(* Real Functionality *)

clone Forward as Fwd1
  with op adv_pi <- adv_fw_pi
proof *.
realize fwd_pi_uniq. by have := ke_pi_uniq. qed.

clone Forward as Fwd2
  with op adv_pi <- adv_fw_pi
proof *.
realize fwd_pi_uniq. by have := ke_pi_uniq. qed.

(* state for Party 1 *)

type ke_real_p1_state = [
    KERealP1StateWaitReq1
  | KERealP1StateWaitFwd2 of (port * port * exp)
  | KERealP1StateFinal    of (port * port * exp)
].

op dec_ke_real_p1_state_wait_fwd2 (st : ke_real_p1_state) :
     (port * port * exp) option =
     with st = KERealP1StateWaitReq1   => None
     with st = KERealP1StateWaitFwd2 x => Some x
     with st = KERealP1StateFinal _    => None.

lemma enc_dec_ke_real_p1_state_wait_fwd2 (x : port * port * exp) :
  dec_ke_real_p1_state_wait_fwd2 (KERealP1StateWaitFwd2 x) = Some x.
proof. done. qed.

op is_ke_real_p1_state_wait_fwd2 (st : ke_real_p1_state) : bool =
  dec_ke_real_p1_state_wait_fwd2 st <> None.

lemma is_ke_real_p1_state_wait_fwd2 (x : port * port * exp) :
  is_ke_real_p1_state_wait_fwd2 (KERealP1StateWaitFwd2 x).
proof. done. qed.

op dec_ke_real_p1_state_final (st : ke_real_p1_state) :
     (port * port * exp) option =
     with st = KERealP1StateWaitReq1   => None
     with st = KERealP1StateWaitFwd2 _ => None
     with st = KERealP1StateFinal x    => Some x.

lemma enc_dec_ke_real_p1_state_final (x : port * port * exp) :
  dec_ke_real_p1_state_final (KERealP1StateFinal x) = Some x.
proof. done. qed.

op is_ke_real_p1_state_final (st : ke_real_p1_state) : bool =
  dec_ke_real_p1_state_final st <> None.

lemma is_ke_real_p1_state_final (x : port * port * exp) :
  is_ke_real_p1_state_final (KERealP1StateFinal x).
proof. done. qed.

(* state for Party 2 *)

type ke_real_p2_state = [
    KERealP2StateWaitFwd1
  | KERealP2StateWaitReq2 of (port * port * exp)
  | KERealP2StateFinal    of (port * port * exp)
].

op dec_ke_real_p2_state_wait_req2 (st : ke_real_p2_state) :
     (port * port * exp) option =
     with st = KERealP2StateWaitFwd1   => None
     with st = KERealP2StateWaitReq2 x => Some x
     with st = KERealP2StateFinal _    => None.

lemma enc_dec_ke_real_p2_state_wait_req2 (x : port * port * exp) :
  dec_ke_real_p2_state_wait_req2 (KERealP2StateWaitReq2 x) = Some x.
proof. done. qed.

op is_ke_real_p2_state_wait_req2 (st : ke_real_p2_state) : bool =
  dec_ke_real_p2_state_wait_req2 st <> None.

lemma is_ke_real_p2_state_wait_req2 (x : port * port * exp) :
  is_ke_real_p2_state_wait_req2 (KERealP2StateWaitReq2 x).
proof. done. qed.

op dec_ke_real_p2_state_final (st : ke_real_p2_state) :
     (port * port * exp) option =
     with st = KERealP2StateWaitFwd1   => None
     with st = KERealP2StateWaitReq2 _ => None
     with st = KERealP2StateFinal x    => Some x.

lemma enc_dec_ke_real_p2_state_final (x : port * port * exp) :
  dec_ke_real_p2_state_final (KERealP2StateFinal x) = Some x.
proof. done. qed.

op is_ke_real_p2_state_final (st : ke_real_p2_state) : bool =
  dec_ke_real_p2_state_final st <> None.

lemma is_ke_real_p2_state_final (x : port * port * exp) :
  is_ke_real_p2_state_final (KERealP2StateFinal x).
proof. done. qed.

module KEReal : FUNC = {
  var self, adv : addr
  var st1 : ke_real_p1_state
  var st2 : ke_real_p2_state

  (* Party 1 (P1) manages ports (self, 1) and (self, 3)
     Party 2 (P2) manages ports (self, 2) and (self, 4)
     First forwarder (Fwd1) is at address self ++ [1]
     Second forwarder (Fwd2) is at address self ++ [2] *)

  proc init(self_ adv_ : addr) : unit = {
    self <- self_; adv <- adv_;
    Fwd1.Forw.init(self ++ [1], adv); Fwd2.Forw.init(self ++ [2], adv);
    st1 <- KERealP1StateWaitReq1; st2 <- KERealP2StateWaitFwd1;
  }

  proc party1(m : msg) : msg option = {
    var pt1, pt2, pt1', pt2' : port; var addr : addr;
    var u : univ; var x2 : key; var q1 : exp;
    var r : msg option <- None;
    if (st1 = KERealP1StateWaitReq1) {
      if (is_ke_req1 m) {
        (* destination of m is (self, 1) *)
        (addr, pt1, pt2) <- oget (dec_ke_req1 m);
        if (! self <= pt1.`1 /\ ! self <= pt2.`1 /\
            ! adv <= pt1.`1 /\ ! adv <= pt2.`1) {
          q1 <$ dexp;
          r <-
            Some
            (Fwd1.fw_req
             (self ++ [1]) (self, 3) (self, 4)
              (univ_triple (UnivPort pt1) (UnivPort pt2)
               (UnivBase (BaseKey (g ^ q1)))));
          st1 <- KERealP1StateWaitFwd2 (pt1, pt2, q1);
        }
      }
    }
    elif (is_ke_real_p1_state_wait_fwd2 st1) {
      (pt1, pt2, q1) <- oget (dec_ke_real_p1_state_wait_fwd2 st1);
      if (Fwd2.is_fw_rsp m) {
        (addr, pt1', pt2', u) <- oget (Fwd2.dec_fw_rsp m);
        if (pt2' = (self, 3)) {
          (* destination of m is (self, 3) *)
          x2 <- oget (dec_base_key (oget (dec_univ_base u)));
          r <- Some (ke_rsp2 self pt1 (x2 ^ q1));
          st1 <- KERealP1StateFinal (pt1, pt2, q1);
        }
      }
    }
    else {  (* is_ke_real_p1_state_final st1 *)
    }
    return r;
  }

  proc party2(m : msg) : msg option = {
    var pt1, pt2, pt1', pt2' : port; var addr : addr;
    var u, v1, v2, v3 : univ; var x1 : key; var q2 : exp;
    var r : msg option <- None;
    if (st2 = KERealP2StateWaitFwd1) {
      if (Fwd1.is_fw_rsp m) {
        (addr, pt1', pt2', u) <- oget (Fwd1.dec_fw_rsp m);
        if (pt2' = (self, 4)) {
          (* destination of m is (self, 4) *)
          (v1, v2, v3) <- oget (dec_univ_triple u);
          pt1 <- oget (dec_univ_port v1);
          pt2 <- oget (dec_univ_port v2);
          x1 <- oget (dec_base_key (oget (dec_univ_base v3)));
          q2 <$ dexp;
          r <- Some (ke_rsp1 self pt1 pt2 (x1 ^ q2));
          st2 <- KERealP2StateWaitReq2 (pt1, pt2, q2);
        }
      }
    }
    elif (is_ke_real_p2_state_wait_req2 st2) {
      (pt1, pt2, q2) <- oget (dec_ke_real_p2_state_wait_req2 st2);
      if (is_ke_req2 m) {
        (* destination of m is (self, 2) *)
        (addr, pt2') <- oget (dec_ke_req2 m);
        if (pt2' = pt2) {
          r <-
            Some
            (Fwd2.fw_req
             (self ++ [2]) (self, 4) (self, 3)
             (UnivBase (BaseKey (g ^ q2))));
          st2 <- KERealP2StateFinal (pt1, pt2, q2);
        }
      }
    }
    else {  (* is_ke_real_p2_state_final st2 *)
    }
    return r;
  }

  proc loop(m : msg) : msg option = {
    var r : msg option <- None;
    var not_done : bool <- true;

    (* invariant: 

         m.`2.`1 = self /\
         (m.`2.`2 = 1 \/ m.`2.`2 = 2 \/
          m.`2.`2 = 3 \/ m.`2.`2 = 4) \/
         self ++ [1] <= m.`2.`1 \/
         self ++ [2] <= m.`2.`1 *)

    while (not_done) {
      if (m.`2.`1 = self /\ (m.`2.`2 = 1 \/ m.`2.`2 = 3)) {
        r <- party1(m);
      }
      elif (m.`2.`1 = self /\ (m.`2.`2 = 2 \/ m.`2.`2 = 4)) {
        r <- party2(m);
      }
      elif (self ++ [1] <= m.`2.`1) {
        r <- Fwd1.Forw.invoke(m);
      }
      else {  (* self ++ [2] <= m.`2.`1 *)
        r <- Fwd2.Forw.invoke(m);
      }

      if (r = None \/ ! self <= (oget r).`2.`1) {
        not_done <- false;
      }
      else {
        m <- oget r;
      }
    }
    return r;
  }

  proc invoke(m : msg) : msg option = {
    var mod : mode; var pt1, pt2 : port; var u : univ;
    var addr1 : addr; var n1 : int;
    var r : msg option <- None;
    (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
    if ((mod = Dir /\ addr1 = self /\ (n1 = 1 \/ n1 = 2)) \/
        (mod = Adv /\ (self ++ [1] <= addr1 \/ self ++ [2] <= addr1))) {
      r <- loop(m);
    }
    return r;
  }
}.

(* Ideal Functionality *)

(* request sent from port index 3 of key exchange ideal functionality
   to port index ke_sim_adv_pi of key exchange simulator, initiating
   first phase of execution of simulator *)

op ke_sim_req1 (ideal adv : addr, pt1 pt2 : port) : msg =
     (Adv, (adv, ke_sim_adv_pi), (ideal, 3),
      UnivPair (UnivPort pt1, UnivPort pt2)).

op dec_ke_sim_req1 (m : msg) : (addr * addr * port * port) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Dir \/ pt1.`2 <> ke_sim_adv_pi \/ pt2.`2 <> 3 \/
         ! is_univ_pair v) ?
        None :
        let (v1, v2) = oget (dec_univ_pair v)
        in (! is_univ_port v1 \/ ! is_univ_port v2) ?
           None :
           Some (pt2.`1, pt1.`1,
                 oget (dec_univ_port v1), oget (dec_univ_port v2)).

lemma enc_dec_ke_sim_req1 (ideal adv : addr, pt1 pt2 : port) :
  dec_ke_sim_req1 (ke_sim_req1 ideal adv pt1 pt2) =
  Some (ideal, adv, pt1, pt2).
proof. done. qed.

op is_ke_sim_req1 (m : msg) : bool =
     dec_ke_sim_req1 m <> None.

lemma is_ke_sim_req1 (ideal adv : addr, pt1 pt2 : port) :
  is_ke_sim_req1 (ke_sim_req1 ideal adv pt1 pt2).
proof. done. qed.

(* response sent from port ke_sim_adv_pi of key exchange simulator to
   port 3 of key exchange ideal functionality, completing first or
   second phase of simulator execution *)

op ke_sim_rsp (ideal adv : addr) : msg =
     (Adv, (ideal, 3), (adv, ke_sim_adv_pi), UnivUnit).

op dec_ke_sim_rsp (m : msg) : (addr * addr) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Dir \/ pt1.`2 <> 3 \/ pt2.`2 <> ke_sim_adv_pi \/
         ! v = UnivUnit) ?
        None :
        Some (pt1.`1, pt2.`1).

lemma enc_dec_ke_sim_rsp (ideal adv : addr) :
  dec_ke_sim_rsp (ke_sim_rsp ideal adv) = Some (ideal, adv).
proof. done. qed.

op is_ke_sim_rsp (m : msg) : bool =
     dec_ke_sim_rsp m <> None.

lemma is_ke_sim_rsp (ideal adv : addr) :
  is_ke_sim_rsp (ke_sim_rsp ideal adv).
proof. done. qed.

lemma dest_good_ke_sim_rsp (m : msg) :
  is_ke_sim_rsp m => (oget (dec_ke_sim_rsp m)).`1 = m.`2.`1.
proof.
rewrite /is_ke_sim_rsp /dec_ke_sim_rsp /=.
case m => x1 x2 x3 x4 /=.
by case (x1 = Dir \/ x2.`2 <> 3 \/ x3.`2 <> ke_sim_adv_pi \/ x4 <> UnivUnit).
qed.

lemma port_good_ke_sim_rsp (m : msg) :
  is_ke_sim_rsp m => m.`2.`2 = 3.
proof.
rewrite /is_ke_sim_rsp /dec_ke_sim_rsp /=.
case m => x1 x2 x3 x4 /=.
case (x1 = Dir \/ x2.`2 <> 3 \/ x3.`2 <> ke_sim_adv_pi \/ x4 <> UnivUnit) => //.
rewrite !negb_or /#.
qed.

(* request sent from port 3 of key exchange ideal functionality to
   port ke_sim_adv_pi of key exchange simulator, initiating second phase
   of execution of simulator *)

op ke_sim_req2 (ideal adv : addr) : msg =
     (Adv, (adv, ke_sim_adv_pi), (ideal, 3), UnivUnit).

op dec_ke_sim_req2 (m : msg) : (addr * addr) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Dir \/ pt1.`2 <> ke_sim_adv_pi \/ pt2.`2 <> 3 \/
         ! v = UnivUnit) ?
        None :
        Some (pt2.`1, pt1.`1).

lemma enc_dec_ke_sim_req2 (ideal adv : addr) :
  dec_ke_sim_req2 (ke_sim_req2 ideal adv) = Some (ideal, adv).
proof. done. qed.

op is_ke_sim_req2 (m : msg) : bool =
     dec_ke_sim_req2 m <> None.

lemma is_ke_sim_req2 (ideal adv : addr) :
  is_ke_sim_req2 (ke_sim_req2 ideal adv).
proof. done. qed.

type ke_ideal_state = [
    KEIdealStateWaitReq1
  | KEIdealStateWaitSim1 of (port * port)
  | KEIdealStateWaitReq2 of (port * port * exp)
  | KEIdealStateWaitSim2 of (port * port * exp)
  | KEIdealStateFinal    of (port * port * exp)
].

op dec_ke_ideal_state_wait_sim1 (st : ke_ideal_state) :
     (port * port) option =
     with st = KEIdealStateWaitReq1   => None
     with st = KEIdealStateWaitSim1 x => Some x
     with st = KEIdealStateWaitReq2 _ => None
     with st = KEIdealStateWaitSim2 _ => None
     with st = KEIdealStateFinal _    => None.

lemma enc_dec_ke_ideal_state_wait_sim1 (x : port * port) :
  dec_ke_ideal_state_wait_sim1 (KEIdealStateWaitSim1 x) = Some x.
proof. done. qed.

op is_ke_ideal_state_wait_sim1 (st : ke_ideal_state) : bool =
  dec_ke_ideal_state_wait_sim1 st <> None.

lemma is_ke_ideal_state_wait_sim1 (x : port * port) :
  is_ke_ideal_state_wait_sim1 (KEIdealStateWaitSim1 x).
proof. done. qed.

op dec_ke_ideal_state_wait_req2 (st : ke_ideal_state) :
     (port * port * exp) option =
     with st = KEIdealStateWaitReq1   => None
     with st = KEIdealStateWaitSim1 _ => None
     with st = KEIdealStateWaitReq2 x => Some x
     with st = KEIdealStateWaitSim2 _ => None
     with st = KEIdealStateFinal _    => None.

lemma enc_dec_ke_ideal_state_wait_req2 (x : port * port * exp) :
  dec_ke_ideal_state_wait_req2 (KEIdealStateWaitReq2 x) = Some x.
proof. done. qed.

op is_ke_ideal_state_wait_req2 (st : ke_ideal_state) : bool =
  dec_ke_ideal_state_wait_req2 st <> None.

lemma is_ke_ideal_state_wait_req2 (x : port * port * exp) :
  is_ke_ideal_state_wait_req2 (KEIdealStateWaitReq2 x).
proof. done. qed.

op dec_ke_ideal_state_wait_sim2 (st : ke_ideal_state) :
     (port * port * exp) option =
     with st = KEIdealStateWaitReq1   => None
     with st = KEIdealStateWaitSim1 _ => None
     with st = KEIdealStateWaitReq2 _ => None
     with st = KEIdealStateWaitSim2 x => Some x
     with st = KEIdealStateFinal _    => None.

lemma enc_dec_ke_ideal_state_wait_sim2 (x : port * port * exp) :
  dec_ke_ideal_state_wait_sim2 (KEIdealStateWaitSim2 x) = Some x.
proof. done. qed.

op is_ke_ideal_state_wait_sim2 (st : ke_ideal_state) : bool =
  dec_ke_ideal_state_wait_sim2 st <> None.

lemma is_ke_ideal_state_wait_sim2 (x : port * port * exp) :
  is_ke_ideal_state_wait_sim2 (KEIdealStateWaitSim2 x).
proof. done. qed.

op dec_ke_ideal_state_final (st : ke_ideal_state) :
     (port * port * exp) option =
     with st = KEIdealStateWaitReq1   => None
     with st = KEIdealStateWaitSim1 _ => None
     with st = KEIdealStateWaitReq2 _ => None
     with st = KEIdealStateWaitSim2 _ => None
     with st = KEIdealStateFinal x    => Some x.

lemma enc_dec_ke_ideal_state_final (x : port * port * exp) :
  dec_ke_ideal_state_final (KEIdealStateFinal x) = Some x.
proof. done. qed.

op is_ke_ideal_state_final (st : ke_ideal_state) : bool =
  dec_ke_ideal_state_final st <> None.

lemma is_ke_ideal_state_final (x : port * port * exp) :
  is_ke_ideal_state_final (KEIdealStateFinal x).
proof. done. qed.

module KEIdeal : FUNC = {
  var self, adv : addr
  var st : ke_ideal_state

  proc init(self_ adv_ : addr) : unit = {
    self <- self_; adv <- adv_;
    st <- KEIdealStateWaitReq1;
  }

  proc parties(m : msg) : msg option = {
    var pt1, pt2, pt2' : port; var addr1, addr2 : addr;
    var q : exp;
    var r : msg option <- None;
    if (st = KEIdealStateWaitReq1) {
      if (is_ke_req1 m) {
        (* destination of m is (self, 1), mode of m is Dir *)
        (addr1, pt1, pt2) <- oget (dec_ke_req1 m);
        if (! self <= pt1.`1 /\ ! self <= pt2.`1 /\
            ! adv <= pt1.`1 /\ ! adv <= pt2.`1) {
          r <- Some (ke_sim_req1 self adv pt1 pt2);
          st <- KEIdealStateWaitSim1 (pt1, pt2);
        }
      }
    }
    elif (is_ke_ideal_state_wait_sim1 st) {
      (pt1, pt2) <- oget (dec_ke_ideal_state_wait_sim1 st);
      if (is_ke_sim_rsp m) {
        (* destination of m is (self, 3), mode of m is Adv *)
        q <$ dexp;
        r <- Some (ke_rsp1 self pt1 pt2 (g ^ q));
        st <- KEIdealStateWaitReq2 (pt1, pt2, q);
      }
    }
    elif (is_ke_ideal_state_wait_req2 st) {
      (pt1, pt2, q) <- oget (dec_ke_ideal_state_wait_req2 st);
      if (is_ke_req2 m) {
        (* destination of m is (self, 2), mode of m is Dir *)
        (addr1, pt2') <- oget (dec_ke_req2 m);
        if (pt2' = pt2) {
          r <- Some (ke_sim_req2 self adv);
          st <- KEIdealStateWaitSim2 (pt1, pt2, q);
        }
      }
    }
    elif (is_ke_ideal_state_wait_sim2 st) {
      (pt1, pt2, q) <- oget (dec_ke_ideal_state_wait_sim2 st);
      if (is_ke_sim_rsp m) {
        (* destination of m is (self, 3), mode of m is Adv *)
        r <- Some (ke_rsp2 self pt1 (g ^ q));
        st <- KEIdealStateFinal (pt1, pt2, q);
      }
    }
    else {  (* st = KEIdealStateFinal *)
    }
    return r;
  }

  proc invoke(m : msg) : msg option = {
    var mod : mode; var pt1, pt2 : port; var u : univ;
    var addr1, addr2 : addr; var n1, n2 : int;
    var r : msg option <- None;
    (mod, pt1, pt2, u) <- m;
    (addr1, n1) <- pt1;
    if ((mod = Dir /\ addr1 = self /\ (n1 = 1 \/ n1 = 2)) \/
        (mod = Adv /\ addr1 = self /\ n1 = 3)) {
      r <- parties(m);
    }
    return r;
  }
}.

(* Simulator *)

type ke_sim_state = [
    KESimStateWaitReq1
  | KESimStateWaitAdv1 of (addr * exp)
  | KESimStateWaitReq2 of (addr * exp * exp)
  | KESimStateWaitAdv2 of (addr * exp * exp)
  | KESimStateFinal    of (addr * exp * exp)
].

op dec_ke_sim_state_wait_adv1 (st : ke_sim_state) : (addr * exp) option =
     with st = KESimStateWaitReq1   => None
     with st = KESimStateWaitAdv1 x => Some x
     with st = KESimStateWaitReq2 _ => None
     with st = KESimStateWaitAdv2 _ => None
     with st = KESimStateFinal _    => None.

lemma enc_dec_ke_sim_state_wait_adv1 (x : addr * exp) :
  dec_ke_sim_state_wait_adv1 (KESimStateWaitAdv1 x) = Some x.
proof. done. qed.

op is_ke_sim_state_wait_adv1 (st : ke_sim_state) : bool =
  dec_ke_sim_state_wait_adv1 st <> None.

lemma is_ke_sim_state_wait_adv1 (x : addr * exp) :
  is_ke_sim_state_wait_adv1 (KESimStateWaitAdv1 x).
proof. done. qed.

op dec_ke_sim_state_wait_req2 (st : ke_sim_state) :
     (addr * exp * exp) option =
     with st = KESimStateWaitReq1   => None
     with st = KESimStateWaitAdv1 _ => None
     with st = KESimStateWaitReq2 x => Some x
     with st = KESimStateWaitAdv2 _ => None
     with st = KESimStateFinal _    => None.

lemma enc_dec_ke_sim_state_wait_req2 (x : addr * exp * exp) :
  dec_ke_sim_state_wait_req2 (KESimStateWaitReq2 x) = Some x.
proof. done. qed.

op is_ke_sim_state_wait_req2 (st : ke_sim_state) : bool =
  dec_ke_sim_state_wait_req2 st <> None.

lemma is_ke_sim_state_wait_req2 (x : addr * exp * exp) :
  is_ke_sim_state_wait_req2 (KESimStateWaitReq2 x).
proof. done. qed.

op dec_ke_sim_state_wait_adv2 (st : ke_sim_state) :
     (addr * exp * exp) option =
     with st = KESimStateWaitReq1   => None
     with st = KESimStateWaitAdv1 _ => None
     with st = KESimStateWaitReq2 _ => None
     with st = KESimStateWaitAdv2 x => Some x
     with st = KESimStateFinal _    => None.

lemma enc_dec_ke_sim_state_wait_adv2 (x : addr * exp * exp) :
  dec_ke_sim_state_wait_adv2 (KESimStateWaitAdv2 x) = Some x.
proof. done. qed.

op is_ke_sim_state_wait_adv2 (st : ke_sim_state) : bool =
  dec_ke_sim_state_wait_adv2 st <> None.

lemma is_ke_sim_state_wait_adv2 (x : addr * exp * exp) :
  is_ke_sim_state_wait_adv2 (KESimStateWaitAdv2 x).
proof. done. qed.

op dec_ke_sim_state_final (st : ke_sim_state) :
     (addr * exp * exp) option =
     with st = KESimStateWaitReq1   => None
     with st = KESimStateWaitAdv1 _ => None
     with st = KESimStateWaitReq2 _ => None
     with st = KESimStateWaitAdv2 _ => None
     with st = KESimStateFinal x    => Some x.

lemma enc_dec_ke_sim_state_final (x : addr * exp * exp) :
  dec_ke_sim_state_final (KESimStateFinal x) = Some x.
proof. done. qed.

op is_ke_sim_state_final (st : ke_sim_state) : bool =
  dec_ke_sim_state_final st <> None.

lemma is_ke_sim_state_final (x : addr * exp * exp) :
  is_ke_sim_state_final (KESimStateFinal x).
proof. done. qed.

module KESim (Adv : FUNC) = {
  var self, adv : addr
  var st : ke_sim_state

  proc init(self_ adv_ : addr) : unit = {
    self <- self_; adv <- adv_;
    Adv.init(self, adv);
    st <- KESimStateWaitReq1;
  }

  proc loop(m : msg) : msg option = {
    var mod : mode; var pt1, pt2, pt1', pt2' : port; var u : univ;
    var addr, addr1, addr2 : addr; var n1: int;
    var q1, q2 : exp;
    var r : msg option <- None;
    var not_done : bool <- true;
    while (not_done) {
      (* m.`1 = Adv /\ m.`2.`1 = self *)
      if (m.`2.`2 = ke_sim_adv_pi) {  (* simulator *)
        r <- None;
        if (st = KESimStateWaitReq1) {
          if (is_ke_sim_req1 m) {
            (addr1, addr2, pt1', pt2') <- oget (dec_ke_sim_req1 m);
            q1 <$ dexp;
            r <-
              Some
              (Fwd1.fw_obs (addr1 ++ [1]) self (addr1, 3) (addr1, 4)
               (univ_triple (UnivPort pt1') (UnivPort pt2')
                (UnivBase (BaseKey (g ^ q1)))));
            st <- KESimStateWaitAdv1 (addr1, q1);
          }
        }
        elif (is_ke_sim_state_wait_req2 st) {
          (addr, q1, q2) <- oget (dec_ke_sim_state_wait_req2 st);
          if (is_ke_sim_req2 m) {
            (addr1, addr2) <- oget (dec_ke_sim_req2 m);
            r <-
              Some (Fwd2.fw_obs (addr ++ [2]) self (addr, 4) (addr, 3)
                    (UnivBase (BaseKey (g ^ q2))));
            st <- KESimStateWaitAdv2 (addr, q1, q2);
          }
        }
        if (r = None) {
          not_done <- false;
        }
        else {
          m <- oget r;
        }
      }
      else {  (* adversary *)
        r <@ Adv.invoke(m);
        not_done <- false;
        if (r <> None) {
          m <- oget r; (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
          if (mod = Dir \/ self <= addr1) {
            r <- None;
          }
          elif (is_ke_sim_state_wait_adv1 st) {
            (addr, q1) <- oget (dec_ke_sim_state_wait_adv1 st);
            if (addr <= addr1) {
              r <- None;
              if (Fwd1.is_fw_ok m) {
                (addr1, addr2) <- oget (Fwd1.dec_fw_ok m);
                if (addr1 = addr ++ [1]) {
                  q2 <$ dexp;
                  r <- Some (ke_sim_rsp addr self);
                  st <- KESimStateWaitReq2 (addr, q1, q2);
                }
              }
            }
          }
          elif (is_ke_sim_state_wait_adv2 st) {
            (addr, q1, q2) <- oget (dec_ke_sim_state_wait_adv2 st);
            if (addr <= addr1) {
              r <- None;
              if (Fwd2.is_fw_ok m) {
                (addr1, addr2) <- oget (Fwd2.dec_fw_ok m);
                if (addr1 = addr ++ [2]) {
                  r <- Some (ke_sim_rsp addr self);
                  st <- KESimStateFinal (addr, q1, q2);
                }
              }
            }
          }
          elif (is_ke_sim_state_wait_req2 st) {
            (addr, q1, q2) <- oget (dec_ke_sim_state_wait_req2 st);
            if (addr <= addr1) {
              r <- None;
            }
          }
        }
      }
    }
    return r;
  }

  proc invoke(m : msg) : msg option = {
    var mod : mode; var pt1, pt2 : port; var u : univ;
    var r : msg option <- None;
    (mod, pt1, pt2, u) <- m;
    if (mod = Adv /\ pt1.`1 = self) {
      r <- loop(m);
    }
    return r;
  }
}.

abstract theory RealSimp.

(* a simplified version of KEReal, not built using forwarders, so
   simpler to work with in proofs *)

type ke_real_simp_state = [
    KERealSimpStateWaitReq1
  | KERealSimpStateWaitAdv1 of (port * port * exp)
  | KERealSimpStateWaitReq2 of (port * port * exp * exp)
  | KERealSimpStateWaitAdv2 of (port * port * exp * exp)
  | KERealSimpStateFinal    of (port * port * exp * exp)
].

op dec_ke_real_simp_state_wait_adv1 (st : ke_real_simp_state) :
     (port * port * exp) option =
     with st = KERealSimpStateWaitReq1   => None
     with st = KERealSimpStateWaitAdv1 x => Some x
     with st = KERealSimpStateWaitReq2 _ => None
     with st = KERealSimpStateWaitAdv2 _ => None
     with st = KERealSimpStateFinal _    => None.

lemma enc_dec_ke_real_simp_state_wait_adv1 (x : port * port * exp) :
  dec_ke_real_simp_state_wait_adv1 (KERealSimpStateWaitAdv1 x) = Some x.
proof. done. qed.

op is_ke_real_simp_state_wait_adv1 (st : ke_real_simp_state) : bool =
  dec_ke_real_simp_state_wait_adv1 st <> None.

lemma is_ke_real_simp_state_wait_adv1 (x : port * port * exp) :
  is_ke_real_simp_state_wait_adv1 (KERealSimpStateWaitAdv1 x).
proof. done. qed.

op dec_ke_real_simp_state_wait_req2 (st : ke_real_simp_state) :
     (port * port * exp * exp) option =
     with st = KERealSimpStateWaitReq1   => None
     with st = KERealSimpStateWaitAdv1 _ => None
     with st = KERealSimpStateWaitReq2 x => Some x
     with st = KERealSimpStateWaitAdv2 _ => None
     with st = KERealSimpStateFinal _    => None.

lemma enc_dec_ke_real_simp_state_wait_req2 (x : port * port * exp * exp) :
  dec_ke_real_simp_state_wait_req2 (KERealSimpStateWaitReq2 x) = Some x.
proof. done. qed.

op is_ke_real_simp_state_wait_req2 (st : ke_real_simp_state) : bool =
  dec_ke_real_simp_state_wait_req2 st <> None.

lemma is_ke_real_simp_state_wait_req2 (x : port * port * exp * exp) :
  is_ke_real_simp_state_wait_req2 (KERealSimpStateWaitReq2 x).
proof. done. qed.

op dec_ke_real_simp_state_wait_adv2 (st : ke_real_simp_state) :
     (port * port * exp * exp) option =
     with st = KERealSimpStateWaitReq1   => None
     with st = KERealSimpStateWaitAdv1 _ => None
     with st = KERealSimpStateWaitReq2 _ => None
     with st = KERealSimpStateWaitAdv2 x => Some x
     with st = KERealSimpStateFinal _    => None.

lemma enc_dec_ke_real_simp_state_wait_adv2 (x : port * port * exp * exp) :
  dec_ke_real_simp_state_wait_adv2 (KERealSimpStateWaitAdv2 x) = Some x.
proof. done. qed.

op is_ke_real_simp_state_wait_adv2 (st : ke_real_simp_state) : bool =
  dec_ke_real_simp_state_wait_adv2 st <> None.

lemma is_ke_real_simp_state_wait_adv2 (x : port * port * exp * exp) :
  is_ke_real_simp_state_wait_adv2 (KERealSimpStateWaitAdv2 x).
proof. done. qed.

op dec_ke_real_simp_state_final (st : ke_real_simp_state) :
     (port * port * exp * exp) option =
     with st = KERealSimpStateWaitReq1   => None
     with st = KERealSimpStateWaitAdv1 _ => None
     with st = KERealSimpStateWaitReq2 _ => None
     with st = KERealSimpStateWaitAdv2 _ => None
     with st = KERealSimpStateFinal x    => Some x.

lemma enc_dec_ke_real_simp_state_final (x : port * port * exp * exp) :
  dec_ke_real_simp_state_final (KERealSimpStateFinal x) = Some x.
proof. done. qed.

op is_ke_real_simp_state_final (st : ke_real_simp_state) : bool =
  dec_ke_real_simp_state_final st <> None.

lemma is_ke_real_simp_state_final (x : port * port * exp * exp) :
  is_ke_real_simp_state_final (KERealSimpStateFinal x).
proof. done. qed.

module KERealSimp : FUNC = {
  var self, adv : addr
  var st : ke_real_simp_state

  proc init(self_ adv_ : addr) : unit = {
    self <- self_; adv <- adv_;
    st <- KERealSimpStateWaitReq1;
  }

  proc parties(m : msg) : msg option = {
    var pt1, pt2, pt1', pt2' : port; var addr, addr1, addr2 : addr;
    var u : univ; var q1, q2 : exp;
    var r : msg option <- None;
    if (st = KERealSimpStateWaitReq1) {
      if (is_ke_req1 m) {
        (* destination of m is (self, 1); mode of m is Dir *)
        (addr, pt1, pt2) <- oget (dec_ke_req1 m);
        if (! self <= pt1.`1 /\ ! self <= pt2.`1 /\
            ! adv <= pt1.`1 /\ ! adv <= pt2.`1) {
          q1 <$ dexp;
          u <-
            univ_triple (UnivPort pt1) (UnivPort pt2)
                        (UnivBase (BaseKey (g ^ q1)));
          r <- Some (Fwd1.fw_obs (self ++ [1]) adv (self, 3) (self, 4) u);
          st <- KERealSimpStateWaitAdv1 (pt1, pt2, q1);
        }
      }
    }
    elif (is_ke_real_simp_state_wait_adv1 st) {
      (pt1, pt2, q1) <- oget (dec_ke_real_simp_state_wait_adv1 st);
      if (Fwd1.is_fw_ok m) {
        (addr1, addr2) <- oget (Fwd1.dec_fw_ok m);
        if (addr1 = self ++ [1]) {
          (* destination of m is (self ++ [1], 1); mode of m is Adv *)
          q2 <$ dexp;
          r <- Some (ke_rsp1 self pt1 pt2 ((g ^ q1) ^ q2));
          st <- KERealSimpStateWaitReq2 (pt1, pt2, q1, q2);
        }
      }
    }
    elif (is_ke_real_simp_state_wait_req2 st) {
      (pt1, pt2, q1, q2) <- oget (dec_ke_real_simp_state_wait_req2 st);
      if (is_ke_req2 m) {
        (* destination of m is (self, 2); mode of m is Dir *)
        (addr, pt2') <- oget (dec_ke_req2 m);
        if (pt2' = pt2) {
          u <- UnivBase (BaseKey (g ^ q2));
          r <- Some (Fwd2.fw_obs (self ++ [2]) adv (self, 4) (self, 3) u);
          st <- KERealSimpStateWaitAdv2 (pt1, pt2, q1, q2);
        }
      }
    }
    elif (is_ke_real_simp_state_wait_adv2 st) {
      (pt1, pt2, q1, q2) <- oget (dec_ke_real_simp_state_wait_adv2 st);
      if (Fwd2.is_fw_ok m) {
        (addr1, addr2) <- oget (Fwd2.dec_fw_ok m);
        if (addr1 = self ++ [2]) {
          (* destination of m is (self ++ [2], 1); mode of m is Adv *)
          r <- Some (ke_rsp2 self pt1 ((g ^ q2) ^ q1));
          st <- KERealSimpStateFinal (pt1, pt2, q1, q2);
        }
      }
    }
    else {  (* st = KERealStateFinal *)
    }
    return r;
  }

  proc invoke(m : msg) : msg option = {
    var mod : mode; var pt1, pt2 : port; var u : univ;
    var addr1, addr2 : addr; var n1, n2 : int;
    var r : msg option <- None;
    (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
    if ((mod = Dir /\ addr1 = self /\ (n1 = 1 \/ n1 = 2)) \/
        (mod = Adv /\ (self ++ [1] <= addr1 \/ self ++ [2] <= addr1))) {
      r <- parties(m);
    }
    return r;
  }
}.

(* relational invariant for connecting KEReal and KERealSimp *)

type real_simp_rel_st = {
  real_simp_rel_st_func : addr;
  real_simp_rel_st_r1s  : ke_real_p1_state;
  real_simp_rel_st_r2s  : ke_real_p2_state;
  real_simp_rel_st_fws1 : Fwd1.fw_state;
  real_simp_rel_st_fws2 : Fwd2.fw_state;
  real_simp_rel_st_rss  : ke_real_simp_state;
}.

pred real_simp_rel0 (st : real_simp_rel_st) =
  (st.`real_simp_rel_st_r1s  = KERealP1StateWaitReq1) /\
  (st.`real_simp_rel_st_r2s  = KERealP2StateWaitFwd1) /\
  (st.`real_simp_rel_st_fws1 = Fwd1.FwStateInit) /\
  (st.`real_simp_rel_st_fws2 = Fwd2.FwStateInit) /\
  (st.`real_simp_rel_st_rss  = KERealSimpStateWaitReq1).

pred real_simp_rel1 (st : real_simp_rel_st, pt1 pt2 : port, q1 : exp) =
  ! (st.`real_simp_rel_st_func <= pt1.`1) /\
  ! (st.`real_simp_rel_st_func <= pt2.`1) /\
  (st.`real_simp_rel_st_r1s  = KERealP1StateWaitFwd2 (pt1, pt2, q1)) /\
  (st.`real_simp_rel_st_r2s  = KERealP2StateWaitFwd1) /\
  (st.`real_simp_rel_st_fws1 =
     Fwd1.FwStateWait
     ((st.`real_simp_rel_st_func, 3), (st.`real_simp_rel_st_func, 4),
      univ_triple (UnivPort pt1) (UnivPort pt2)
                  (UnivBase (BaseKey (g ^ q1))))) /\
  (st.`real_simp_rel_st_fws2 = Fwd2.FwStateInit) /\
  (st.`real_simp_rel_st_rss  = KERealSimpStateWaitAdv1 (pt1, pt2, q1)).

pred real_simp_rel2 (st : real_simp_rel_st, pt1 pt2 : port, q1 q2 : exp) =
  ! (st.`real_simp_rel_st_func <= pt1.`1) /\
  ! (st.`real_simp_rel_st_func <= pt2.`1) /\
  (st.`real_simp_rel_st_r1s  = KERealP1StateWaitFwd2 (pt1, pt2, q1)) /\
  (st.`real_simp_rel_st_r2s  = KERealP2StateWaitReq2 (pt1, pt2, q2)) /\
  (st.`real_simp_rel_st_fws1 =
     Fwd1.FwStateFinal
     ((st.`real_simp_rel_st_func, 3), (st.`real_simp_rel_st_func, 4),
      univ_triple (UnivPort pt1) (UnivPort pt2)
                  (UnivBase (BaseKey (g ^ q1))))) /\
  (st.`real_simp_rel_st_fws2 = Fwd2.FwStateInit) /\
  (st.`real_simp_rel_st_rss  = KERealSimpStateWaitReq2 (pt1, pt2, q1, q2)).

pred real_simp_rel3 (st : real_simp_rel_st, pt1 pt2 : port, q1 q2 : exp) =
  ! (st.`real_simp_rel_st_func <= pt1.`1) /\
  ! (st.`real_simp_rel_st_func <= pt2.`1) /\
  (st.`real_simp_rel_st_r1s  = KERealP1StateWaitFwd2 (pt1, pt2, q1)) /\
  (st.`real_simp_rel_st_r2s  = KERealP2StateFinal (pt1, pt2, q2)) /\
  (st.`real_simp_rel_st_fws1 =
     Fwd1.FwStateFinal
     ((st.`real_simp_rel_st_func, 3), (st.`real_simp_rel_st_func, 4),
      univ_triple (UnivPort pt1) (UnivPort pt2)
                  (UnivBase (BaseKey (g ^ q1))))) /\
  (st.`real_simp_rel_st_fws2 =
     Fwd2.FwStateWait
     ((st.`real_simp_rel_st_func, 4), (st.`real_simp_rel_st_func, 3),
      UnivBase (BaseKey (g ^ q2)))) /\
  (st.`real_simp_rel_st_rss  = KERealSimpStateWaitAdv2 (pt1, pt2, q1, q2)).

pred real_simp_rel4 (st : real_simp_rel_st, pt1 pt2 : port, q1 q2 : exp) =
  ! (st.`real_simp_rel_st_func <= pt1.`1) /\
  ! (st.`real_simp_rel_st_func <= pt2.`1) /\
  (st.`real_simp_rel_st_r1s  = KERealP1StateFinal (pt1, pt2, q1)) /\
  (st.`real_simp_rel_st_r2s  = KERealP2StateFinal (pt1, pt2, q2)) /\
  (st.`real_simp_rel_st_fws1 =
     Fwd1.FwStateFinal
     ((st.`real_simp_rel_st_func, 3), (st.`real_simp_rel_st_func, 4),
      univ_triple (UnivPort pt1) (UnivPort pt2)
                  (UnivBase (BaseKey (g ^ q1))))) /\
  (st.`real_simp_rel_st_fws2 =
     Fwd2.FwStateFinal
     ((st.`real_simp_rel_st_func, 4), (st.`real_simp_rel_st_func, 3),
      UnivBase (BaseKey (g ^ q2)))) /\
  (st.`real_simp_rel_st_rss  = KERealSimpStateFinal (pt1, pt2, q1, q2)).

inductive real_simp_rel (st : real_simp_rel_st) =
    RealSimpRel0 of (real_simp_rel0 st)
  | RealSimpRel1 (pt1 pt2 : port, q1 : exp) of
      (real_simp_rel1 st pt1 pt2 q1)
  | RealSimpRel2 (pt1 pt2 : port, q1 q2 : exp) of
      (real_simp_rel2 st pt1 pt2 q1 q2)
  | RealSimpRel3 (pt1 pt2 : port, q1 q2 : exp) of
      (real_simp_rel3 st pt1 pt2 q1 q2)
  | RealSimpRel4 (pt1 pt2 : port, q1 q2 : exp) of
      (real_simp_rel4 st pt1 pt2 q1 q2).

lemma KEReal_KERealSimp_invoke (func adv : addr) :
  equiv
  [KEReal.invoke ~ KERealSimp.invoke :
   ! func <= adv /\ ={m} /\
   KEReal.self{1} = func /\ KEReal.adv{1} = adv /\
   Fwd1.Forw.self{1} = func ++ [1] /\ Fwd1.Forw.adv{1} = adv /\
   Fwd2.Forw.self{1} = func ++ [2] /\ Fwd2.Forw.adv{1} = adv /\
   KERealSimp.self{2} = func /\ KERealSimp.adv{2} = adv /\
   real_simp_rel
   {|real_simp_rel_st_func = func;
     real_simp_rel_st_r1s  = KEReal.st1{1};
     real_simp_rel_st_r2s  = KEReal.st2{1};
     real_simp_rel_st_fws1 = Fwd1.Forw.st{1};
     real_simp_rel_st_fws2 = Fwd2.Forw.st{1};
     real_simp_rel_st_rss  = KERealSimp.st{2}|} ==>
   ={res} /\
   real_simp_rel
   {|real_simp_rel_st_func = func;
     real_simp_rel_st_r1s  = KEReal.st1{1};
     real_simp_rel_st_r2s  = KEReal.st2{1};
     real_simp_rel_st_fws1 = Fwd1.Forw.st{1};
     real_simp_rel_st_fws2 = Fwd2.Forw.st{1};
     real_simp_rel_st_rss  = KERealSimp.st{2}|}].
proof.
proc.
case
  (real_simp_rel0
   {|real_simp_rel_st_func = func;
     real_simp_rel_st_r1s  = KEReal.st1{1};
     real_simp_rel_st_r2s  = KEReal.st2{1};
     real_simp_rel_st_fws1 = Fwd1.Forw.st{1};
     real_simp_rel_st_fws2 = Fwd2.Forw.st{1};
     real_simp_rel_st_rss  = KERealSimp.st{2}|}).
(* case 0 *)
sp 3 3.
if => //.
case (mod{1} = Dir /\ addr1{1} = KEReal.self{1} /\ n1{1} = 1).
inline KEReal.loop KERealSimp.parties.
sp 3 2.
rcondt{1} 1; first auto.
rcondt{1} 1; first auto.
inline{1} (1) KEReal.party1.
sp.
rcondt{1} 1; first auto; smt().
rcondt{2} 1; first auto; smt().
if => //.
sp.
if; first move => &1 &2 |> <- |>.
seq 1 1 :
  (! KEReal.self{1} <= KEReal.adv{1} /\
   not_done{1} = true /\ ={q1, pt10, pt20} /\
  ! KEReal.self{1} <= pt10{1}.`1 /\ ! KEReal.self{1} <= pt20{1}.`1 /\
   KEReal.self{1} = func /\ KEReal.adv{1} = adv /\
   Fwd1.Forw.self{1} = func ++ [1] /\ Fwd1.Forw.adv{1} = adv /\
   Fwd2.Forw.self{1} = func ++ [2] /\ Fwd2.Forw.adv{1} = adv /\
   KERealSimp.self{2} = func /\ KERealSimp.adv{2} = adv /\
   real_simp_rel0
   {|real_simp_rel_st_func = func;
     real_simp_rel_st_r1s = KEReal.st1{1};
     real_simp_rel_st_r2s = KEReal.st2{1};
     real_simp_rel_st_fws1 = Fwd1.Forw.st{1};
     real_simp_rel_st_fws2 = Fwd2.Forw.st{1};
     real_simp_rel_st_rss = KERealSimp.st{2};|}).
auto; move => &1 &2 [#]; smt().
rcondf{1} 4.
auto; progress; rewrite oget_some /fw_req /= le_ext_r.
sp.
rcondt{1} 1; first auto.
rcondf{1} 1.
progress; auto; progress; by rewrite oget_some /fw_req /= ne_cat_nonnil_r.
rcondf{1} 1.
progress; auto; progress; by rewrite oget_some /fw_req /= ne_cat_nonnil_r.
rcondt{1} 1.
auto; progress; rewrite oget_some /fw_req /= le_refl.
inline Fwd1.Forw.invoke.
rcondt{1} 3; first auto; smt().
rcondt{1} 3; auto.
rcondt{1} 4.
auto; progress.
by rewrite oget_some Fwd1.enc_dec_fw_req oget_some.
rewrite oget_some Fwd1.enc_dec_fw_req oget_some /=.
by rewrite not_le_ext_nonnil_l.
rewrite oget_some Fwd1.enc_dec_fw_req oget_some /=.
by rewrite not_le_ext_nonnil_l.
rcondt{1} 7; first auto.
rcondf{1} 8; first auto.
auto; progress;
  first 3 by rewrite oget_some Fwd1.enc_dec_fw_req oget_some.
rewrite oget_some Fwd1.enc_dec_fw_req oget_some
        (RealSimpRel1 _ pt10{2} pt20{2} q1{2})
        /real_simp_rel1 /= /#.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto.
inline KEReal.loop KERealSimp.parties.
case (mod{1} = Dir /\ addr1{1} = KEReal.self{1} /\ n1{1} = 2).
sp 3 2.
rcondt{1} 1; first auto.
rcondf{1} 1; first auto.
rcondt{1} 1; first auto.
inline{1} (1) KEReal.party2.
sp.
rcondt{1} 1; first auto; smt().
rcondt{2} 1; first auto; smt().
rcondf{2} 1; first auto.
wp.
if{1}.
rcondf{1} 2; first auto; smt(Fwd1.dest_good_fw_rsp).
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
auto.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto.
sp 3 2.
rcondt{1} 1; auto.
rcondf{1} 1; first auto; smt(not_le_ext_nonnil_l).
rcondf{1} 1; first auto; smt(not_le_ext_nonnil_l).
rcondt{2} 1; first auto; smt().
rcondf{2} 1; first auto; progress; rewrite /is_ke_req1 /dec_ke_req1 /= /#.
seq 1 0 :
  (r0{1} = None /\ r0{2} = None /\
   KEReal.self{1} = func /\ KEReal.adv{1} = adv /\
   Fwd1.Forw.self{1} = func ++ [1] /\ Fwd1.Forw.adv{1} = adv /\
   Fwd2.Forw.self{1} = func ++ [2] /\ Fwd2.Forw.adv{1} = adv /\
   KERealSimp.self{2} = func /\ KERealSimp.adv{2} = adv /\
   real_simp_rel
   {|real_simp_rel_st_func = func;
     real_simp_rel_st_r1s = KEReal.st1{1};
     real_simp_rel_st_r2s = KEReal.st2{1};
     real_simp_rel_st_fws1 = Fwd1.Forw.st{1};
     real_simp_rel_st_fws2 = Fwd2.Forw.st{1};
     real_simp_rel_st_rss = KERealSimp.st{2};|}).
if{1}.
inline Fwd1.Forw.invoke.
rcondt{1} 3; first auto; smt().
rcondf{1} 3.
auto; progress; rewrite /Fwd1.is_fw_req /Fwd1.dec_fw_req /= /#.
auto.
inline Fwd2.Forw.invoke.
rcondt{1} 3; first auto; smt().
rcondf{1} 3.
auto; progress; rewrite /Fwd2.is_fw_req /Fwd2.dec_fw_req /= /#.
auto.
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
auto.
case
  (exists (pt1 pt2 : port, q1 : exp),
   real_simp_rel1
   {|real_simp_rel_st_func = func;
     real_simp_rel_st_r1s  = KEReal.st1{1};
     real_simp_rel_st_r2s  = KEReal.st2{1};
     real_simp_rel_st_fws1 = Fwd1.Forw.st{1};
     real_simp_rel_st_fws2 = Fwd2.Forw.st{1};
     real_simp_rel_st_rss  = KERealSimp.st{2}|}
   pt1 pt2 q1).
(* case 1 *)
elim* => pt1' pt2' q1'.
sp 3 3.
if => //.
inline KEReal.loop KERealSimp.parties; sp.
rcondt{1} 1; first auto.
case
  (mod{1} = Dir /\ addr1{1} = KEReal.self{1} /\
   (n1{1} = 1 \/ n1{1} = 2)).
seq 4 0 :
  (KEReal.self{1} = func /\ KEReal.adv{1} = adv /\
   Fwd1.Forw.self{1} = func ++ [1] /\ Fwd1.Forw.adv{1} = adv /\
   Fwd2.Forw.self{1} = func ++ [2] /\ Fwd2.Forw.adv{1} = adv /\
   KERealSimp.self{2} = func /\ KERealSimp.adv{2} = adv /\
   real_simp_rel1
   {|real_simp_rel_st_func = func;
     real_simp_rel_st_r1s = KEReal.st1{1};
     real_simp_rel_st_r2s = KEReal.st2{1};
     real_simp_rel_st_fws1 = Fwd1.Forw.st{1};
     real_simp_rel_st_fws2 = Fwd2.Forw.st{1};
     real_simp_rel_st_rss = KERealSimp.st{2};|}
   pt1' pt2' q1' /\
   ={m0} /\ m0{1} = (mod{1}, pt1{1}, pt2{1}, u{1}) /\
   mod{1} = Dir /\ pt1{1} = (addr1{1}, n1{1}) /\ (n1{1} = 1 \/ n1{1} = 2) /\
   r{1} = None /\ r0{2} = None).
if{1}.
inline{1} (1) KEReal.party1.
sp.
rcondf{1} 1; first auto; smt().
rcondt{1} 1; first auto; smt(is_ke_real_p1_state_wait_fwd2).
sp 1 0.
if{1}.
sp 1 0.
rcondf{1} 1; first auto => &hr />; smt(Fwd2.dest_good_fw_rsp).
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto.
if{1}.
inline{1} (1) KEReal.party2.
sp.
rcondt{1} 1; first auto; smt().
if{1}.
sp 1 0.
rcondf{1} 1; first auto => &hr />; smt(Fwd1.dest_good_fw_rsp).
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto.
rcondf{1} 1; first auto; smt().
exfalso; smt().
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_ke_real_simp_state_wait_adv1).
rcondf{2} 2; first auto.
auto; progress; by apply (RealSimpRel1 _ pt1' pt2' q1').
rcondf{1} 1; first auto; smt(ge_nonnil_ext_imp_ne).
rcondf{1} 1; first auto; smt(ge_nonnil_ext_imp_ne).
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_ke_real_simp_state_wait_adv1).
case (KEReal.self{1} ++ [1] = m0{1}.`2.`1 /\ Fwd1.is_fw_ok m0{1}).
rcondt{2} 2; first auto.
rcondt{2} 3; first auto; smt(Fwd1.dest_good_fw_ok).
rcondt{1} 1; first auto; smt(le_refl).
inline{1} (1) Fwd1.Forw.invoke.
rcondf{1} 3; first auto; smt().
rcondt{1} 3; first auto; smt(Fwd1.is_fw_state_wait).
rcondt{1} 4; first auto.
rcondt{1} 5; first auto; smt(Fwd1.dest_good_fw_ok).
rcondf{1} 8.
auto => |> &hr _ _ _ @/real_simp_rel1 /= [#]
        _ _ _ _ -> _ _ _ _ _.
rewrite oget_some /fw_rsp /= oget_some /= le_refl.
rcondt{1} 9; first auto.
rcondf{1} 9; first auto.
auto => |> &hr _ _ _ @/real_simp_rel1 /= [#] _ _ _ _ -> _ _ _ _ _.
by rewrite oget_some /fw_rsp /= oget_some.
rcondt{1} 9.
auto => |> &hr _ _ _ @/real_simp_rel1 /= [#] _ _ _ _ -> _ _ _ _ _.
by rewrite oget_some /fw_rsp /= oget_some.
sp 8 0; elim* => r0_L st_L.
inline{1} (1) KEReal.party2.
rcondt{1} 3; first auto; smt().
rcondt{1} 3; first auto.
rcondt{1} 4; first auto =>
  |> &hr dec_fw_st _ _ _ _ @/real_simp_rel1 /= [#]
  pt1'_nonloc pt2'_nonloc _ _ ->> _ _ _ _ _.
rewrite Fwd1.enc_dec_fw_state_wait oget_some /= in dec_fw_st.
rewrite oget_some Fwd1.enc_dec_fw_rsp oget_some /= /#.
rcondt{1} 12; first auto =>
  |> &hr dec_fw_st _ _ _ _ @/real_simp_rel1 /= [#]
  pt1'_nonloc pt2'_nonloc _ _ ->> _ _ _ _ _ q _.
rewrite /= oget_some /= in dec_fw_st.
rewrite oget_some /ke_rsp1 /= oget_some.
elim dec_fw_st => -> [#] -> ->.
by rewrite Fwd1.enc_dec_fw_rsp oget_some /= enc_dec_univ_triple
   oget_some.
rcondf{1} 13; first auto.
wp; sp; rnd.
auto => |> &1 &2 dec_simp_st _ dec_fw_rsp dec_tripl dec_fw_st dec_fw_ok
        _ _ _ @/real_simp_rel1 /= [#] pt1'_nonloc pt2'_nonloc _ _ ->> _ ->>
        _ _ _ q _.
rewrite enc_dec_ke_real_simp_state_wait_adv1 oget_some /= in dec_simp_st.
rewrite oget_some Fwd1.enc_dec_fw_rsp oget_some in dec_fw_rsp.
rewrite Fwd1.enc_dec_fw_state_wait oget_some /= in dec_fw_st.
elim dec_fw_st => ->> [#] ->> ->>.
rewrite /= in dec_fw_rsp.
elim dec_fw_rsp => ->> [#] ->> ->> ->>.
rewrite enc_dec_univ_triple oget_some /= in dec_tripl.
elim dec_tripl => ->> [#] ->> ->>.
elim dec_simp_st => ->> [#] ->> ->>.
split.
progress.
by rewrite oget_some enc_dec_base_key oget_some.
rewrite (RealSimpRel2 _ pt1' pt2' q1' q) /real_simp_rel2 /=.
progress.
seq 4 0 :
  (={m0} /\ r{1} = None /\ r0{2} = None /\
   ! (KEReal.self{1} ++ [1] = m0{1}.`2.`1 /\ Fwd1.is_fw_ok m0{1}) /\
   (KEReal.self{1} ++ [1] <= addr1{1} \/ KEReal.self{1} ++ [2] <= addr1{1}) /\
   KEReal.self{1} = func /\ KEReal.adv{1} = adv /\
   Fwd1.Forw.self{1} = func ++ [1] /\ Fwd1.Forw.adv{1} = adv /\
   Fwd2.Forw.self{1} = func ++ [2] /\ Fwd2.Forw.adv{1} = adv /\
   KERealSimp.self{2} = func /\ KERealSimp.adv{2} = adv /\
   real_simp_rel1
   {|real_simp_rel_st_func = func;
     real_simp_rel_st_r1s = KEReal.st1{1};
     real_simp_rel_st_r2s = KEReal.st2{1};
     real_simp_rel_st_fws1 = Fwd1.Forw.st{1};
     real_simp_rel_st_fws2 = Fwd2.Forw.st{1};
     real_simp_rel_st_rss = KERealSimp.st{2};|}
   pt1' pt2' q1').
if{1}.
inline{1} (1) Fwd1.Forw.invoke.
rcondf{1} 3; first auto; smt().
rcondt{1} 3; first auto; smt(Fwd1.is_fw_state_wait).
sp 3 0.
if{1}.
rcondf{1} 2; first auto; progress.
smt(Fwd1.dest_good_fw_ok).
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
auto; smt().
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto; smt().
inline{1} (1) Fwd2.Forw.invoke.
rcondt{1} 3; first auto; smt().
sp 2 0.
if{1}.
rcondf{1} 2; first auto; smt(Fwd2.dest_good_fw_req).
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
auto; smt().
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto; smt().
sp 0 1.
if{2}.
rcondf{2} 2; first auto; progress.
smt(Fwd1.dest_good_fw_ok).
trivial.
auto; progress; by apply (RealSimpRel1 _ pt1' pt2' q1').
auto; progress; by apply (RealSimpRel1 _ pt1' pt2' q1').
case
  (exists (pt1 pt2 : port, q1 q2 : exp),
   real_simp_rel2
   {|real_simp_rel_st_func = func;
     real_simp_rel_st_r1s  = KEReal.st1{1};
     real_simp_rel_st_r2s  = KEReal.st2{1};
     real_simp_rel_st_fws1 = Fwd1.Forw.st{1};
     real_simp_rel_st_fws2 = Fwd2.Forw.st{1};
     real_simp_rel_st_rss  = KERealSimp.st{2}|}
   pt1 pt2 q1 q2).
(* case 2 *)
elim* => pt1' pt2' q1' q2'.
sp 3 3.
if => //.
case (mod{1} = Dir /\ addr1{1} = KEReal.self{1} /\ n1{1} = 1).
inline KEReal.loop KERealSimp.parties.
sp 3 2.
rcondt{1} 1; first auto.
rcondt{1} 1; first auto.
inline KEReal.party1.
rcondf{1} 3; first auto; smt().
rcondt{1} 3; first auto; smt(is_ke_real_p1_state_wait_fwd2).
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_ke_real_simp_state_wait_req2).
rcondf{2} 2; first auto.
wp; sp 3 0.
if{1}.
sp 1 0.
rcondf{1} 1; first auto; progress.
have /# :=
  Fwd2.dest_good_fw_rsp (Dir, (KEReal.self{hr}, 1), pt2{m}, u{m}).
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto.
case (mod{1} = Dir /\ addr1{1} = KEReal.self{1} /\ n1{1} = 2).
inline KEReal.loop KERealSimp.parties.
sp 3 2.
rcondt{1} 1; first auto.
rcondf{1} 1; first auto.
rcondt{1} 1; first auto.
inline{1} (1) KEReal.party2.
sp.
rcondf{1} 1; first auto; smt().
rcondt{1} 1; first auto; smt(is_ke_real_p2_state_wait_req2).
sp 1 0.
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_ke_real_simp_state_wait_req2).
sp 0 1.
if => //.
sp 1 1.
if.
move =>
  &1 &2 [#] dec_req2_0 dec_req2_1 dec_simp_st dec_real2_st
  ->> _ ->> _ ->> _ _ _ m2_eq _ _ m1_eq _ _ ->>.
rewrite -dec_req2_0 /= in dec_req2_1.
rewrite -m2_eq /= in m1_eq.
smt().
wp.
rcondf{1} 4; first auto; progress; rewrite oget_some /fw_req /= le_ext_r.
sp.
rcondt{1} 1; first auto.
rcondf{1} 1; first auto.
progress; by rewrite oget_some /fw_req /= ne_cat_nonnil_r.
rcondf{1} 1; first auto.
rcondf{1} 1; first auto; progress.
by rewrite oget_some /fw_req /= le_ext_comm sing_not_le.
inline{1} (1) Fwd2.Forw.invoke.
rcondt{1} 3; first auto; smt().
rcondt{1} 3; first auto.
sp 3 0.
rcondt{1} 1; first auto => /> &hr.
rewrite oget_some Fwd2.enc_dec_fw_req oget_some /=.
progress; by rewrite not_le_ext_nonnil_l.
rcondt{1} 4; auto.
rcondf{1} 5; first auto.
auto => /> &1 &2.
rewrite !oget_some Fwd2.enc_dec_fw_req oget_some /=.
progress.
rewrite (RealSimpRel3 _ pt10{2} pt20{2} q1{2} q2{2})
        /real_simp_rel3 /= /#.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto.
inline KEReal.loop KERealSimp.parties.
sp 3 2.
rcondt{1} 1; auto.
rcondf{1} 1; first auto; smt(not_le_ext_nonnil_l).
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_ke_real_simp_state_wait_req2).
rcondf{2} 2; first auto; progress; rewrite /is_ke_req2 /dec_ke_req2 /= /#.
seq 1 0 :
  (r0{1} = None /\ r0{2} = None /\
   KEReal.self{1} = func /\ KEReal.adv{1} = adv /\
   Fwd1.Forw.self{1} = func ++ [1] /\ Fwd1.Forw.adv{1} = adv /\
   Fwd2.Forw.self{1} = func ++ [2] /\ Fwd2.Forw.adv{1} = adv /\
   KERealSimp.self{2} = func /\ KERealSimp.adv{2} = adv /\
   real_simp_rel2
   {|real_simp_rel_st_func = func;
     real_simp_rel_st_r1s = KEReal.st1{1};
     real_simp_rel_st_r2s = KEReal.st2{1};
     real_simp_rel_st_fws1 = Fwd1.Forw.st{1};
     real_simp_rel_st_fws2 = Fwd2.Forw.st{1};
     real_simp_rel_st_rss = KERealSimp.st{2}; |}
   pt1' pt2' q1' q2').
rcondf{1} 1; first auto; smt(not_le_ext_nonnil_l).
if{1}.
inline Fwd1.Forw.invoke.
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
auto.
inline Fwd2.Forw.invoke.
rcondt{1} 3; first auto; smt().
rcondf{1} 3.
auto; progress; rewrite /Fwd2.is_fw_req /Fwd2.dec_fw_req /= /#.
auto.
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
auto; progress; by rewrite (RealSimpRel2 _ pt1' pt2' q1' q2').
case
  (exists (pt1 pt2 : port, q1 q2 : exp),
   real_simp_rel3
   {|real_simp_rel_st_func = func;
     real_simp_rel_st_r1s  = KEReal.st1{1};
     real_simp_rel_st_r2s  = KEReal.st2{1};
     real_simp_rel_st_fws1 = Fwd1.Forw.st{1};
     real_simp_rel_st_fws2 = Fwd2.Forw.st{1};
     real_simp_rel_st_rss  = KERealSimp.st{2}|}
   pt1 pt2 q1 q2).
(* case 3 *)
elim* => pt1' pt2' q1' q2'.
sp 3 3.
if => //.
inline KEReal.loop KERealSimp.parties; sp.
rcondt{1} 1; first auto.
case
  (mod{1} = Dir /\ addr1{1} = KEReal.self{1} /\
   (n1{1} = 1 \/ n1{1} = 2)).
seq 4 0 :
  (KEReal.self{1} = func /\ KEReal.adv{1} = adv /\
   Fwd1.Forw.self{1} = func ++ [1] /\ Fwd1.Forw.adv{1} = adv /\
   Fwd2.Forw.self{1} = func ++ [2] /\ Fwd2.Forw.adv{1} = adv /\
   KERealSimp.self{2} = func /\ KERealSimp.adv{2} = adv /\
   real_simp_rel3
   {|real_simp_rel_st_func = func;
     real_simp_rel_st_r1s = KEReal.st1{1};
     real_simp_rel_st_r2s = KEReal.st2{1};
     real_simp_rel_st_fws1 = Fwd1.Forw.st{1};
     real_simp_rel_st_fws2 = Fwd2.Forw.st{1};
     real_simp_rel_st_rss = KERealSimp.st{2};|}
   pt1' pt2' q1' q2' /\
   ={m0} /\ m0{1} = (mod{1}, pt1{1}, pt2{1}, u{1}) /\
   mod{1} = Dir /\ pt1{1} = (addr1{1}, n1{1}) /\ (n1{1} = 1 \/ n1{1} = 2) /\
   r{1} = None /\ r0{2} = None).
if{1}.
inline{1} (1) KEReal.party1.
rcondf{1} 3; first auto; smt().
rcondt{1} 3; first auto; smt(is_ke_real_p1_state_wait_fwd2).
sp 3 0.
if{1}.
rcondf{1} 2; first auto; smt(Fwd2.dest_good_fw_rsp).
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
auto.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto.
if{1}.
inline{1} (1) KEReal.party2.
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondt{1} 4; first auto.
rcondf{1} 5; first auto.
auto.
rcondf{1} 1; first auto; smt().
exfalso; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_ke_real_simp_state_wait_adv2).
rcondf{2} 2; first auto.
auto; progress; by apply (RealSimpRel3 _ pt1' pt2' q1' q2').
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_ke_real_simp_state_wait_adv2).
rcondf{1} 1; first auto; smt(ge_nonnil_ext_imp_ne).
rcondf{1} 1; first auto; smt(not_le_ext_nonnil_l).
case (KEReal.self{1} ++ [2] = m0{1}.`2.`1 /\ Fwd2.is_fw_ok m0{1}).
rcondt{2} 2; first auto.
rcondt{2} 3; first auto; smt(Fwd2.dest_good_fw_ok).
rcondf{1} 1; first auto; progress; by rewrite le_ext_comm sing_not_le.
inline{1} (1) Fwd2.Forw.invoke.
rcondf{1} 3; first auto; smt().
rcondt{1} 3; first auto; smt(Fwd2.is_fw_state_wait).
rcondt{1} 4; first auto.
rcondt{1} 5; first auto; smt(Fwd2.dest_good_fw_ok).
rcondf{1} 8.
auto => |> &hr _ _ _ _ _ @/real_simp_rel3 /= [#]
        _ _ _ _ _ -> _ _ _ _.
rewrite oget_some /fw_rsp /= oget_some /= le_refl.
rcondt{1} 9; first auto.
rcondt{1} 9.
auto => |> &hr _ _ _ _ _ @/real_simp_rel3 /= [#] _ _ _ _ _ -> _ _ _ _.
by rewrite oget_some /fw_rsp /= oget_some.
sp 8 0; elim* => r0_L st_L.
inline{1} (1) KEReal.party1.
rcondf{1} 3; first auto; smt().
rcondt{1} 3; first auto; smt(is_ke_real_p1_state_wait_fwd2).
rcondt{1} 4; first auto.
rcondt{1} 5.
auto; progress; rewrite oget_some Fwd2.enc_dec_fw_rsp oget_some /= /#.
rcondt{1} 9; first auto =>
  |> &hr _ _ _ _ _ _ _ @/real_simp_rel3 /= [#]
  _ _ -> _ _ ->> _ _ _ _.
by rewrite oget_some /ke_rsp2 /= oget_some /=.
rcondf{1} 10; first auto.
auto =>
  |> &1 &2 dec_fw_st _ _ _ _ _ _ @/real_simp_rel3 /= [#]
  _ _ -> _ _ ->> -> _ _ _ /=.
rewrite oget_some /= oget_some Fwd2.enc_dec_fw_rsp oget_some /=.
rewrite /= oget_some /= in dec_fw_st.
elim dec_fw_st => -> [#] -> -> /=.
rewrite oget_some /= oget_some.
split => //.
by rewrite (RealSimpRel4 _ pt1' pt2' q1' q2').
seq 4 0 :
  (={m0} /\ r{1} = None /\ r0{2} = None /\
   ! (KEReal.self{1} ++ [2] = m0{1}.`2.`1 /\ Fwd2.is_fw_ok m0{1}) /\
   (KEReal.self{1} ++ [1] <= addr1{1} \/ KEReal.self{1} ++ [2] <= addr1{1}) /\
   KEReal.self{1} = func /\ KEReal.adv{1} = adv /\
   Fwd1.Forw.self{1} = func ++ [1] /\ Fwd1.Forw.adv{1} = adv /\
   Fwd2.Forw.self{1} = func ++ [2] /\ Fwd2.Forw.adv{1} = adv /\
   KERealSimp.self{2} = func /\ KERealSimp.adv{2} = adv /\
   real_simp_rel3
   {|real_simp_rel_st_func = func;
     real_simp_rel_st_r1s = KEReal.st1{1};
     real_simp_rel_st_r2s = KEReal.st2{1};
     real_simp_rel_st_fws1 = Fwd1.Forw.st{1};
     real_simp_rel_st_fws2 = Fwd2.Forw.st{1};
     real_simp_rel_st_rss = KERealSimp.st{2};|}
   pt1' pt2' q1' q2').
if{1}.
inline{1} (1) Fwd1.Forw.invoke.
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondt{1} 4; first auto.
rcondf{1} 5; first auto.
auto; smt().
inline{1} (1) Fwd2.Forw.invoke.
rcondf{1} 3; first auto; smt().
rcondt{1} 3; first auto; smt(Fwd2.is_fw_state_wait).
sp 3 0.
if{1}.
rcondf{1} 2; first auto; progress.
smt(Fwd2.dest_good_fw_ok).
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
auto; smt().
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto; smt().
sp 0 1.
if{2}.
rcondf{2} 2; first auto; smt(Fwd2.dest_good_fw_ok).
auto; progress; by apply (RealSimpRel3 _ pt1' pt2' q1' q2').
auto; progress; by apply (RealSimpRel3 _ pt1' pt2' q1' q2').
case
  (exists (pt1 pt2 : port, q1 q2 : exp),
   real_simp_rel4
   {|real_simp_rel_st_func = func;
     real_simp_rel_st_r1s  = KEReal.st1{1};
     real_simp_rel_st_r2s  = KEReal.st2{1};
     real_simp_rel_st_fws1 = Fwd1.Forw.st{1};
     real_simp_rel_st_fws2 = Fwd2.Forw.st{1};
     real_simp_rel_st_rss  = KERealSimp.st{2}|}
   pt1 pt2 q1 q2).
(* case 4 *)
elim* => pt1' pt2' q1' q2'.
sp 3 3.
if => //.
seq 1 0 :
  (={m} /\ r{1} = None /\
   KEReal.self{1} = func /\ KEReal.adv{1} = adv /\
   Fwd1.Forw.self{1} = func ++ [1] /\ Fwd1.Forw.adv{1} = adv /\
   Fwd2.Forw.self{1} = func ++ [2] /\ Fwd2.Forw.adv{1} = adv /\
   KERealSimp.self{2} = func /\ KERealSimp.adv{2} = adv /\
   real_simp_rel4
   {|real_simp_rel_st_func = func;
     real_simp_rel_st_r1s = KEReal.st1{1};
     real_simp_rel_st_r2s = KEReal.st2{1};
     real_simp_rel_st_fws1 = Fwd1.Forw.st{1};
     real_simp_rel_st_fws2 = Fwd2.Forw.st{1};
     real_simp_rel_st_rss = KERealSimp.st{2};|}
   pt1' pt2' q1' q2').
inline KEReal.loop.
rcondt{1} 4; first auto.
sp.
if{1}.
inline KEReal.party1.
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
auto.
rcondt{1} 4; first auto.
rcondf{1} 5; first auto.
auto.
if{1}.
inline KEReal.party2.
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
auto.
rcondt{1} 4; first auto.
rcondf{1} 5; first auto.
auto.
if{1}.
inline{1} (1) Fwd1.Forw.invoke.
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondt{1} 4; first auto.
rcondf{1} 5; first auto.
auto.
inline{1} (1) Fwd2.Forw.invoke.
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondt{1} 4; first auto.
rcondf{1} 5; first auto.
auto.
inline{2} KERealSimp.parties.
rcondf{2} 3; first auto; smt().
rcondf{2} 3; first auto; smt().
rcondf{2} 3; first auto; smt().
rcondf{2} 3; first auto; smt().
auto; progress; by apply (RealSimpRel4 _ pt1' pt2' q1' q2').
(* no more cases *)
exfalso => &1 &2 [#] _ _ _ _ _ _ _ _ _ _ []; smt().
qed.

lemma Exper_KEReal_KERealSimp
      (func' adv' : addr) (in_guard' : int fset) &m
      (Adv <: FUNC{MI, KEReal, KERealSimp})
      (Env <: ENV{MI, KEReal, KERealSimp, Adv}) :
  ! func' <= adv' =>
  Pr[Exper(MI(KEReal, Adv), Env).main
       (func', adv', in_guard') @ &m : res] =
  Pr[Exper(MI(KERealSimp, Adv), Env).main
       (func', adv', in_guard') @ &m : res].
proof.
move => pre.
byequiv => //; proc; inline*.
seq 23 12 :
  (! func' <= adv' /\ ={func, adv, in_guard, glob Adv, glob MI} /\
   func{1} = func' /\ adv{1} = adv' /\ in_guard{1} = in_guard' /\
   MI.func{1} = func' /\ MI.adv{1} = adv' /\ MI.in_guard{1} = in_guard' /\
   KEReal.self{1} = func' /\ KEReal.adv{1} = adv' /\
   Fwd1.Forw.self{1} = func' ++ [1] /\ Fwd1.Forw.adv{1} = adv' /\
   Fwd2.Forw.self{1} = func' ++ [2] /\ Fwd2.Forw.adv{1} = adv' /\
   KERealSimp.self{2} = func' /\ KERealSimp.adv{2} = adv' /\
   real_simp_rel
   {|real_simp_rel_st_func = func';
     real_simp_rel_st_r1s  = KEReal.st1{1};
     real_simp_rel_st_r2s  = KEReal.st2{1};
     real_simp_rel_st_fws1 = Fwd1.Forw.st{1};
     real_simp_rel_st_fws2 = Fwd2.Forw.st{1};
     real_simp_rel_st_rss  = KERealSimp.st{2}|}).
call (_ : true).
auto; progress; by rewrite RealSimpRel0 /real_simp_rel0.
call
  (_ :
   ! func' <= adv' /\ ={glob Adv, glob MI} /\
   MI.func{1} = func' /\ MI.adv{1} = adv' /\ MI.in_guard{1} = in_guard' /\
   KEReal.self{1} = func' /\ KEReal.adv{1} = adv' /\
   Fwd1.Forw.self{1} = func' ++ [1] /\ Fwd1.Forw.adv{1} = adv' /\
   Fwd2.Forw.self{1} = func' ++ [2] /\ Fwd2.Forw.adv{1} = adv' /\
   KERealSimp.self{2} = func' /\ KERealSimp.adv{2} = adv' /\
   real_simp_rel
   {|real_simp_rel_st_func = func';
     real_simp_rel_st_r1s  = KEReal.st1{1};
     real_simp_rel_st_r2s  = KEReal.st2{1};
     real_simp_rel_st_fws1 = Fwd1.Forw.st{1};
     real_simp_rel_st_fws2 = Fwd2.Forw.st{1};
     real_simp_rel_st_rss  = KERealSimp.st{2}|}).
proc.
sp 2 2.
if => //.
inline MI(KEReal, Adv).loop MI(KERealSimp, Adv).loop.
wp; sp.
while
  (={not_done, m0, r0} /\ 
   ! func' <= adv' /\ ={glob Adv, glob MI} /\
   MI.func{1} = func' /\ MI.adv{1} = adv' /\ MI.in_guard{1} = in_guard' /\
   KEReal.self{1} = func' /\ KEReal.adv{1} = adv' /\
   Fwd1.Forw.self{1} = func' ++ [1] /\ Fwd1.Forw.adv{1} = adv' /\
   Fwd2.Forw.self{1} = func' ++ [2] /\ Fwd2.Forw.adv{1} = adv' /\
   KERealSimp.self{2} = func' /\ KERealSimp.adv{2} = adv' /\
   real_simp_rel
   {|real_simp_rel_st_func = func';
     real_simp_rel_st_r1s  = KEReal.st1{1};
     real_simp_rel_st_r2s  = KEReal.st2{1};
     real_simp_rel_st_fws1 = Fwd1.Forw.st{1};
     real_simp_rel_st_fws2 = Fwd2.Forw.st{1};
     real_simp_rel_st_rss  = KERealSimp.st{2}|}).
sp 2 2.
if => //.
wp; call (KEReal_KERealSimp_invoke func' adv'); auto.
wp; call (_ : true); auto.
auto.
auto.
auto.
qed.

end RealSimp.

type ke_ddh_state = [
    KEDDHStateWaitReq1
  | KEDDHStateWaitAdv1 of (port * port)
  | KEDDHStateWaitReq2 of (port * port)
  | KEDDHStateWaitAdv2 of (port * port)
  | KEDDHStateFinal    of (port * port)
].

op dec_ke_ddh_state_wait_adv1 (st : ke_ddh_state) :
     (port * port) option =
     with st = KEDDHStateWaitReq1   => None
     with st = KEDDHStateWaitAdv1 x => Some x
     with st = KEDDHStateWaitReq2 _ => None
     with st = KEDDHStateWaitAdv2 _ => None
     with st = KEDDHStateFinal _    => None.

lemma enc_dec_ke_ddh_state_wait_adv1 (x : port * port) :
  dec_ke_ddh_state_wait_adv1 (KEDDHStateWaitAdv1 x) = Some x.
proof. done. qed.

op is_ke_ddh_state_wait_adv1 (st : ke_ddh_state) : bool =
  dec_ke_ddh_state_wait_adv1 st <> None.

lemma is_ke_ddh_state_wait_adv1 (x : port * port) :
  is_ke_ddh_state_wait_adv1 (KEDDHStateWaitAdv1 x).
proof. done. qed.

op dec_ke_ddh_state_wait_req2 (st : ke_ddh_state) :
     (port * port) option =
     with st = KEDDHStateWaitReq1   => None
     with st = KEDDHStateWaitAdv1 _ => None
     with st = KEDDHStateWaitReq2 x => Some x
     with st = KEDDHStateWaitAdv2 _ => None
     with st = KEDDHStateFinal _    => None.

lemma enc_dec_ke_ddh_state_wait_req2 (x : port * port) :
  dec_ke_ddh_state_wait_req2 (KEDDHStateWaitReq2 x) = Some x.
proof. done. qed.

op is_ke_ddh_state_wait_req2 (st : ke_ddh_state) : bool =
  dec_ke_ddh_state_wait_req2 st <> None.

lemma is_ke_ddh_state_wait_req2 (x : port * port) :
  is_ke_ddh_state_wait_req2 (KEDDHStateWaitReq2 x).
proof. done. qed.

op dec_ke_ddh_state_wait_adv2 (st : ke_ddh_state) :
     (port * port) option =
     with st = KEDDHStateWaitReq1   => None
     with st = KEDDHStateWaitAdv1 _ => None
     with st = KEDDHStateWaitReq2 _ => None
     with st = KEDDHStateWaitAdv2 x => Some x
     with st = KEDDHStateFinal _    => None.

lemma enc_dec_ke_ddh_state_wait_adv2 (x : port * port) :
  dec_ke_ddh_state_wait_adv2 (KEDDHStateWaitAdv2 x) = Some x.
proof. done. qed.

op is_ke_ddh_state_wait_adv2 (st : ke_ddh_state) : bool =
  dec_ke_ddh_state_wait_adv2 st <> None.

lemma is_ke_ddh_state_wait_adv2 (x : port * port) :
  is_ke_ddh_state_wait_adv2 (KEDDHStateWaitAdv2 x).
proof. done. qed.

op dec_ke_ddh_state_final (st : ke_ddh_state) :
     (port * port) option =
     with st = KEDDHStateWaitReq1   => None
     with st = KEDDHStateWaitAdv1 _ => None
     with st = KEDDHStateWaitReq2 _ => None
     with st = KEDDHStateWaitAdv2 _ => None
     with st = KEDDHStateFinal x    => Some x.

lemma enc_dec_ke_ddh_state_wait_final (x : port * port) :
  dec_ke_ddh_state_final (KEDDHStateFinal x) = Some x.
proof. done. qed.

op is_ke_ddh_state_final (st : ke_ddh_state) : bool =
  dec_ke_ddh_state_final st <> None.

lemma is_ke_ddh_state_final (x : port * port) :
  is_ke_ddh_state_final (KEDDHStateFinal x).
proof. done. qed.

module DDH_Adv (Env : ENV, Adv : FUNC) : DDH_ADV = {
  var func, adv : addr
  var x1, x2, x3 : key

  module KEDDH : FUNC = {
    var self, adv : addr
    var st : ke_ddh_state

    proc init(self_ adv_ : addr) : unit = {
      self <- self_; adv <- adv_;
      st <- KEDDHStateWaitReq1;
    }

    proc parties(m : msg) : msg option = {
      var pt1, pt2, pt1', pt2' : port; var addr, addr1, addr2 : addr;
      var u : univ; var q1, q2 : exp;
      var r : msg option <- None;
      if (st = KEDDHStateWaitReq1) {
        if (is_ke_req1 m) {
          (* destination of m is (self, 1); mode of m is Dir *)
          (addr, pt1, pt2) <- oget (dec_ke_req1 m);
          if (! self <= pt1.`1 /\ ! self <= pt2.`1 /\
              ! adv <= pt1.`1 /\ ! adv <= pt2.`1) {
            u <-
              univ_triple (UnivPort pt1) (UnivPort pt2)
                          (UnivBase (BaseKey x1));
            r <- Some (Fwd1.fw_obs (self ++ [1]) adv (self, 3) (self, 4) u);
            st <- KEDDHStateWaitAdv1 (pt1, pt2);
          }
        }
      }
      elif (is_ke_ddh_state_wait_adv1 st) {
        (pt1, pt2) <- oget (dec_ke_ddh_state_wait_adv1 st);
        if (Fwd1.is_fw_ok m) {
          (addr1, addr2) <- oget (Fwd1.dec_fw_ok m);
          if (addr1 = self ++ [1]) {
            (* destination of m is (self ++ [1], 1); mode of m is Adv *)
            r <- Some (ke_rsp1 self pt1 pt2 x3);
            st <- KEDDHStateWaitReq2 (pt1, pt2);
          }
        }
      }
      elif (is_ke_ddh_state_wait_req2 st) {
        (pt1, pt2) <- oget (dec_ke_ddh_state_wait_req2 st);
        if (is_ke_req2 m) {
          (* destination of m is (self, 2); mode of m is Dir *)
          (addr, pt2') <- oget (dec_ke_req2 m);
          if (pt2' = pt2) {
            u <- UnivBase (BaseKey x2);
            r <- Some (Fwd2.fw_obs (self ++ [2]) adv (self, 4) (self, 3) u);
            st <- KEDDHStateWaitAdv2 (pt1, pt2);
          }
        }
      }
      elif (is_ke_ddh_state_wait_adv2 st) {
        (pt1, pt2) <- oget (dec_ke_ddh_state_wait_adv2 st);
        if (Fwd2.is_fw_ok m) {
          (addr1, addr2) <- oget (Fwd2.dec_fw_ok m);
          if (addr1 = self ++ [2]) {
            (* destination of m is (self ++ [2], 1); mode of m is Adv *)
            r <- Some (ke_rsp2 self pt1 x3);
            st <- KEDDHStateFinal (pt1, pt2);
          }
        }
      }
      else {  (* st = KEDDHStateFinal *)
      }
      return r;
    }

    proc invoke(m : msg) : msg option = {
      var mod : mode; var pt1, pt2 : port; var u : univ;
      var addr1, addr2 : addr; var n1, n2 : int;
      var r : msg option <- None;
      (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
      if ((mod = Dir /\ addr1 = self /\ (n1 = 1 \/ n1 = 2)) \/
          (mod = Adv /\ (self ++ [1] <= addr1 \/ self ++ [2] <= addr1))) {
        r <- parties(m);
      }
      return r;
    }
  }

  proc main(x1_ x2_ x3_ : key) : bool = {
    var b : bool;
    x1 <- x1_; x2 <- x2_; x3 <- x3_;
    b <@ Exper(MI(KEDDH, Adv), Env).main(func, adv, fset1 adv_fw_pi);
    return b;
  }
}.

section.

declare module Adv : FUNC{MI, KEReal, KEIdeal, KESim, DDH_Adv}.
declare module Env : ENV{Adv, MI, KEReal, KEIdeal, KESim, DDH_Adv}.

local clone import RealSimp as RS
proof *.

type exp_names = [exp1 | exp2 | exp3].

local clone RedundantHashing as RH with
  type input <- exp_names,
  type output <- exp,
  op doutput <- dexp
proof *.
realize doutput_ll. apply dexp_ll. qed.

local module (KERealSimpHashingAdv : RH.HASHING_ADV)
             (Hash : RH.HASHING) = {
  module KERealSimpHash : FUNC = {
    var self, adv : addr
    var st : ke_real_simp_state

    proc init(self_ adv_ : addr) : unit = {
      self <- self_; adv <- adv_;
      st <- KERealSimpStateWaitReq1;
    }

    proc parties(m : msg) : msg option = {
      var pt1, pt2, pt1', pt2' : port; var addr, addr1, addr2 : addr;
      var u : univ; var q1, q2 : exp;
      var r : msg option <- None;
      if (st = KERealSimpStateWaitReq1) {
        if (is_ke_req1 m) {
          (* destination of m is (self, 1); mode of m is Dir *)
          (addr, pt1, pt2) <- oget (dec_ke_req1 m);
          if (! self <= pt1.`1 /\ ! self <= pt2.`1 /\
              ! adv <= pt1.`1 /\ ! adv <= pt2.`1) {
            q1 <@ Hash.hash(exp1);
            u <-
              univ_triple (UnivPort pt1) (UnivPort pt2)
                          (UnivBase (BaseKey (g ^ q1)));
            r <- Some (Fwd1.fw_obs (self ++ [1]) adv (self, 3) (self, 4) u);
            st <- KERealSimpStateWaitAdv1 (pt1, pt2, q1);
          }
        }
      }
      elif (is_ke_real_simp_state_wait_adv1 st) {
        (pt1, pt2, q1) <- oget (dec_ke_real_simp_state_wait_adv1 st);
        if (Fwd1.is_fw_ok m) {
          (addr1, addr2) <- oget (Fwd1.dec_fw_ok m);
          if (addr1 = self ++ [1]) {
            (* destination of m is (self ++ [1], 1); mode of m is Adv *)
            q2 <@ Hash.hash(exp2);
            r <- Some (ke_rsp1 self pt1 pt2 ((g ^ q1) ^ q2));
            st <- KERealSimpStateWaitReq2 (pt1, pt2, q1, q2);
          }
        }
      }
      elif (is_ke_real_simp_state_wait_req2 st) {
        (pt1, pt2, q1, q2) <- oget (dec_ke_real_simp_state_wait_req2 st);
        if (is_ke_req2 m) {
          (* destination of m is (self, 2); mode of m is Dir *)
          (addr, pt2') <- oget (dec_ke_req2 m);
          if (pt2' = pt2) {
            u <- UnivBase (BaseKey (g ^ q2));
            r <- Some (Fwd2.fw_obs (self ++ [2]) adv (self, 4) (self, 3) u);
            st <- KERealSimpStateWaitAdv2 (pt1, pt2, q1, q2);
          }
        }
      }
      elif (is_ke_real_simp_state_wait_adv2 st) {
        (pt1, pt2, q1, q2) <- oget (dec_ke_real_simp_state_wait_adv2 st);
        if (Fwd2.is_fw_ok m) {
          (addr1, addr2) <- oget (Fwd2.dec_fw_ok m);
          if (addr1 = self ++ [2]) {
            (* destination of m is (self ++ [2], 1); mode of m is Adv *)
            r <- Some (ke_rsp2 self pt1 ((g ^ q2) ^ q1));
            st <- KERealSimpStateFinal (pt1, pt2, q1, q2);
          }
        }
      }
      else {  (* st = KERealStateFinal *)
      }
      return r;
    }

    proc invoke(m : msg) : msg option = {
      var mod : mode; var pt1, pt2 : port; var u : univ;
      var addr1, addr2 : addr; var n1, n2 : int;
      var r : msg option <- None;
      (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
      if ((mod = Dir /\ addr1 = self /\ (n1 = 1 \/ n1 = 2)) \/
          (mod = Adv /\ (self ++ [1] <= addr1 \/ self ++ [2] <= addr1))) {
        r <- parties(m);
      }
      return r;
    }
  }

  proc main() : bool = {
    var b : bool;
    Hash.rhash(exp1); Hash.rhash(exp2);
    b <@ Exper(MI(KERealSimpHash, Adv), Env).main
           (DDH_Adv.func, DDH_Adv.adv, fset1 adv_fw_pi);
    return b;
  }
}.

(* relation between state of KERealSimpHash and map of
   RH.OptHashing *)

type real_simp_hash_rel_st = {
  real_simp_hash_rel_st_rss : ke_real_simp_state;
  real_simp_hash_rel_st_map : (exp_names, exp) fmap;
}.

pred real_simp_hash_rel0 (st : real_simp_hash_rel_st) =
  st.`real_simp_hash_rel_st_rss = KERealSimpStateWaitReq1 /\
  st.`real_simp_hash_rel_st_map.[exp1] = None /\
  st.`real_simp_hash_rel_st_map.[exp2] = None.

pred real_simp_hash_rel1 (st : real_simp_hash_rel_st, pt1 pt2 : port, q1 : exp) =
  st.`real_simp_hash_rel_st_rss = KERealSimpStateWaitAdv1 (pt1, pt2, q1) /\
  st.`real_simp_hash_rel_st_map.[exp1] = Some q1 /\
  st.`real_simp_hash_rel_st_map.[exp2] = None.

pred real_simp_hash_rel2 (st : real_simp_hash_rel_st, pt1 pt2 : port, q1 q2 : exp) =
  st.`real_simp_hash_rel_st_rss = KERealSimpStateWaitReq2 (pt1, pt2, q1, q2) /\
  st.`real_simp_hash_rel_st_map.[exp1] = Some q1 /\
  st.`real_simp_hash_rel_st_map.[exp2] = Some q2.

pred real_simp_hash_rel3 (st : real_simp_hash_rel_st, pt1 pt2 : port, q1 q2 : exp) =
  st.`real_simp_hash_rel_st_rss = KERealSimpStateWaitAdv2 (pt1, pt2, q1, q2) /\
  st.`real_simp_hash_rel_st_map.[exp1] = Some q1 /\
  st.`real_simp_hash_rel_st_map.[exp2] = Some q2.

pred real_simp_hash_rel4 (st : real_simp_hash_rel_st, pt1 pt2 : port, q1 q2 : exp) =
  st.`real_simp_hash_rel_st_rss = KERealSimpStateFinal (pt1, pt2, q1, q2) /\
  st.`real_simp_hash_rel_st_map.[exp1] = Some q1 /\
  st.`real_simp_hash_rel_st_map.[exp2] = Some q2.

inductive real_simp_hash_rel (st : real_simp_hash_rel_st) =
    RealSimpHashRel0 of (real_simp_hash_rel0 st)
  | RealSimpHashRel1 (pt1 pt2 : port, q1 : exp) of
      (real_simp_hash_rel1 st pt1 pt2 q1)
  | RealSimpHashRel2 (pt1 pt2 : port, q1 q2 : exp) of
      (real_simp_hash_rel2 st pt1 pt2 q1 q2)
  | RealSimpHashRel3 (pt1 pt2 : port, q1 q2 : exp) of
      (real_simp_hash_rel3 st pt1 pt2 q1 q2)
  | RealSimpHashRel4 (pt1 pt2 : port, q1 q2 : exp) of
      (real_simp_hash_rel4 st pt1 pt2 q1 q2).

local lemma KERealSimp_KERealSimpHash_OptHashing_invoke :
  equiv
  [KERealSimp.invoke ~
   KERealSimpHashingAdv(RH.OptHashing).KERealSimpHash.invoke :
   ={m} /\
   ={self, adv, st}(KERealSimp, KERealSimpHashingAdv.KERealSimpHash) /\
   real_simp_hash_rel
   {|real_simp_hash_rel_st_rss = KERealSimp.st{1};
     real_simp_hash_rel_st_map = RH.OptHashing.mp{2}|} ==>
   ={res} /\
   ={self, adv, st}(KERealSimp, KERealSimpHashingAdv.KERealSimpHash) /\
   real_simp_hash_rel
   {|real_simp_hash_rel_st_rss = KERealSimp.st{1};
     real_simp_hash_rel_st_map = RH.OptHashing.mp{2}|}].
proof.
proc.
case
  (real_simp_hash_rel0
   {|real_simp_hash_rel_st_rss = KERealSimp.st{1};
     real_simp_hash_rel_st_map = RH.OptHashing.mp{2}|}).
sp 3 3.
if => //.
inline KERealSimp.parties
       KERealSimpHashingAdv(RH.OptHashing).KERealSimpHash.parties.
sp 2 2.
rcondt{1} 1; first auto; smt().
rcondt{2} 1; first auto; smt().
if => //.
sp 1 1.
if => //.
move => &1 &2 /> <- //.
wp.
inline RH.OptHashing.hash.
rcondt{2} 2; first auto; smt().
auto => &1 &2 /> <-.
progress.
by rewrite get_setE /= oget_some.
by rewrite get_setE /= oget_some.
rewrite (RealSimpHashRel1 _ pt10{2} pt20{2} q1L)
        /real_simp_hash_rel1 /=.
by rewrite 2!get_setE.
auto.
auto.
case
  (exists (pt1 pt2 : port) (q1 : exp),
   real_simp_hash_rel1
   {|real_simp_hash_rel_st_rss = KERealSimp.st{1};
     real_simp_hash_rel_st_map = RH.OptHashing.mp{2}|}
   pt1 pt2 q1).
elim* => pt1 pt2 q1.
sp 3 3.
if => //.
inline KERealSimp.parties
       KERealSimpHashingAdv(RH.OptHashing).KERealSimpHash.parties.
sp 2 2.
rcondf{1} 1; first auto; smt().
rcondt{1} 1; first auto; smt(is_ke_real_simp_state_wait_adv1).
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_ke_real_simp_state_wait_adv1).
sp 1 1.
if => //.
sp 1 1.
if.
move => &1 &2 [#] dec_fw_ok2 dec_fw_ok1 dec_wait2 dec_wait1
        ->> _ ->> _ _ _ _ _ _ _ ->> <<- <<- <<-.
rewrite -dec_fw_ok2 /= in dec_fw_ok1.
elim dec_fw_ok1 => -> _ //.
wp.
inline RH.OptHashing.hash.
rcondt{2} 2; first auto; smt().
auto => &1 &2 |> _ _ ^ st2_eq <- /= [#] -> -> -> _ _
        @/real_simp_hash_rel1 /= [#] ->>.
progress.
by rewrite get_setE /= oget_some.
by rewrite get_setE /= oget_some.
rewrite (RealSimpHashRel2 _ pt10{2} pt20{2} q1 q2L)
        /real_simp_hash_rel2 /=.
rewrite 2!get_setE /= /#.
auto.
auto.
case
  (exists (pt1 pt2 : port) (q1 q2 : exp),
   real_simp_hash_rel2
   {|real_simp_hash_rel_st_rss = KERealSimp.st{1};
     real_simp_hash_rel_st_map = RH.OptHashing.mp{2}|}
   pt1 pt2 q1 q2).
elim* => pt1 pt2 q1 q2.
sp 3 3.
if => //.
inline KERealSimp.parties
       KERealSimpHashingAdv(RH.OptHashing).KERealSimpHash.parties.
sp 2 2.
rcondf{1} 1; first auto; smt().
rcondf{1} 1; first auto; smt().
rcondt{1} 1; first auto; smt(is_ke_real_simp_state_wait_req2).
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_ke_real_simp_state_wait_req2).
auto => &1 &2 |> _ _ _ @/real_simp_hash_rel2 /= [#].
progress.
rewrite oget_some (RealSimpHashRel3 _ pt1 pt2 q1 q2)
        /real_simp_hash_rel3 /= /#.
case
  (exists (pt1 pt2 : port) (q1 q2 : exp),
   real_simp_hash_rel3
   {|real_simp_hash_rel_st_rss = KERealSimp.st{1};
     real_simp_hash_rel_st_map = RH.OptHashing.mp{2}|}
   pt1 pt2 q1 q2).
elim* => pt1 pt2 q1 q2.
sp 3 3.
if => //.
inline KERealSimp.parties
       KERealSimpHashingAdv(RH.OptHashing).KERealSimpHash.parties.
sp 2 2.
rcondf{1} 1; first auto; smt().
rcondf{1} 1; first auto; smt().
rcondf{1} 1; first auto; smt().
rcondt{1} 1; first auto; smt(is_ke_real_simp_state_wait_adv2).
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_ke_real_simp_state_wait_adv2).
auto => &1 &2 |> _ _ _ @/real_simp_hash_rel3 /= [#].
progress.
rewrite oget_some (RealSimpHashRel4 _ pt1 pt2 q1 q2)
        /real_simp_hash_rel4 /= /#.
case
  (exists (pt1 pt2 : port) (q1 q2 : exp),
   real_simp_hash_rel4
   {|real_simp_hash_rel_st_rss = KERealSimp.st{1};
     real_simp_hash_rel_st_map = RH.OptHashing.mp{2}|}
   pt1 pt2 q1 q2).
elim* => pt1 pt2 q1 q2.
sp 3 3.
if => //.
inline KERealSimp.parties
       KERealSimpHashingAdv(RH.OptHashing).KERealSimpHash.parties.
sp 2 2.
rcondf{1} 1; first auto; smt().
rcondf{1} 1; first auto; smt().
rcondf{1} 1; first auto; smt().
rcondf{1} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
auto.
exfalso => &1 &2 [#] _ _ _ _ []; smt().
qed.

local lemma Exper_KERealSimp_GOptHashing_KERealSimpHashingAdv
            (func' adv' : addr) &m :
  DDH_Adv.func{m} = func' => DDH_Adv.adv{m} = adv' =>
  Pr[Exper(MI(KERealSimp, Adv), Env).main
       (func', adv', fset1 adv_fw_pi) @ &m : res] =
  Pr[RH.GOptHashing(KERealSimpHashingAdv).main() @ &m : res].
proof.
move => func'_eq adv'_eq.
byequiv => //.
proc.
inline MI(KERealSimp, Adv).init
       KERealSimp.init
       RH.OptHashing.init
       RH.GOptHashing(KERealSimpHashingAdv).HA.main
       RH.OptHashing.rhash
       Exper(MI(KERealSimpHashingAdv(RH.OptHashing).KERealSimpHash,
                Adv),
             Env).main
       KERealSimpHashingAdv(RH.OptHashing).KERealSimpHash.init
       MI(KERealSimpHashingAdv(RH.OptHashing).KERealSimpHash, Adv).init.
wp.
seq 12 18 :
  (={func, adv, in_guard, MI.func, MI.adv, MI.in_guard} /\
   ={self, adv, st}(KERealSimp, KERealSimpHashingAdv.KERealSimpHash) /\
   func' = func{1} /\ func{1} = MI.func{1} /\
   KERealSimp.self{1} = func{1} /\
   adv' = adv{1} /\ adv{1} = MI.adv{1} /\
   KERealSimp.adv{1} = adv{1} /\
   KERealSimp.st{1} = KERealSimpStateWaitReq1 /\
   RH.OptHashing.mp{2} = empty /\
   ={glob Adv}).
call (_ : true).
auto; smt().
call
  (_ :
   ={MI.func, MI.adv, MI.in_guard} /\
   ={self, adv, st}(KERealSimp, KERealSimpHashingAdv.KERealSimpHash) /\
   KERealSimp.self{1} = MI.func{1} /\ KERealSimp.adv{1} = MI.adv{1} /\
   ={glob Adv} /\
   real_simp_hash_rel
   {|real_simp_hash_rel_st_rss = KERealSimp.st{1};
     real_simp_hash_rel_st_map = RH.OptHashing.mp{2}|}).
proc.
sp 2 2.
if => //.
inline MI(KERealSimp, Adv).loop
       MI(KERealSimpHashingAdv(RH.OptHashing).KERealSimpHash, Adv).loop.
sp 3 3; wp.
while
  (={not_done} /\ ={m0, r0} /\
   ={MI.func, MI.adv, MI.in_guard} /\
   ={self, adv, st}(KERealSimp, KERealSimpHashingAdv.KERealSimpHash) /\
   KERealSimp.self{1} = MI.func{1} /\ KERealSimp.adv{1} = MI.adv{1} /\
   ={glob Adv} /\
   real_simp_hash_rel
   {|real_simp_hash_rel_st_rss = KERealSimp.st{1};
     real_simp_hash_rel_st_map = RH.OptHashing.mp{2}|}).
sp 2 2.
if => //.
wp.
call KERealSimp_KERealSimpHash_OptHashing_invoke.
auto.
wp.
call (_ : true).
auto.
auto.
auto.
auto; progress.
rewrite RealSimpHashRel0 /real_simp_hash_rel0 /=; smt(emptyE).
qed.

(* relation supporting transition from
  RH.GNonOptHashing(KERealSimpHashingAdv) to
  DDH1(DDH_Adv(Env, Adv)) *)

type real_simp_hash_ddh1_rel_st = {
  real_simp_hash_ddh1_rel_st_x1 : key;
  real_simp_hash_ddh1_rel_st_x2 : key;
  real_simp_hash_ddh1_rel_st_rss : ke_real_simp_state;
  real_simp_hash_ddh1_rel_st_hs  : ke_ddh_state;
}.

pred real_simp_hash_ddh1_rel0 (st : real_simp_hash_ddh1_rel_st) =
  st.`real_simp_hash_ddh1_rel_st_rss = KERealSimpStateWaitReq1 /\
  st.`real_simp_hash_ddh1_rel_st_hs = KEDDHStateWaitReq1.

pred real_simp_hash_ddh1_rel1
     (st : real_simp_hash_ddh1_rel_st, pt1 pt2 : port) =
  st.`real_simp_hash_ddh1_rel_st_rss =
  KERealSimpStateWaitAdv1 (pt1, pt2, log st.`real_simp_hash_ddh1_rel_st_x1) /\
  st.`real_simp_hash_ddh1_rel_st_hs =
  KEDDHStateWaitAdv1 (pt1, pt2).

pred real_simp_hash_ddh1_rel2
     (st : real_simp_hash_ddh1_rel_st, pt1 pt2 : port) =
  st.`real_simp_hash_ddh1_rel_st_rss =
  KERealSimpStateWaitReq2
  (pt1, pt2,
   log st.`real_simp_hash_ddh1_rel_st_x1,
   log st.`real_simp_hash_ddh1_rel_st_x2) /\
  st.`real_simp_hash_ddh1_rel_st_hs =
  KEDDHStateWaitReq2 (pt1, pt2).

pred real_simp_hash_ddh1_rel3
     (st : real_simp_hash_ddh1_rel_st, pt1 pt2 : port) =
  st.`real_simp_hash_ddh1_rel_st_rss =
  KERealSimpStateWaitAdv2
  (pt1, pt2,
   log st.`real_simp_hash_ddh1_rel_st_x1,
   log st.`real_simp_hash_ddh1_rel_st_x2) /\
  st.`real_simp_hash_ddh1_rel_st_hs =
  KEDDHStateWaitAdv2 (pt1, pt2).

pred real_simp_hash_ddh1_rel4
     (st : real_simp_hash_ddh1_rel_st, pt1 pt2 : port) =
  st.`real_simp_hash_ddh1_rel_st_rss =
  KERealSimpStateFinal
  (pt1, pt2,
   log st.`real_simp_hash_ddh1_rel_st_x1,
   log st.`real_simp_hash_ddh1_rel_st_x2) /\
  st.`real_simp_hash_ddh1_rel_st_hs =
  KEDDHStateFinal (pt1, pt2).

inductive real_simp_hash_ddh1_rel (st : real_simp_hash_ddh1_rel_st) =
    RealSimpHashDDH1Rel0 of (real_simp_hash_ddh1_rel0 st)
  | RealSimpHashDDH1Rel1 (pt1 pt2 : port) of
      (real_simp_hash_ddh1_rel1 st pt1 pt2)
  | RealSimpHashDDH1Rel2 (pt1 pt2 : port) of
      (real_simp_hash_ddh1_rel2 st pt1 pt2)
  | RealSimpHashDDH1Rel3 (pt1 pt2 : port) of
      (real_simp_hash_ddh1_rel3 st pt1 pt2)
  | RealSimpHashDDH1Rel4 (pt1 pt2 : port) of
      (real_simp_hash_ddh1_rel4 st pt1 pt2).

local lemma KERealSimpHashingAdv_NonOptHashing_KEDDH_DDH1_invoke :
  equiv
  [KERealSimpHashingAdv(RH.NonOptHashing).KERealSimpHash.invoke ~
   DDH_Adv(Env, Adv).KEDDH.invoke :
   ={m} /\
   RH.NonOptHashing.mp{1}.[exp1] = Some (log DDH_Adv.x1{2}) /\
   RH.NonOptHashing.mp{1}.[exp2] = Some (log DDH_Adv.x2{2}) /\
   DDH_Adv.x3{2} = g ^ (log DDH_Adv.x1{2} * log DDH_Adv.x2{2}) /\
   ={MI.func, MI.adv, MI.in_guard} /\
   ={self, adv}(KERealSimpHashingAdv.KERealSimpHash, DDH_Adv.KEDDH) /\
   DDH_Adv.KEDDH.self{2} = MI.func{1} /\
   DDH_Adv.KEDDH.adv{2} = MI.adv{1} /\
   ={glob Adv} /\
   real_simp_hash_ddh1_rel
   {|real_simp_hash_ddh1_rel_st_x1 = DDH_Adv.x1{2};
     real_simp_hash_ddh1_rel_st_x2 = DDH_Adv.x2{2};
     real_simp_hash_ddh1_rel_st_rss =
     KERealSimpHashingAdv.KERealSimpHash.st{1};
     real_simp_hash_ddh1_rel_st_hs = DDH_Adv.KEDDH.st{2}|} ==>
   ={res} /\
   RH.NonOptHashing.mp{1}.[exp1] = Some (log DDH_Adv.x1{2}) /\
   RH.NonOptHashing.mp{1}.[exp2] = Some (log DDH_Adv.x2{2}) /\
   DDH_Adv.x3{2} = g ^ (log DDH_Adv.x1{2} * log DDH_Adv.x2{2}) /\
   ={MI.func, MI.adv, MI.in_guard} /\
   ={self, adv}(KERealSimpHashingAdv.KERealSimpHash, DDH_Adv.KEDDH) /\
   DDH_Adv.KEDDH.self{2} = MI.func{1} /\
   DDH_Adv.KEDDH.adv{2} = MI.adv{1} /\
   ={glob Adv} /\
   real_simp_hash_ddh1_rel
   {|real_simp_hash_ddh1_rel_st_x1 = DDH_Adv.x1{2};
     real_simp_hash_ddh1_rel_st_x2 = DDH_Adv.x2{2};
     real_simp_hash_ddh1_rel_st_rss =
     KERealSimpHashingAdv.KERealSimpHash.st{1};
     real_simp_hash_ddh1_rel_st_hs = DDH_Adv.KEDDH.st{2}|}].
proof.
proc.
case
  (real_simp_hash_ddh1_rel0
   {|real_simp_hash_ddh1_rel_st_x1 = DDH_Adv.x1{2};
     real_simp_hash_ddh1_rel_st_x2 = DDH_Adv.x2{2};
     real_simp_hash_ddh1_rel_st_rss =
     KERealSimpHashingAdv.KERealSimpHash.st{1};
     real_simp_hash_ddh1_rel_st_hs = DDH_Adv.KEDDH.st{2}|}).
sp 3 3.
if => //.
inline KERealSimpHashingAdv(RH.NonOptHashing).KERealSimpHash.parties
       DDH_Adv(Env, Adv).KEDDH.parties.
sp 2 2.
rcondt{1} 1; first auto; smt().
rcondt{2} 1; first auto; smt().
if => //.
sp 1 1.
if.
move => &1 &2 /> <- //.
inline{1} (1) RH.NonOptHashing.hash.
rcondf{1} 2; first auto; smt().
auto => &1 &2 |> <-.
progress.
clear H8 H7 H6 H5; smt(gen_logK).
by rewrite (RealSimpHashDDH1Rel1 _ pt10{2} pt20{2})
           /real_simp_hash_ddh1_rel1 /= H oget_some.
auto.
auto.
case
  (exists (pt1 pt2 : port),
   real_simp_hash_ddh1_rel1
   {|real_simp_hash_ddh1_rel_st_x1 = DDH_Adv.x1{2};
     real_simp_hash_ddh1_rel_st_x2 = DDH_Adv.x2{2};
     real_simp_hash_ddh1_rel_st_rss =
     KERealSimpHashingAdv.KERealSimpHash.st{1};
     real_simp_hash_ddh1_rel_st_hs = DDH_Adv.KEDDH.st{2}|}
   pt1 pt2).
elim* => pt1 pt2.
sp 3 3.
if => //.
inline KERealSimpHashingAdv(RH.NonOptHashing).KERealSimpHash.parties
       DDH_Adv(Env, Adv).KEDDH.parties.
sp 2 2.
rcondf{1} 1; first auto; smt().
rcondt{1} 1; first auto; smt(is_ke_real_simp_state_wait_adv1).
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_ke_ddh_state_wait_adv1).
sp 1 1.
if => //.
sp 1 1.
if.
move => &1 &2 [#] dec_fw_ok2 dec_fw_ok1 dec_wait2 dec_wait1
        ->> _ ->> _ _ _ _ _ _ _ ->> <<- <<- <<-.
rewrite -dec_fw_ok2 /= in dec_fw_ok1.
elim dec_fw_ok1 => -> _ //.
inline{1} (1) RH.NonOptHashing.hash.
rcondf{1} 2; first auto; smt().
auto => &1 &2 |> _ _  st2_eq st1_eq mp_exp1_eq mp_exp2_eq
        _ _ @/real_simp_hash_ddh1_rel1 /= [#] ->> ->>.
rewrite /= oget_some /= in st1_eq.
rewrite /= oget_some /= in st2_eq.
elim st1_eq => [#] ->> [#] ->> ->>.
elim st2_eq => -> ->.
progress.
by rewrite mp_exp2_eq oget_some double_exp_gen.
by rewrite (RealSimpHashDDH1Rel2 _ pt1 pt2)
           /real_simp_hash_ddh1_rel2 /= mp_exp2_eq oget_some.
auto.
auto.
case
  (exists (pt1 pt2 : port),
   real_simp_hash_ddh1_rel2
   {|real_simp_hash_ddh1_rel_st_x1 = DDH_Adv.x1{2};
     real_simp_hash_ddh1_rel_st_x2 = DDH_Adv.x2{2};
     real_simp_hash_ddh1_rel_st_rss =
     KERealSimpHashingAdv.KERealSimpHash.st{1};
     real_simp_hash_ddh1_rel_st_hs = DDH_Adv.KEDDH.st{2}|}
   pt1 pt2).
elim* => pt1 pt2.
sp 3 3.
if => //.
inline KERealSimpHashingAdv(RH.NonOptHashing).KERealSimpHash.parties
       DDH_Adv(Env, Adv).KEDDH.parties.
sp 2 2.
rcondf{1} 1; first auto; smt().
rcondf{1} 1; first auto; smt().
rcondt{1} 1; first auto; smt(is_ke_real_simp_state_wait_req2).
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_ke_ddh_state_wait_req2).
sp 1 1.
if => //.
sp 1 1.
if.
move => &1 &2 [#] dec_ke_req2 dec_ke_req1 dec_wait2 dec_wait1
        ->> _ ->> _ _ _ _ _ _ _ ->> _ _ _ _ _ _ _ _ _ _ _ _ _ _
        @/real_simp_hash_ddh1_rel2 /= [#] ->> ->> _ _.
rewrite -dec_ke_req2 /= in dec_ke_req1.
elim dec_ke_req1 => _ ->>.
rewrite /= oget_some /= in dec_wait1.
elim dec_wait1 => ->> [#] ->> ->> _.
rewrite /= oget_some /= in dec_wait2.
by elim dec_wait2 => _ <-.
auto => &1 &2 |> _ _ st2_eq st1_eq mp_exp1_eq mp_exp2_eq _ _ _
        @/real_simp_hash_ddh1_rel2 /= [#] ->> ->> _ _.
rewrite /= oget_some /= in st2_eq.
elim st2_eq => ->> ->>.
rewrite /= oget_some /= in st1_eq.
elim st1_eq => ->> [#] ->> ->> ->>.
progress.
smt(gen_logK).
by rewrite (RealSimpHashDDH1Rel3 _ pt1 pt2) /real_simp_hash_ddh1_rel3.
auto.
auto.
case
  (exists (pt1 pt2 : port),
   real_simp_hash_ddh1_rel3
   {|real_simp_hash_ddh1_rel_st_x1 = DDH_Adv.x1{2};
     real_simp_hash_ddh1_rel_st_x2 = DDH_Adv.x2{2};
     real_simp_hash_ddh1_rel_st_rss =
     KERealSimpHashingAdv.KERealSimpHash.st{1};
     real_simp_hash_ddh1_rel_st_hs = DDH_Adv.KEDDH.st{2}|}
   pt1 pt2).
elim* => pt1 pt2.
sp 3 3.
if => //.
inline KERealSimpHashingAdv(RH.NonOptHashing).KERealSimpHash.parties
       DDH_Adv(Env, Adv).KEDDH.parties.
sp 2 2.
rcondf{1} 1; first auto; smt().
rcondf{1} 1; first auto; smt().
rcondf{1} 1; first auto; smt().
rcondt{1} 1; first auto; smt(is_ke_real_simp_state_wait_adv2).
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_ke_ddh_state_wait_adv2).
sp 1 1.
if => //.
sp 1 1.
if.
move => &1 &2 [#] dec_fw_ok2 dec_fw_ok1 dec_wait2 dec_wait1
        ->> _ ->> _ _ _ _ _ _ _ ->> _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        @/real_simp_hash_ddh1_rel3 /= [#] ->> ->> _ _.
rewrite -dec_fw_ok2 /= in dec_fw_ok1.
elim dec_fw_ok1 => ->> ->>.
congr. congr.
auto => &1 &2 |> <- /= [#] -> _ dec_wait2 dec_wait1
        mp_exp1_eq mp_exp2_eq _ _ _ _
        @/real_simp_hash_ddh1_rel3 /= [#] ->> ->> _ _.
rewrite /= oget_some /= in dec_wait1.
elim dec_wait1 => ->> [#] ->> ->> ->>.
rewrite /= oget_some /= in dec_wait2.
elim dec_wait2 => ->> ->>.
progress.
by rewrite double_exp_gen mulC.
rewrite (RealSimpHashDDH1Rel4 _ pt1 pt2) /#.
auto.
auto.
case
  (exists (pt1 pt2 : port),
   real_simp_hash_ddh1_rel4
   {|real_simp_hash_ddh1_rel_st_x1 = DDH_Adv.x1{2};
     real_simp_hash_ddh1_rel_st_x2 = DDH_Adv.x2{2};
     real_simp_hash_ddh1_rel_st_rss =
     KERealSimpHashingAdv.KERealSimpHash.st{1};
     real_simp_hash_ddh1_rel_st_hs = DDH_Adv.KEDDH.st{2}|}
   pt1 pt2).
elim* => pt1 pt2.
sp 3 3.
if => //.
inline KERealSimpHashingAdv(RH.NonOptHashing).KERealSimpHash.parties
       DDH_Adv(Env, Adv).KEDDH.parties.
sp 2 2.
rcondf{1} 1; first auto; smt().
rcondf{1} 1; first auto; smt().
rcondf{1} 1; first auto; smt().
rcondf{1} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
auto.
exfalso => &1 &2 [#] _ _ _ _ _ _ _ _ _ _ _ _ []; smt().
qed.

local lemma KERealSimpHashingAdv_NonOptHashing_DDH1_DDH_Adv
            (func' adv' : addr) &m :
  DDH_Adv.func{m} = func' => DDH_Adv.adv{m} = adv' =>
  Pr[RH.GNonOptHashing(KERealSimpHashingAdv).main() @ &m : res] =
  Pr[DDH1(DDH_Adv(Env, Adv)).main() @ &m : res].
proof.
move => func'_eq adv'_eq.
byequiv => //.
proc.
inline RH.NonOptHashing.init
       RH.GNonOptHashing(KERealSimpHashingAdv).HA.main
       RH.NonOptHashing.rhash RH.NonOptHashing.hash
       Exper(MI(KERealSimpHashingAdv(RH.NonOptHashing).KERealSimpHash,
                Adv),
             Env).main
       MI(KERealSimpHashingAdv(RH.NonOptHashing).KERealSimpHash, Adv).init
       KERealSimpHashingAdv(RH.NonOptHashing).KERealSimpHash.init
       DDH_Adv(Env, Adv).main
       Exper(MI(DDH_Adv(Env, Adv).KEDDH, Adv), Env).main
       MI(DDH_Adv(Env, Adv).KEDDH, Adv).init
       DDH_Adv(Env, Adv).KEDDH.init.
rcondt{1} 4; first auto; smt(mem_empty).
rcondt{1} 7; first auto; smt(mem_set mem_empty).
wp.
seq 7 8 :
  (={DDH_Adv.func, DDH_Adv.adv} /\
   DDH_Adv.func{1} = func' /\ DDH_Adv.adv{1} = adv' /\
   RH.NonOptHashing.mp{1}.[exp1] = Some u1{2} /\
   RH.NonOptHashing.mp{1}.[exp2] = Some u2{2} /\
   DDH_Adv.x1{2} = g ^ u1{2} /\
   DDH_Adv.x2{2} = g ^ u2{2} /\
   DDH_Adv.x3{2} = g ^ (u1{2} * u2{2})).
auto; progress.
by rewrite get_setE /= get_setE /=.
by rewrite get_setE /=.
seq 15 15 :
  (RH.NonOptHashing.mp{1}.[exp1] = Some u1{2} /\
   RH.NonOptHashing.mp{1}.[exp2] = Some u2{2} /\
   DDH_Adv.x1{2} = g ^ u1{2} /\
   DDH_Adv.x2{2} = g ^ u2{2} /\
   DDH_Adv.x3{2} = g ^ (u1{2} * u2{2}) /\
   ={func, adv, in_guard, MI.func, MI.adv, MI.in_guard,
     DDH_Adv.func, DDH_Adv.adv} /\
   func{1} = func' /\ adv{1} = adv' /\ in_guard{1} = fset1 adv_fw_pi /\
   DDH_Adv.func{1} = func' /\ DDH_Adv.adv{1} = adv' /\
   ={self, adv}(KERealSimpHashingAdv.KERealSimpHash, DDH_Adv.KEDDH) /\
   DDH_Adv.KEDDH.self{2} = MI.func{1} /\
   DDH_Adv.KEDDH.adv{2} = MI.adv{1} /\
   ={glob Adv} /\
   KERealSimpHashingAdv.KERealSimpHash.st{1} = KERealSimpStateWaitReq1 /\
   DDH_Adv.KEDDH.st{2} = KEDDHStateWaitReq1).
call (_ : true).
auto.
call
  (_ :
   RH.NonOptHashing.mp{1}.[exp1] = Some (log DDH_Adv.x1{2}) /\
   RH.NonOptHashing.mp{1}.[exp2] = Some (log DDH_Adv.x2{2}) /\
   DDH_Adv.x3{2} = g ^ (log DDH_Adv.x1{2} * log DDH_Adv.x2{2}) /\
   ={MI.func, MI.adv, MI.in_guard} /\
   ={self, adv}(KERealSimpHashingAdv.KERealSimpHash, DDH_Adv.KEDDH) /\
   DDH_Adv.KEDDH.self{2} = MI.func{1} /\
   DDH_Adv.KEDDH.adv{2} = MI.adv{1} /\
   ={glob Adv} /\
   real_simp_hash_ddh1_rel
   {|real_simp_hash_ddh1_rel_st_x1 = DDH_Adv.x1{2};
     real_simp_hash_ddh1_rel_st_x2 = DDH_Adv.x2{2};
     real_simp_hash_ddh1_rel_st_rss =
     KERealSimpHashingAdv.KERealSimpHash.st{1};
     real_simp_hash_ddh1_rel_st_hs = DDH_Adv.KEDDH.st{2}|}).
proc.
sp 2 2.
if => //.
inline MI(KERealSimpHashingAdv(RH.NonOptHashing).KERealSimpHash, Adv).loop
       MI(DDH_Adv(Env, Adv).KEDDH, Adv).loop.
sp 3 3; wp.
while
  (={not_done} /\ ={m0, r0} /\
   RH.NonOptHashing.mp{1}.[exp1] = Some (log DDH_Adv.x1{2}) /\
   RH.NonOptHashing.mp{1}.[exp2] = Some (log DDH_Adv.x2{2}) /\
   DDH_Adv.x3{2} = g ^ (log DDH_Adv.x1{2} * log DDH_Adv.x2{2}) /\
   ={MI.func, MI.adv, MI.in_guard} /\
   ={self, adv}(KERealSimpHashingAdv.KERealSimpHash, DDH_Adv.KEDDH) /\
   DDH_Adv.KEDDH.self{2} = MI.func{1} /\
   DDH_Adv.KEDDH.adv{2} = MI.adv{1} /\
   ={glob Adv} /\
   real_simp_hash_ddh1_rel
   {|real_simp_hash_ddh1_rel_st_x1 = DDH_Adv.x1{2};
     real_simp_hash_ddh1_rel_st_x2 = DDH_Adv.x2{2};
     real_simp_hash_ddh1_rel_st_rss =
     KERealSimpHashingAdv.KERealSimpHash.st{1};
     real_simp_hash_ddh1_rel_st_hs = DDH_Adv.KEDDH.st{2}|}).
sp 2 2.
if => //.
wp.
call KERealSimpHashingAdv_NonOptHashing_KEDDH_DDH1_invoke.
auto.
wp.
call (_ : true).
auto.
auto.
auto.
auto; progress.
by rewrite log_genK.
by rewrite log_genK.
by rewrite 2!log_genK.
by rewrite RealSimpHashDDH1Rel0.
qed.

type ke_hybrid_state = [
    KEHybridStateWaitReq1
  | KEHybridStateWaitAdv1 of (port * port * exp)
  | KEHybridStateWaitReq2 of (port * port * exp * exp * exp)
  | KEHybridStateWaitAdv2 of (port * port * exp * exp * exp)
  | KEHybridStateFinal    of (port * port * exp * exp * exp)
].

op dec_ke_hybrid_state_wait_adv1 (st : ke_hybrid_state) :
     (port * port * exp) option =
     with st = KEHybridStateWaitReq1   => None
     with st = KEHybridStateWaitAdv1 x => Some x
     with st = KEHybridStateWaitReq2 _ => None
     with st = KEHybridStateWaitAdv2 _ => None
     with st = KEHybridStateFinal _    => None.

lemma enc_dec_ke_hybrid_state_wait_adv1 (x : port * port * exp) :
  dec_ke_hybrid_state_wait_adv1 (KEHybridStateWaitAdv1 x) = Some x.
proof. done. qed.

op is_ke_hybrid_state_wait_adv1 (st : ke_hybrid_state) : bool =
  dec_ke_hybrid_state_wait_adv1 st <> None.

lemma is_ke_hybrid_state_wait_adv1 (x : port * port * exp) :
  is_ke_hybrid_state_wait_adv1 (KEHybridStateWaitAdv1 x).
proof. done. qed.

op dec_ke_hybrid_state_wait_req2 (st : ke_hybrid_state) :
     (port * port * exp * exp * exp) option =
     with st = KEHybridStateWaitReq1   => None
     with st = KEHybridStateWaitAdv1 _ => None
     with st = KEHybridStateWaitReq2 x => Some x
     with st = KEHybridStateWaitAdv2 _ => None
     with st = KEHybridStateFinal _    => None.

lemma enc_dec_ke_hybrid_state_wait_req2 (x : port * port * exp * exp * exp) :
  dec_ke_hybrid_state_wait_req2 (KEHybridStateWaitReq2 x) = Some x.
proof. done. qed.

op is_ke_hybrid_state_wait_req2 (st : ke_hybrid_state) : bool =
  dec_ke_hybrid_state_wait_req2 st <> None.

lemma is_ke_hybrid_state_wait_req2 (x : port * port * exp * exp * exp) :
  is_ke_hybrid_state_wait_req2 (KEHybridStateWaitReq2 x).
proof. done. qed.

op dec_ke_hybrid_state_wait_adv2 (st : ke_hybrid_state) :
     (port * port * exp * exp * exp) option =
     with st = KEHybridStateWaitReq1   => None
     with st = KEHybridStateWaitAdv1 _ => None
     with st = KEHybridStateWaitReq2 _ => None
     with st = KEHybridStateWaitAdv2 x => Some x
     with st = KEHybridStateFinal _    => None.

lemma enc_dec_ke_hybrid_state_wait_adv2 (x : port * port * exp * exp * exp) :
  dec_ke_hybrid_state_wait_adv2 (KEHybridStateWaitAdv2 x) = Some x.
proof. done. qed.

op is_ke_hybrid_state_wait_adv2 (st : ke_hybrid_state) : bool =
  dec_ke_hybrid_state_wait_adv2 st <> None.

lemma is_ke_hybrid_state_wait_adv2 (x : port * port * exp * exp * exp) :
  is_ke_hybrid_state_wait_adv2 (KEHybridStateWaitAdv2 x).
proof. done. qed.

op dec_ke_hybrid_state_final (st : ke_hybrid_state) :
     (port * port * exp * exp * exp) option =
     with st = KEHybridStateWaitReq1   => None
     with st = KEHybridStateWaitAdv1 _ => None
     with st = KEHybridStateWaitReq2 _ => None
     with st = KEHybridStateWaitAdv2 _ => None
     with st = KEHybridStateFinal x    => Some x.

lemma enc_dec_ke_hybrid_state_final (x : port * port * exp * exp * exp) :
  dec_ke_hybrid_state_final (KEHybridStateFinal x) = Some x.
proof. done. qed.

op is_ke_hybrid_state_final (st : ke_hybrid_state) : bool =
  dec_ke_hybrid_state_final st <> None.

lemma is_ke_hybrid_state_final (x : port * port * exp * exp * exp) :
  is_ke_hybrid_state_final (KEHybridStateFinal x).
proof. done. qed.

local module KEHybrid : FUNC = {
  var self, adv : addr
  var st : ke_hybrid_state

  proc init(self_ adv_ : addr) : unit = {
    self <- self_; adv <- adv_;
    st <- KEHybridStateWaitReq1;
  }

  proc parties(m : msg) : msg option = {
    var pt1, pt2, pt1', pt2' : port; var addr, addr1, addr2 : addr;
    var u : univ; var q1, q2, q3 : exp;
    var r : msg option <- None;
    if (st = KEHybridStateWaitReq1) {
      if (is_ke_req1 m) {
        (* destination of m is (self, 1); mode of m is Dir *)
        (addr, pt1, pt2) <- oget (dec_ke_req1 m);
        if (! self <= pt1.`1 /\ ! self <= pt2.`1 /\
            ! adv <= pt1.`1 /\ ! adv <= pt2.`1) {
          q1 <$ dexp;
          u <-
            univ_triple (UnivPort pt1) (UnivPort pt2)
                        (UnivBase (BaseKey (g ^ q1)));
          r <- Some (Fwd1.fw_obs (self ++ [1]) adv (self, 3) (self, 4) u);
          st <- KEHybridStateWaitAdv1 (pt1, pt2, q1);
        }
      }
    }
    elif (is_ke_hybrid_state_wait_adv1 st) {
      (pt1, pt2, q1) <- oget (dec_ke_hybrid_state_wait_adv1 st);
      if (Fwd1.is_fw_ok m) {
        (addr1, addr2) <- oget (Fwd1.dec_fw_ok m);
        if (addr1 = self ++ [1]) {
          (* destination of m is (self ++ [1], 1); mode of m is Adv *)
          q2 <$ dexp; q3 <$ dexp;
          r <- Some (ke_rsp1 self pt1 pt2 (g ^ q3));
          st <- KEHybridStateWaitReq2 (pt1, pt2, q1, q2, q3);
        }
      }
    }
    elif (is_ke_hybrid_state_wait_req2 st) {
      (pt1, pt2, q1, q2, q3) <- oget (dec_ke_hybrid_state_wait_req2 st);
      if (is_ke_req2 m) {
        (* destination of m is (self, 2); mode of m is Dir *)
        (addr, pt2') <- oget (dec_ke_req2 m);
        if (pt2' = pt2) {
          u <- UnivBase (BaseKey (g ^ q2));
          r <- Some (Fwd2.fw_obs (self ++ [2]) adv (self, 4) (self, 3) u);
          st <- KEHybridStateWaitAdv2 (pt1, pt2, q1, q2, q3);
        }
      }
    }
    elif (is_ke_hybrid_state_wait_adv2 st) {
      (pt1, pt2, q1, q2, q3) <- oget (dec_ke_hybrid_state_wait_adv2 st);
      if (Fwd2.is_fw_ok m) {
        (addr1, addr2) <- oget (Fwd2.dec_fw_ok m);
        if (addr1 = self ++ [2]) {
          (* destination of m is (self ++ [2], 1); mode of m is Adv *)
          r <- Some (ke_rsp2 self pt1 (g ^ q3));
          st <- KEHybridStateFinal (pt1, pt2, q1, q2, q3);
        }
      }
    }
    else {  (* st = KERealStateFinal *)
    }
    return r;
  }

  proc invoke(m : msg) : msg option = {
    var mod : mode; var pt1, pt2 : port; var u : univ;
    var addr1, addr2 : addr; var n1, n2 : int;
    var r : msg option <- None;
    (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
    if ((mod = Dir /\ addr1 = self /\ (n1 = 1 \/ n1 = 2)) \/
        (mod = Adv /\ (self ++ [1] <= addr1 \/ self ++ [2] <= addr1))) {
      r <- parties(m);
    }
    return r;
  }
}.

local module (KEHybridHashingAdv : RH.HASHING_ADV)
             (Hash : RH.HASHING) = {
  module KEHybridHash : FUNC = {
    var self, adv : addr
    var st : ke_hybrid_state

    proc init(self_ adv_ : addr) : unit = {
      self <- self_; adv <- adv_;
      st <- KEHybridStateWaitReq1;
    }

  proc parties(m : msg) : msg option = {
    var pt1, pt2, pt1', pt2' : port; var addr, addr1, addr2 : addr;
    var u : univ; var q1, q2, q3 : exp;
    var r : msg option <- None;
    if (st = KEHybridStateWaitReq1) {
      if (is_ke_req1 m) {
        (* destination of m is (self, 1); mode of m is Dir *)
        (addr, pt1, pt2) <- oget (dec_ke_req1 m);
        if (! self <= pt1.`1 /\ ! self <= pt2.`1 /\
            ! adv <= pt1.`1 /\ ! adv <= pt2.`1) {
          q1 <@ Hash.hash(exp1);
          u <-
            univ_triple (UnivPort pt1) (UnivPort pt2)
                        (UnivBase (BaseKey (g ^ q1)));
          r <- Some (Fwd1.fw_obs (self ++ [1]) adv (self, 3) (self, 4) u);
          st <- KEHybridStateWaitAdv1 (pt1, pt2, q1);
        }
      }
    }
    elif (is_ke_hybrid_state_wait_adv1 st) {
      (pt1, pt2, q1) <- oget (dec_ke_hybrid_state_wait_adv1 st);
      if (Fwd1.is_fw_ok m) {
        (addr1, addr2) <- oget (Fwd1.dec_fw_ok m);
        if (addr1 = self ++ [1]) {
          (* destination of m is (self ++ [1], 1); mode of m is Adv *)
          q2 <@ Hash.hash(exp2); q3 <@ Hash.hash(exp3);
          r <- Some (ke_rsp1 self pt1 pt2 (g ^ q3));
          st <- KEHybridStateWaitReq2 (pt1, pt2, q1, q2, q3);
        }
      }
    }
    elif (is_ke_hybrid_state_wait_req2 st) {
      (pt1, pt2, q1, q2, q3) <- oget (dec_ke_hybrid_state_wait_req2 st);
      if (is_ke_req2 m) {
        (* destination of m is (self, 2); mode of m is Dir *)
        (addr, pt2') <- oget (dec_ke_req2 m);
        if (pt2' = pt2) {
          u <- UnivBase (BaseKey (g ^ q2));
          r <- Some (Fwd2.fw_obs (self ++ [2]) adv (self, 4) (self, 3) u);
          st <- KEHybridStateWaitAdv2 (pt1, pt2, q1, q2, q3);
        }
      }
    }
    elif (is_ke_hybrid_state_wait_adv2 st) {
      (pt1, pt2, q1, q2, q3) <- oget (dec_ke_hybrid_state_wait_adv2 st);
      if (Fwd2.is_fw_ok m) {
        (addr1, addr2) <- oget (Fwd2.dec_fw_ok m);
        if (addr1 = self ++ [2]) {
          (* destination of m is (self ++ [2], 1); mode of m is Adv *)
          r <- Some (ke_rsp2 self pt1 (g ^ q3));
          st <- KEHybridStateFinal (pt1, pt2, q1, q2, q3);
        }
      }
    }
    else {  (* st = KERealStateFinal *)
    }
    return r;
  }

    proc invoke(m : msg) : msg option = {
      var mod : mode; var pt1, pt2 : port; var u : univ;
      var addr1, addr2 : addr; var n1, n2 : int;
      var r : msg option <- None;
      (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
      if ((mod = Dir /\ addr1 = self /\ (n1 = 1 \/ n1 = 2)) \/
          (mod = Adv /\ (self ++ [1] <= addr1 \/ self ++ [2] <= addr1))) {
        r <- parties(m);
      }
      return r;
    }
  }

  proc main() : bool = {
    var b : bool;
    Hash.rhash(exp1); Hash.rhash(exp2); Hash.rhash(exp3);
    b <@ Exper(MI(KEHybridHash, Adv), Env).main
           (DDH_Adv.func, DDH_Adv.adv, fset1 adv_fw_pi);
    return b;
  }
}.

(* relation supporting transition from
   RH.GNonOptHashing(KEHybridHashingAdv) to
   DDH2(DDH_Adv(Env, Adv)) *)

type hybrid_hash_ddh2_rel_st = {
  hybrid_hash_ddh2_rel_st_x1 : key;
  hybrid_hash_ddh2_rel_st_x2 : key;
  hybrid_hash_ddh2_rel_st_x3 : key;
  hybrid_hash_ddh2_rel_st_rss : ke_hybrid_state;
  hybrid_hash_ddh2_rel_st_hs  : ke_ddh_state;
}.

pred hybrid_hash_ddh2_rel0 (st : hybrid_hash_ddh2_rel_st) =
  st.`hybrid_hash_ddh2_rel_st_rss = KEHybridStateWaitReq1 /\
  st.`hybrid_hash_ddh2_rel_st_hs = KEDDHStateWaitReq1.

pred hybrid_hash_ddh2_rel1
     (st : hybrid_hash_ddh2_rel_st, pt1 pt2 : port) =
  st.`hybrid_hash_ddh2_rel_st_rss =
  KEHybridStateWaitAdv1 (pt1, pt2, log st.`hybrid_hash_ddh2_rel_st_x1) /\
  st.`hybrid_hash_ddh2_rel_st_hs =
  KEDDHStateWaitAdv1 (pt1, pt2).

pred hybrid_hash_ddh2_rel2
     (st : hybrid_hash_ddh2_rel_st, pt1 pt2 : port) =
  st.`hybrid_hash_ddh2_rel_st_rss =
  KEHybridStateWaitReq2
  (pt1, pt2,
   log st.`hybrid_hash_ddh2_rel_st_x1,
   log st.`hybrid_hash_ddh2_rel_st_x2,
   log st.`hybrid_hash_ddh2_rel_st_x3) /\
  st.`hybrid_hash_ddh2_rel_st_hs =
  KEDDHStateWaitReq2 (pt1, pt2).

pred hybrid_hash_ddh2_rel3
     (st : hybrid_hash_ddh2_rel_st, pt1 pt2 : port) =
  st.`hybrid_hash_ddh2_rel_st_rss =
  KEHybridStateWaitAdv2
  (pt1, pt2,
   log st.`hybrid_hash_ddh2_rel_st_x1,
   log st.`hybrid_hash_ddh2_rel_st_x2,
   log st.`hybrid_hash_ddh2_rel_st_x3) /\
  st.`hybrid_hash_ddh2_rel_st_hs =
  KEDDHStateWaitAdv2 (pt1, pt2).

pred hybrid_hash_ddh2_rel4
     (st : hybrid_hash_ddh2_rel_st, pt1 pt2 : port) =
  st.`hybrid_hash_ddh2_rel_st_rss =
  KEHybridStateFinal
  (pt1, pt2,
   log st.`hybrid_hash_ddh2_rel_st_x1,
   log st.`hybrid_hash_ddh2_rel_st_x2,
   log st.`hybrid_hash_ddh2_rel_st_x3) /\
  st.`hybrid_hash_ddh2_rel_st_hs =
  KEDDHStateFinal (pt1, pt2).

inductive hybrid_hash_ddh2_rel (st : hybrid_hash_ddh2_rel_st) =
    HybridHashDDH2Rel0 of (hybrid_hash_ddh2_rel0 st)
  | HybridHashDDH2Rel1 (pt1 pt2 : port) of
      (hybrid_hash_ddh2_rel1 st pt1 pt2)
  | HybridHashDDH2Rel2 (pt1 pt2 : port) of
      (hybrid_hash_ddh2_rel2 st pt1 pt2)
  | HybridHashDDH2Rel3 (pt1 pt2 : port) of
      (hybrid_hash_ddh2_rel3 st pt1 pt2)
  | HybridHashDDH2Rel4 (pt1 pt2 : port) of
      (hybrid_hash_ddh2_rel4 st pt1 pt2).

local lemma KEHybridHashingAdv_NonOptHashing_KEDDH_DDH2_invoke :
  equiv
  [KEHybridHashingAdv(RH.NonOptHashing).KEHybridHash.invoke ~
   DDH_Adv(Env, Adv).KEDDH.invoke :
   ={m} /\
   RH.NonOptHashing.mp{1}.[exp1] = Some (log DDH_Adv.x1{2}) /\
   RH.NonOptHashing.mp{1}.[exp2] = Some (log DDH_Adv.x2{2}) /\
   RH.NonOptHashing.mp{1}.[exp3] = Some (log DDH_Adv.x3{2}) /\
   ={MI.func, MI.adv, MI.in_guard} /\
   ={self, adv}(KEHybridHashingAdv.KEHybridHash, DDH_Adv.KEDDH) /\
   DDH_Adv.KEDDH.self{2} = MI.func{1} /\
   DDH_Adv.KEDDH.adv{2} = MI.adv{1} /\
   ={glob Adv} /\
   hybrid_hash_ddh2_rel
   {|hybrid_hash_ddh2_rel_st_x1 = DDH_Adv.x1{2};
     hybrid_hash_ddh2_rel_st_x2 = DDH_Adv.x2{2};
     hybrid_hash_ddh2_rel_st_x3 = DDH_Adv.x3{2};
     hybrid_hash_ddh2_rel_st_rss =
     KEHybridHashingAdv.KEHybridHash.st{1};
     hybrid_hash_ddh2_rel_st_hs = DDH_Adv.KEDDH.st{2}|} ==>
   ={res} /\
   RH.NonOptHashing.mp{1}.[exp1] = Some (log DDH_Adv.x1{2}) /\
   RH.NonOptHashing.mp{1}.[exp2] = Some (log DDH_Adv.x2{2}) /\
   RH.NonOptHashing.mp{1}.[exp3] = Some (log DDH_Adv.x3{2}) /\
   ={MI.func, MI.adv, MI.in_guard} /\
   ={self, adv}(KEHybridHashingAdv.KEHybridHash, DDH_Adv.KEDDH) /\
   DDH_Adv.KEDDH.self{2} = MI.func{1} /\
   DDH_Adv.KEDDH.adv{2} = MI.adv{1} /\
   ={glob Adv} /\
   hybrid_hash_ddh2_rel
   {|hybrid_hash_ddh2_rel_st_x1 = DDH_Adv.x1{2};
     hybrid_hash_ddh2_rel_st_x2 = DDH_Adv.x2{2};
     hybrid_hash_ddh2_rel_st_x3 = DDH_Adv.x3{2};
     hybrid_hash_ddh2_rel_st_rss =
     KEHybridHashingAdv.KEHybridHash.st{1};
     hybrid_hash_ddh2_rel_st_hs = DDH_Adv.KEDDH.st{2}|}].
proof.
proc.
case
  (hybrid_hash_ddh2_rel0
   {|hybrid_hash_ddh2_rel_st_x1 = DDH_Adv.x1{2};
     hybrid_hash_ddh2_rel_st_x2 = DDH_Adv.x2{2};
     hybrid_hash_ddh2_rel_st_x3 = DDH_Adv.x3{2};
     hybrid_hash_ddh2_rel_st_rss =
     KEHybridHashingAdv.KEHybridHash.st{1};
     hybrid_hash_ddh2_rel_st_hs = DDH_Adv.KEDDH.st{2}|}).
sp 3 3.
if => //.
inline KEHybridHashingAdv(RH.NonOptHashing).KEHybridHash.parties
       DDH_Adv(Env, Adv).KEDDH.parties.
sp 2 2.
rcondt{1} 1; first auto; smt().
rcondt{2} 1; first auto; smt().
if => //.
sp 1 1.
if.
move => &1 &2 /> <- //.
inline{1} (1) RH.NonOptHashing.hash.
rcondf{1} 2; first auto; smt().
auto => &1 &2 |> <-.
progress.
smt(gen_logK).
rewrite (HybridHashDDH2Rel1 _ pt10{2} pt20{2})
        /hybrid_hash_ddh2_rel1 /= /#.
auto.
auto.
case
  (exists (pt1 pt2 : port),
   hybrid_hash_ddh2_rel1
   {|hybrid_hash_ddh2_rel_st_x1 = DDH_Adv.x1{2};
     hybrid_hash_ddh2_rel_st_x2 = DDH_Adv.x2{2};
     hybrid_hash_ddh2_rel_st_x3 = DDH_Adv.x3{2};
     hybrid_hash_ddh2_rel_st_rss =
     KEHybridHashingAdv.KEHybridHash.st{1};
     hybrid_hash_ddh2_rel_st_hs = DDH_Adv.KEDDH.st{2}|}
   pt1 pt2).
elim* => pt1 pt2.
sp 3 3.
if => //.
inline KEHybridHashingAdv(RH.NonOptHashing).KEHybridHash.parties
       DDH_Adv(Env, Adv).KEDDH.parties.
sp 2 2.
rcondf{1} 1; first auto; smt().
rcondt{1} 1; first auto; smt(is_ke_hybrid_state_wait_adv1).
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_ke_ddh_state_wait_adv1).
sp 1 1.
if => //.
sp 1 1.
if.
move => &1 &2 [#] dec_fw_ok2 dec_fw_ok1 dec_wait2 dec_wait1
        ->> _ ->> _ _ _ _ _ _ _ ->> <<- <<- <<-.
rewrite -dec_fw_ok2 /= in dec_fw_ok1.
elim dec_fw_ok1 => -> _ //.
inline{1} (1 2) RH.NonOptHashing.hash.
rcondf{1} 2; first auto; smt().
rcondf{1} 4; first auto; smt().
auto => &1 &2 |> _ _  st2_eq st1_eq mp_exp1_eq mp_exp2_eq
        mp_exp3_eq _ _ @/hybrid_hash_ddh2_rel1 /= [#] ->> ->>.
rewrite /= oget_some /= in st1_eq.
rewrite /= oget_some /= in st2_eq.
elim st1_eq => [#] ->> [#] ->> ->>.
elim st2_eq => -> ->.
progress.
by rewrite mp_exp3_eq oget_some; smt(gen_logK).
by rewrite (HybridHashDDH2Rel2 _ pt1 pt2)
           /hybrid_hash_ddh2_rel2 /=
           mp_exp2_eq oget_some mp_exp3_eq oget_some.
auto.
auto.
case
  (exists (pt1 pt2 : port),
   hybrid_hash_ddh2_rel2
   {|hybrid_hash_ddh2_rel_st_x1 = DDH_Adv.x1{2};
     hybrid_hash_ddh2_rel_st_x2 = DDH_Adv.x2{2};
     hybrid_hash_ddh2_rel_st_x3 = DDH_Adv.x3{2};
     hybrid_hash_ddh2_rel_st_rss =
     KEHybridHashingAdv.KEHybridHash.st{1};
     hybrid_hash_ddh2_rel_st_hs = DDH_Adv.KEDDH.st{2}|}
   pt1 pt2).
elim* => pt1 pt2.
sp 3 3.
if => //.
inline KEHybridHashingAdv(RH.NonOptHashing).KEHybridHash.parties
       DDH_Adv(Env, Adv).KEDDH.parties.
sp 2 2.
rcondf{1} 1; first auto; smt().
rcondf{1} 1; first auto; smt().
rcondt{1} 1; first auto; smt(is_ke_hybrid_state_wait_req2).
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_ke_ddh_state_wait_req2).
sp 1 1.
if => //.
sp 1 1.
if.
move => &1 &2 [#] dec_ke_req2 dec_ke_req1 dec_wait2 dec_wait1
        ->> _ ->> _ _ _ _ _ _ _ ->> _ _ _ _ _ _ _ _ _ _ _ _ _ _
        @/hybrid_hash_ddh2_rel2 /= [#] ->> ->> _ _.
rewrite -dec_ke_req2 /= in dec_ke_req1.
elim dec_ke_req1 => _ ->>.
rewrite /= oget_some /= in dec_wait1.
elim dec_wait1 => ->> [#] ->> ->> _.
rewrite /= oget_some /= in dec_wait2.
by elim dec_wait2 => _ <-.
auto => &1 &2 |> _ _ st2_eq st1_eq mp_exp1_eq mp_exp2_eq _ _ _ _
        @/hybrid_hash_ddh2_rel2 /= [#] ->> ->> _ _.
rewrite /= oget_some /= in st2_eq.
elim st2_eq => ->> ->>.
rewrite /= oget_some /= in st1_eq.
elim st1_eq => ->> [#] ->> ->> ->>.
progress.
smt(gen_logK).
by rewrite (HybridHashDDH2Rel3 _ pt1 pt2) /hybrid_hash_ddh2_rel3.
auto.
auto.
case
  (exists (pt1 pt2 : port),
   hybrid_hash_ddh2_rel3
   {|hybrid_hash_ddh2_rel_st_x1 = DDH_Adv.x1{2};
     hybrid_hash_ddh2_rel_st_x2 = DDH_Adv.x2{2};
     hybrid_hash_ddh2_rel_st_x3 = DDH_Adv.x3{2};
     hybrid_hash_ddh2_rel_st_rss =
     KEHybridHashingAdv.KEHybridHash.st{1};
     hybrid_hash_ddh2_rel_st_hs = DDH_Adv.KEDDH.st{2}|}
   pt1 pt2).
elim* => pt1 pt2.
sp 3 3.
if => //.
inline KEHybridHashingAdv(RH.NonOptHashing).KEHybridHash.parties
       DDH_Adv(Env, Adv).KEDDH.parties.
sp 2 2.
rcondf{1} 1; first auto; smt().
rcondf{1} 1; first auto; smt().
rcondf{1} 1; first auto; smt().
rcondt{1} 1; first auto; smt(is_ke_hybrid_state_wait_adv2).
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_ke_ddh_state_wait_adv2).
sp 1 1.
if => //.
sp 1 1.
if.
move => &1 &2 [#] dec_fw_ok2 dec_fw_ok1 dec_wait2 dec_wait1
        ->> _ ->> _ _ _ _ _ _ _ ->> _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        @/hybrid_hash_ddh2_rel3 /= [#] ->> ->> _ _.
rewrite -dec_fw_ok2 /= in dec_fw_ok1.
elim dec_fw_ok1 => ->> ->>.
congr. congr.
auto => &1 &2 |> <- /= [#] -> _ dec_wait2 dec_wait1
        mp_exp1_eq mp_exp2_eq _ _ _ _ _
        @/hybrid_hash_ddh2_rel3 /= [#] ->> ->>.
rewrite /= oget_some /= in dec_wait1.
elim dec_wait1 => ->> [#] ->> ->> ->>.
rewrite /= oget_some /= in dec_wait2.
elim dec_wait2 => ->> ->>.
progress.
smt(gen_logK).
rewrite (HybridHashDDH2Rel4 _ pt1 pt2) /#.
auto.
auto.
case
  (exists (pt1 pt2 : port),
   hybrid_hash_ddh2_rel4
   {|hybrid_hash_ddh2_rel_st_x1 = DDH_Adv.x1{2};
     hybrid_hash_ddh2_rel_st_x2 = DDH_Adv.x2{2};
     hybrid_hash_ddh2_rel_st_x3 = DDH_Adv.x3{2};
     hybrid_hash_ddh2_rel_st_rss =
     KEHybridHashingAdv.KEHybridHash.st{1};
     hybrid_hash_ddh2_rel_st_hs = DDH_Adv.KEDDH.st{2}|}
   pt1 pt2).
elim* => pt1 pt2.
sp 3 3.
if => //.
inline KEHybridHashingAdv(RH.NonOptHashing).KEHybridHash.parties
       DDH_Adv(Env, Adv).KEDDH.parties.
sp 2 2.
rcondf{1} 1; first auto; smt().
rcondf{1} 1; first auto; smt().
rcondf{1} 1; first auto; smt().
rcondf{1} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
auto.
exfalso => &1 &2 [#] _ _ _ _ _ _ _ _ _ _ _ _ []; smt().
qed.

local lemma KEHybridHashingAdv_NonOptHashing_DDH2_DDH_Adv
            (func' adv' : addr) &m :
  DDH_Adv.func{m} = func' => DDH_Adv.adv{m} = adv' =>
  Pr[RH.GNonOptHashing(KEHybridHashingAdv).main() @ &m : res] =
  Pr[DDH2(DDH_Adv(Env, Adv)).main() @ &m : res].
proof.
move => func'_eq adv'_eq.
byequiv => //.
proc.
inline RH.NonOptHashing.init
       RH.GNonOptHashing(KEHybridHashingAdv).HA.main
       RH.NonOptHashing.rhash RH.NonOptHashing.hash
       Exper(MI(KEHybridHashingAdv(RH.NonOptHashing).KEHybridHash,
                Adv),
             Env).main
       MI(KEHybridHashingAdv(RH.NonOptHashing).KEHybridHash, Adv).init
       KEHybridHashingAdv(RH.NonOptHashing).KEHybridHash.init
       DDH_Adv(Env, Adv).main
       Exper(MI(DDH_Adv(Env, Adv).KEDDH, Adv), Env).main
       MI(DDH_Adv(Env, Adv).KEDDH, Adv).init
       DDH_Adv(Env, Adv).KEDDH.init.
rcondt{1} 4; first auto; smt(mem_empty).
rcondt{1} 7; first auto; smt(mem_set mem_empty).
rcondt{1} 10; first auto; smt(mem_set mem_empty).
wp.
seq 10 9 :
  (={DDH_Adv.func, DDH_Adv.adv} /\
   DDH_Adv.func{1} = func' /\ DDH_Adv.adv{1} = adv' /\
   RH.NonOptHashing.mp{1}.[exp1] = Some u1{2} /\
   RH.NonOptHashing.mp{1}.[exp2] = Some u2{2} /\
   RH.NonOptHashing.mp{1}.[exp3] = Some u3{2} /\
   DDH_Adv.x1{2} = g ^ u1{2} /\
   DDH_Adv.x2{2} = g ^ u2{2} /\
   DDH_Adv.x3{2} = g ^ u3{2}).
auto; progress.
by rewrite get_setE /= get_setE /= get_setE.
by rewrite get_setE /= get_setE.
by rewrite get_setE.
seq 15 15 :
  (RH.NonOptHashing.mp{1}.[exp1] = Some u1{2} /\
   RH.NonOptHashing.mp{1}.[exp2] = Some u2{2} /\
   RH.NonOptHashing.mp{1}.[exp3] = Some u3{2} /\
   DDH_Adv.x1{2} = g ^ u1{2} /\
   DDH_Adv.x2{2} = g ^ u2{2} /\
   DDH_Adv.x3{2} = g ^ u3{2} /\
   ={func, adv, in_guard, MI.func, MI.adv, MI.in_guard,
     DDH_Adv.func, DDH_Adv.adv} /\
   func{1} = func' /\ adv{1} = adv' /\ in_guard{1} = fset1 adv_fw_pi /\
   DDH_Adv.func{1} = func' /\ DDH_Adv.adv{1} = adv' /\
   ={self, adv}(KEHybridHashingAdv.KEHybridHash, DDH_Adv.KEDDH) /\
   DDH_Adv.KEDDH.self{2} = MI.func{1} /\
   DDH_Adv.KEDDH.adv{2} = MI.adv{1} /\
   ={glob Adv} /\
   KEHybridHashingAdv.KEHybridHash.st{1} = KEHybridStateWaitReq1 /\
   DDH_Adv.KEDDH.st{2} = KEDDHStateWaitReq1).
call (_ : true).
auto.
call
  (_ :
   RH.NonOptHashing.mp{1}.[exp1] = Some (log DDH_Adv.x1{2}) /\
   RH.NonOptHashing.mp{1}.[exp2] = Some (log DDH_Adv.x2{2}) /\
   RH.NonOptHashing.mp{1}.[exp3] = Some (log DDH_Adv.x3{2}) /\
   ={MI.func, MI.adv, MI.in_guard} /\
   ={self, adv}(KEHybridHashingAdv.KEHybridHash, DDH_Adv.KEDDH) /\
   DDH_Adv.KEDDH.self{2} = MI.func{1} /\
   DDH_Adv.KEDDH.adv{2} = MI.adv{1} /\
   ={glob Adv} /\
   hybrid_hash_ddh2_rel
   {|hybrid_hash_ddh2_rel_st_x1 = DDH_Adv.x1{2};
     hybrid_hash_ddh2_rel_st_x2 = DDH_Adv.x2{2};
     hybrid_hash_ddh2_rel_st_x3 = DDH_Adv.x3{2};
     hybrid_hash_ddh2_rel_st_rss =
     KEHybridHashingAdv.KEHybridHash.st{1};
     hybrid_hash_ddh2_rel_st_hs = DDH_Adv.KEDDH.st{2}|}).
proc.
sp 2 2.
if => //.
inline MI(KEHybridHashingAdv(RH.NonOptHashing).KEHybridHash, Adv).loop
       MI(DDH_Adv(Env, Adv).KEDDH, Adv).loop.
sp 3 3; wp.
while
  (={not_done} /\ ={m0, r0} /\
   RH.NonOptHashing.mp{1}.[exp1] = Some (log DDH_Adv.x1{2}) /\
   RH.NonOptHashing.mp{1}.[exp2] = Some (log DDH_Adv.x2{2}) /\
   RH.NonOptHashing.mp{1}.[exp3] = Some (log DDH_Adv.x3{2}) /\
   ={MI.func, MI.adv, MI.in_guard} /\
   ={self, adv}(KEHybridHashingAdv.KEHybridHash, DDH_Adv.KEDDH) /\
   DDH_Adv.KEDDH.self{2} = MI.func{1} /\
   DDH_Adv.KEDDH.adv{2} = MI.adv{1} /\
   ={glob Adv} /\
   hybrid_hash_ddh2_rel
   {|hybrid_hash_ddh2_rel_st_x1 = DDH_Adv.x1{2};
     hybrid_hash_ddh2_rel_st_x2 = DDH_Adv.x2{2};
     hybrid_hash_ddh2_rel_st_x3 = DDH_Adv.x3{2};
     hybrid_hash_ddh2_rel_st_rss =
     KEHybridHashingAdv.KEHybridHash.st{1};
     hybrid_hash_ddh2_rel_st_hs = DDH_Adv.KEDDH.st{2}|}).
sp 2 2.
if => //.
wp.
call KEHybridHashingAdv_NonOptHashing_KEDDH_DDH2_invoke.
auto.
wp.
call (_ : true).
auto.
auto.
auto.
auto; progress.
by rewrite log_genK.
by rewrite log_genK.
by rewrite log_genK.
by rewrite HybridHashDDH2Rel0.
qed.

(* relation between state of KEHybridHash and map of
   RH.OptHashing *)

type hybrid_hash_rel_st = {
  hybrid_hash_rel_st_rss : ke_hybrid_state;
  hybrid_hash_rel_st_map : (exp_names, exp) fmap;
}.

pred hybrid_hash_rel0 (st : hybrid_hash_rel_st) =
  st.`hybrid_hash_rel_st_rss = KEHybridStateWaitReq1 /\
  st.`hybrid_hash_rel_st_map.[exp1] = None /\
  st.`hybrid_hash_rel_st_map.[exp2] = None /\
  st.`hybrid_hash_rel_st_map.[exp3] = None.

pred hybrid_hash_rel1 (st : hybrid_hash_rel_st, pt1 pt2 : port, q1 : exp) =
  st.`hybrid_hash_rel_st_rss = KEHybridStateWaitAdv1 (pt1, pt2, q1) /\
  st.`hybrid_hash_rel_st_map.[exp1] = Some q1 /\
  st.`hybrid_hash_rel_st_map.[exp2] = None /\
  st.`hybrid_hash_rel_st_map.[exp3] = None.

pred hybrid_hash_rel2 (st : hybrid_hash_rel_st, pt1 pt2 : port, q1 q2 q3 : exp) =
  st.`hybrid_hash_rel_st_rss = KEHybridStateWaitReq2 (pt1, pt2, q1, q2, q3) /\
  st.`hybrid_hash_rel_st_map.[exp1] = Some q1 /\
  st.`hybrid_hash_rel_st_map.[exp2] = Some q2 /\
  st.`hybrid_hash_rel_st_map.[exp3] = Some q3.

pred hybrid_hash_rel3 (st : hybrid_hash_rel_st, pt1 pt2 : port, q1 q2 q3 : exp) =
  st.`hybrid_hash_rel_st_rss = KEHybridStateWaitAdv2 (pt1, pt2, q1, q2, q3) /\
  st.`hybrid_hash_rel_st_map.[exp1] = Some q1 /\
  st.`hybrid_hash_rel_st_map.[exp2] = Some q2 /\
  st.`hybrid_hash_rel_st_map.[exp3] = Some q3.

pred hybrid_hash_rel4 (st : hybrid_hash_rel_st, pt1 pt2 : port, q1 q2 q3 : exp) =
  st.`hybrid_hash_rel_st_rss = KEHybridStateFinal (pt1, pt2, q1, q2, q3) /\
  st.`hybrid_hash_rel_st_map.[exp1] = Some q1 /\
  st.`hybrid_hash_rel_st_map.[exp2] = Some q2 /\
  st.`hybrid_hash_rel_st_map.[exp3] = Some q3.

inductive hybrid_hash_rel (st : hybrid_hash_rel_st) =
    HybridHashRel0 of (hybrid_hash_rel0 st)
  | HybridHashRel1 (pt1 pt2 : port, q1 : exp) of
      (hybrid_hash_rel1 st pt1 pt2 q1)
  | HybridHashRel2 (pt1 pt2 : port, q1 q2 q3 : exp) of
      (hybrid_hash_rel2 st pt1 pt2 q1 q2 q3)
  | HybridHashRel3 (pt1 pt2 : port, q1 q2 q3 : exp) of
      (hybrid_hash_rel3 st pt1 pt2 q1 q2 q3)
  | HybridHashRel4 (pt1 pt2 : port, q1 q2 q3 : exp) of
      (hybrid_hash_rel4 st pt1 pt2 q1 q2 q3).

local lemma KEHybrid_KEHybridHash_OptHashing_invoke :
  equiv
  [KEHybrid.invoke ~
   KEHybridHashingAdv(RH.OptHashing).KEHybridHash.invoke :
   ={m} /\
   ={self, adv, st}(KEHybrid, KEHybridHashingAdv.KEHybridHash) /\
   hybrid_hash_rel
   {|hybrid_hash_rel_st_rss = KEHybrid.st{1};
     hybrid_hash_rel_st_map = RH.OptHashing.mp{2}|} ==>
   ={res} /\
   ={self, adv, st}(KEHybrid, KEHybridHashingAdv.KEHybridHash) /\
   hybrid_hash_rel
   {|hybrid_hash_rel_st_rss = KEHybrid.st{1};
     hybrid_hash_rel_st_map = RH.OptHashing.mp{2}|}].
proof.
proc.
case
  (hybrid_hash_rel0
   {|hybrid_hash_rel_st_rss = KEHybrid.st{1};
     hybrid_hash_rel_st_map = RH.OptHashing.mp{2}|}).
sp 3 3.
if => //.
inline KEHybrid.parties
       KEHybridHashingAdv(RH.OptHashing).KEHybridHash.parties.
sp 2 2.
rcondt{1} 1; first auto; smt().
rcondt{2} 1; first auto; smt().
if => //.
sp 1 1.
if => //.
move => &1 &2 /> <- //.
wp.
inline RH.OptHashing.hash.
rcondt{2} 2; first auto; smt().
auto => &1 &2 /> <-.
progress.
by rewrite get_setE /= oget_some.
by rewrite get_setE /= oget_some.
rewrite (HybridHashRel1 _ pt10{2} pt20{2} q1L)
        /hybrid_hash_rel1 /=.
by rewrite 3!get_setE.
auto.
auto.
case
  (exists (pt1 pt2 : port) (q1 : exp),
   hybrid_hash_rel1
   {|hybrid_hash_rel_st_rss = KEHybrid.st{1};
     hybrid_hash_rel_st_map = RH.OptHashing.mp{2}|}
   pt1 pt2 q1).
elim* => pt1 pt2 q1.
sp 3 3.
if => //.
inline KEHybrid.parties
       KEHybridHashingAdv(RH.OptHashing).KEHybridHash.parties.
sp 2 2.
rcondf{1} 1; first auto; smt().
rcondt{1} 1; first auto; smt(is_ke_hybrid_state_wait_adv1).
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_ke_hybrid_state_wait_adv1).
sp 1 1.
if => //.
sp 1 1.
if.
move => &1 &2 [#] dec_fw_ok2 dec_fw_ok1 dec_wait2 dec_wait1
        ->> _ ->> _ _ _ _ _ _ _ ->> <<- <<- <<-.
rewrite -dec_fw_ok2 /= in dec_fw_ok1.
by elim dec_fw_ok1 => ->.
wp.
inline RH.OptHashing.hash.
rcondt{2} 2; first auto; smt().
rcondt{2} 5; first auto; smt(mem_set).
auto => &1 &2 |> _ _ ^ st2_eq <- /= [#] -> -> -> _ _
        @/hybrid_hash_rel1 /= [#] ->>.
progress.
by rewrite get_setE /= oget_some.
by rewrite get_setE /= oget_some.
by rewrite get_setE /= oget_some.
rewrite (HybridHashRel2 _ pt10{2} pt20{2} q1 q2L q3L)
        /hybrid_hash_rel2 /=.
rewrite 6!get_setE /= /#.
auto.
auto.
case
  (exists (pt1 pt2 : port) (q1 q2 q3 : exp),
   hybrid_hash_rel2
   {|hybrid_hash_rel_st_rss = KEHybrid.st{1};
     hybrid_hash_rel_st_map = RH.OptHashing.mp{2}|}
   pt1 pt2 q1 q2 q3).
elim* => pt1 pt2 q1 q2 q3.
sp 3 3.
if => //.
inline KEHybrid.parties
       KEHybridHashingAdv(RH.OptHashing).KEHybridHash.parties.
sp 2 2.
rcondf{1} 1; first auto; smt().
rcondf{1} 1; first auto; smt().
rcondt{1} 1; first auto; smt(is_ke_hybrid_state_wait_req2).
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_ke_hybrid_state_wait_req2).
auto => &1 &2 |> _ _ _ @/hybrid_hash_rel2 /= [#].
progress.
rewrite oget_some (HybridHashRel3 _ pt1 pt2 q1 q2 q3)
        /hybrid_hash_rel3 /= /#.
case
  (exists (pt1 pt2 : port) (q1 q2 q3 : exp),
   hybrid_hash_rel3
   {|hybrid_hash_rel_st_rss = KEHybrid.st{1};
     hybrid_hash_rel_st_map = RH.OptHashing.mp{2}|}
   pt1 pt2 q1 q2 q3).
elim* => pt1 pt2 q1 q2 q3.
sp 3 3.
if => //.
inline KEHybrid.parties
       KEHybridHashingAdv(RH.OptHashing).KEHybridHash.parties.
sp 2 2.
rcondf{1} 1; first auto; smt().
rcondf{1} 1; first auto; smt().
rcondf{1} 1; first auto; smt().
rcondt{1} 1; first auto; smt(is_ke_hybrid_state_wait_adv2).
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_ke_hybrid_state_wait_adv2).
auto => &1 &2 |> _ _ _ @/hybrid_hash_rel3 /= [#].
progress.
rewrite oget_some (HybridHashRel4 _ pt1 pt2 q1 q2 q3)
        /hybrid_hash_rel4 /= /#.
case
  (exists (pt1 pt2 : port) (q1 q2 q3 : exp),
   hybrid_hash_rel4
   {|hybrid_hash_rel_st_rss = KEHybrid.st{1};
     hybrid_hash_rel_st_map = RH.OptHashing.mp{2}|}
   pt1 pt2 q1 q2 q3).
elim* => pt1 pt2 q1 q2 q3.
sp 3 3.
if => //.
inline KEHybrid.parties
       KEHybridHashingAdv(RH.OptHashing).KEHybridHash.parties.
sp 2 2.
rcondf{1} 1; first auto; smt().
rcondf{1} 1; first auto; smt().
rcondf{1} 1; first auto; smt().
rcondf{1} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
auto.
exfalso => &1 &2 [#] _ _ _ _ []; smt().
qed.

local lemma Exper_KEHybrid_KEHybridHashingAdv_OptHashing
            (func' adv' : addr) &m :
  DDH_Adv.func{m} = func' => DDH_Adv.adv{m} = adv' =>
  Pr[Exper(MI(KEHybrid, Adv), Env).main
       (func', adv', fset1 adv_fw_pi) @ &m : res] =
  Pr[RH.GOptHashing(KEHybridHashingAdv).main() @ &m : res].
proof.
move => func'_eq adv'_eq.
byequiv => //.
proc.
inline MI(KEHybrid, Adv).init
       KEHybrid.init
       RH.OptHashing.init
       RH.GOptHashing(KEHybridHashingAdv).HA.main
       RH.OptHashing.rhash
       Exper(MI(KEHybridHashingAdv(RH.OptHashing).KEHybridHash,
                Adv),
             Env).main
       KEHybridHashingAdv(RH.OptHashing).KEHybridHash.init
       MI(KEHybridHashingAdv(RH.OptHashing).KEHybridHash, Adv).init.
wp.
seq 12 19 :
  (={func, adv, in_guard, MI.func, MI.adv, MI.in_guard} /\
   ={self, adv, st}(KEHybrid, KEHybridHashingAdv.KEHybridHash) /\
   func' = func{1} /\ func{1} = MI.func{1} /\
   KEHybrid.self{1} = func{1} /\
   adv' = adv{1} /\ adv{1} = MI.adv{1} /\
   KEHybrid.adv{1} = adv{1} /\
   KEHybrid.st{1} = KEHybridStateWaitReq1 /\
   RH.OptHashing.mp{2} = empty /\
   ={glob Adv}).
call (_ : true).
auto; smt().
call
  (_ :
   ={MI.func, MI.adv, MI.in_guard} /\
   ={self, adv, st}(KEHybrid, KEHybridHashingAdv.KEHybridHash) /\
   KEHybrid.self{1} = MI.func{1} /\ KEHybrid.adv{1} = MI.adv{1} /\
   ={glob Adv} /\
   hybrid_hash_rel
   {|hybrid_hash_rel_st_rss = KEHybrid.st{1};
     hybrid_hash_rel_st_map = RH.OptHashing.mp{2}|}).
proc.
sp 2 2.
if => //.
inline MI(KEHybrid, Adv).loop
       MI(KEHybridHashingAdv(RH.OptHashing).KEHybridHash, Adv).loop.
sp 3 3; wp.
while
  (={not_done} /\ ={m0, r0} /\
   ={MI.func, MI.adv, MI.in_guard} /\
   ={self, adv, st}(KEHybrid, KEHybridHashingAdv.KEHybridHash) /\
   KEHybrid.self{1} = MI.func{1} /\ KEHybrid.adv{1} = MI.adv{1} /\
   ={glob Adv} /\
   hybrid_hash_rel
   {|hybrid_hash_rel_st_rss = KEHybrid.st{1};
     hybrid_hash_rel_st_map = RH.OptHashing.mp{2}|}).
sp 2 2.
if => //.
wp.
call KEHybrid_KEHybridHash_OptHashing_invoke.
auto.
wp.
call (_ : true).
auto.
auto.
auto.
auto; progress.
rewrite HybridHashRel0 /hybrid_hash_rel0 /=; smt(emptyE).
qed.

(* relational invariant for connecting Exper(MI(KEHybrid, Adv), Env)
   and Exper(MI(KEIdeal, KESim(Adv)), Env) *)

type ke_hybrid_ideal_sim_rel_st = {
  ke_hybrid_ideal_sim_rel_st_func : addr;
  ke_hybrid_ideal_sim_rel_st_adv : addr;
  ke_hybrid_ideal_sim_rel_st_hs : ke_hybrid_state;
  ke_hybrid_ideal_sim_rel_st_is : ke_ideal_state;
  ke_hybrid_ideal_sim_rel_st_ss : ke_sim_state
}.

pred ke_hybrid_ideal_sim_rel0 (st : ke_hybrid_ideal_sim_rel_st) =
  st.`ke_hybrid_ideal_sim_rel_st_hs = KEHybridStateWaitReq1 /\
  st.`ke_hybrid_ideal_sim_rel_st_is = KEIdealStateWaitReq1 /\
  st.`ke_hybrid_ideal_sim_rel_st_ss = KESimStateWaitReq1.

pred ke_hybrid_ideal_sim_rel1
     (st : ke_hybrid_ideal_sim_rel_st, pt1 pt2 : port, q1 : exp) =
  ! st.`ke_hybrid_ideal_sim_rel_st_func <= pt1.`1 /\
  ! st.`ke_hybrid_ideal_sim_rel_st_func <= pt2.`1 /\
  ! st.`ke_hybrid_ideal_sim_rel_st_adv <= pt1.`1 /\
  ! st.`ke_hybrid_ideal_sim_rel_st_adv <= pt2.`1 /\
  st.`ke_hybrid_ideal_sim_rel_st_hs = KEHybridStateWaitAdv1 (pt1, pt2, q1) /\
  st.`ke_hybrid_ideal_sim_rel_st_is = KEIdealStateWaitSim1 (pt1, pt2) /\
  st.`ke_hybrid_ideal_sim_rel_st_ss =
  KESimStateWaitAdv1(st.`ke_hybrid_ideal_sim_rel_st_func, q1).

pred ke_hybrid_ideal_sim_rel2
     (st : ke_hybrid_ideal_sim_rel_st, pt1 pt2 : port, q1 q2 q3 : exp) =
  ! st.`ke_hybrid_ideal_sim_rel_st_func <= pt1.`1 /\
  ! st.`ke_hybrid_ideal_sim_rel_st_func <= pt2.`1 /\
  ! st.`ke_hybrid_ideal_sim_rel_st_adv <= pt1.`1 /\
  ! st.`ke_hybrid_ideal_sim_rel_st_adv <= pt2.`1 /\
  st.`ke_hybrid_ideal_sim_rel_st_hs = KEHybridStateWaitReq2 (pt1, pt2, q1, q2, q3) /\
  st.`ke_hybrid_ideal_sim_rel_st_is = KEIdealStateWaitReq2 (pt1, pt2, q3) /\
  st.`ke_hybrid_ideal_sim_rel_st_ss =
  KESimStateWaitReq2(st.`ke_hybrid_ideal_sim_rel_st_func, q1, q2).

pred ke_hybrid_ideal_sim_rel3
     (st : ke_hybrid_ideal_sim_rel_st, pt1 pt2 : port, q1 q2 q3 : exp) =
  ! st.`ke_hybrid_ideal_sim_rel_st_func <= pt1.`1 /\
  ! st.`ke_hybrid_ideal_sim_rel_st_func <= pt2.`1 /\
  ! st.`ke_hybrid_ideal_sim_rel_st_adv <= pt1.`1 /\
  ! st.`ke_hybrid_ideal_sim_rel_st_adv <= pt2.`1 /\
  st.`ke_hybrid_ideal_sim_rel_st_hs = KEHybridStateWaitAdv2 (pt1, pt2, q1, q2, q3) /\
  st.`ke_hybrid_ideal_sim_rel_st_is = KEIdealStateWaitSim2 (pt1, pt2, q3) /\
  st.`ke_hybrid_ideal_sim_rel_st_ss =
  KESimStateWaitAdv2(st.`ke_hybrid_ideal_sim_rel_st_func, q1, q2).

pred ke_hybrid_ideal_sim_rel4
     (st : ke_hybrid_ideal_sim_rel_st, pt1 pt2 : port, q1 q2 q3 : exp) =
  ! st.`ke_hybrid_ideal_sim_rel_st_func <= pt1.`1 /\
  ! st.`ke_hybrid_ideal_sim_rel_st_func <= pt2.`1 /\
  ! st.`ke_hybrid_ideal_sim_rel_st_adv <= pt1.`1 /\
  ! st.`ke_hybrid_ideal_sim_rel_st_adv <= pt2.`1 /\
  st.`ke_hybrid_ideal_sim_rel_st_hs = KEHybridStateFinal (pt1, pt2, q1, q2, q3) /\
  st.`ke_hybrid_ideal_sim_rel_st_is = KEIdealStateFinal (pt1, pt2, q3) /\
  st.`ke_hybrid_ideal_sim_rel_st_ss =
  KESimStateFinal(st.`ke_hybrid_ideal_sim_rel_st_func, q1, q2).

inductive ke_hybrid_ideal_sim_rel (st : ke_hybrid_ideal_sim_rel_st) =
    KEHybridIdealSimRel0 of (ke_hybrid_ideal_sim_rel0 st)
  | KEHybridIdealSimRel1 (pt1 pt2 : port, q1 : exp) of
      (ke_hybrid_ideal_sim_rel1 st pt1 pt2 q1)
  | KEHybridIdealSimRel2 (pt1 pt2 : port, q1 q2 q3 : exp) of
      (ke_hybrid_ideal_sim_rel2 st pt1 pt2 q1 q2 q3)
  | KEHybridIdealSimRel3 (pt1 pt2 : port, q1 q2 q3 : exp) of
      (ke_hybrid_ideal_sim_rel3 st pt1 pt2 q1 q2 q3)
  | KEHybridIdealSimRel4 (pt1 pt2 : port, q1 q2 q3 : exp) of
      (ke_hybrid_ideal_sim_rel4 st pt1 pt2 q1 q2 q3).

local module MI_KEHybrid_AfterAdv = {
  proc after_adv(r : msg option) : msg option = {
    var not_done : bool <- true; var m : msg;
    var mod : mode; var pt1, pt2 : port;
    var addr1 : addr; var n1 : int; var u : univ;
    m <- oget r; (mod, pt1, pt2, u) <- m;
    (addr1, n1) <- pt1;
    if (MI.adv <= addr1 \/ mod = Dir) {
      r <- None; not_done <- false;
    }
    elif (! MI.func <= addr1) {
      not_done <- false;
    }
    while (not_done) {
      (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
      if (MI.func <= addr1) {
        r <@ KEHybrid.invoke(m);
        if (r = None) {
          not_done <- false;
        } else {
          m <- oget r; (mod, pt1, pt2, u) <- m;
          (addr1, n1) <- pt1;
          if (MI.func <= addr1) {
            r <- None; not_done <- false;
          }
          elif (mod = Dir) {
            not_done <- false;
            if (MI.adv <= addr1) {
              r <- None;
            }
          }
          elif (addr1 <> MI.adv \/ n1 = 0) {
            r <- None; not_done <- false;
          }
        }
      }
      else {
        r <@ Adv.invoke(m);
        if (r = None) {
          not_done <- false;
        } else {
          m <- oget r; (mod, pt1, pt2, u) <- m;
          (addr1, n1) <- pt1;
          if (MI.adv <= addr1 \/ mod = Dir) {
            r <- None; not_done <- false;
          }
          elif (! MI.func <= addr1) {
            not_done <- false;
          }
        }
      }
    }
    return r;
  }
}.

local module MI_KEIdeal_KESim_AfterAdv = {
  proc after_adv(r : msg option) : msg option = {
    var not_done : bool <- true; var not_done' : bool <- true;
    var m : msg; var mod : mode; var pt1, pt2, pt1', pt2' : port;
    var addr, addr1, addr2 : addr; var n1 : int;
    var u : univ; var q1, q2 : exp;
    m <- oget r; (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
    if (mod = Dir \/ KESim.self <= addr1) {
      r <- None;
    }
    elif (is_ke_sim_state_wait_adv1 KESim.st) {
      (addr, q1) <- oget (dec_ke_sim_state_wait_adv1 KESim.st);
      if (addr <= addr1) {
        r <- None;
        if (Fwd1.is_fw_ok m) {
          (addr1, addr2) <- oget (Fwd1.dec_fw_ok m);
          if (addr1 = addr ++ [1]) {
            q2 <$ dexp;
            r <- Some (ke_sim_rsp addr KESim.self);
            KESim.st <- KESimStateWaitReq2 (addr, q1, q2);
          }
        }
      }
    }
    elif (is_ke_sim_state_wait_adv2 KESim.st) {
      (addr, q1, q2) <- oget (dec_ke_sim_state_wait_adv2 KESim.st);
      if (addr <= addr1) {
        r <- None;
        if (Fwd2.is_fw_ok m) {
          (addr1, addr2) <- oget (Fwd2.dec_fw_ok m);
          if (addr1 = addr ++ [2]) {
            r <- Some (ke_sim_rsp addr KESim.self);
            KESim.st <- KESimStateFinal (addr, q1, q2);
          }
        }
      }
    }
    elif (is_ke_sim_state_wait_req2 KESim.st) {
      (addr, q1, q2) <- oget (dec_ke_sim_state_wait_req2 KESim.st);
      if (addr <= addr1) {
        r <- None;
      }
    }
    if (r = None) {
      not_done <- false;
    }
    else {
      m <- oget r; (mod, pt1, pt2, u) <- m;
      (addr1, n1) <- pt1;
      if (MI.adv <= addr1 \/ mod = Dir) {
        r <- None; not_done <- false;
      }
      elif (! MI.func <= addr1) {
        not_done <- false;
      }
    }
    while (not_done) {
      (mod, pt1, pt2, u) <- m;
      (addr1, n1) <- pt1;
      if (MI.func <= addr1) {
        r <@ KEIdeal.invoke(m);
        if (r = None) {
          not_done <- false;
        }
        else {
          m <- oget r; (mod, pt1, pt2, u) <- m;
          (addr1, n1) <- pt1;
          if (MI.func <= addr1) {
            r <- None; not_done <- false;
          }
          elif (mod = Dir) {
            not_done <- false;
            if (MI.adv <= addr1) {
              r <- None;
            }
          }
          elif (addr1 <> MI.adv \/ n1 = 0) {
            r <- None; not_done <- false;
          }
        }
      } else {
        r <@ KESim(Adv).invoke(m);
        if (r = None) {
          not_done <- false;
        } else {
          m <- oget r; (mod, pt1, pt2, u) <- m;
          (addr1, n1) <- pt1;
          if (MI.adv <= addr1 \/ mod = Dir) {
            r <- None; not_done <- false;
          }
          elif (! MI.func <= addr1) {
            not_done <- false;
          }
        }
      }
    }
    return r;
  }
}.

local lemma MI_KEHybrid_KEIdeal_KESim_after_adv_1
            (pt1' pt2' : port, q1' : exp) :
  equiv
  [MI_KEHybrid_AfterAdv.after_adv ~
   MI_KEIdeal_KESim_AfterAdv.after_adv :
   ={r} /\ r{1} <> None /\ ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   KEHybrid.self{1} = MI.func{1} /\ KEHybrid.adv{1} = MI.adv{1} /\
   KEIdeal.self{2} = MI.func{1} /\ KEIdeal.adv{2} = MI.adv{1} /\
   KESim.self{2} = MI.adv{1} /\ KESim.adv{2} = [] /\ ={glob Adv} /\
   ke_hybrid_ideal_sim_rel1
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2};|}
   pt1' pt2' q1' ==>
   ={res, glob Adv} /\
   ke_hybrid_ideal_sim_rel
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2};|}].
proof.
proc.
sp 4 5.
if; first smt().
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondt{2} 2; first auto.
auto; progress; by apply (KEHybridIdealSimRel1 _ pt1' pt2' q1').
rcondt{2} 1; first auto; smt(is_ke_sim_state_wait_adv1).
sp 0 1.
case ((MI.func <= addr1){1}).
rcondf{1} 1; first auto.
rcondt{2} 1; first auto.
move => |> &hr dec_sim_state <- /= [#] -> -> _ _ _ _ _
        [] /= [#] _ [#] _ _ _ _ _ ->>.
rewrite /= oget_some /= in dec_sim_state.
elim dec_sim_state => -> _ //.
rcondt{1} 1; first auto.
sp 2 1.
rcondt{1} 1; first auto.
inline{1} (1) KEHybrid.invoke.
sp 4 0.
case ((KEHybrid.self ++ [1] = addr10 /\ Fwd1.is_fw_ok m){1}).
rcondt{1} 1; first auto.
move => |> &hr _ <- /= [#] -> -> -> _ _ _ _ _ /negb_or [#]
        _ /not_dir -> /=.
smt(le_refl).
inline{1} (1) KEHybrid.parties.
rcondf{1} 3; first auto; smt().
rcondt{1} 3; first auto; smt(is_ke_hybrid_state_wait_adv1).
rcondt{1} 4; first auto.
rcondt{1} 5; first auto.
move => |> &hr _ <- /= [#] -> -> -> -> _ _ _ _ /negb_or [#]
        _ /not_dir.
rewrite /is_fw_ok /dec_fw_ok /=.
case
  (mod{m} = Dir \/ n1{m} <> 1 \/ pt2{m}.`2 <> adv_fw_pi \/
   u0{hr} <> UnivUnit) => //.
rcondf{1} 11; first auto.
rcondf{1} 14; first auto.
move => |> &hr _ <- /= [#] -> -> -> -> _ _ _ [] //.
rcondt{1} 14; first auto.
rcondf{1} 15; first auto.
move => |> &hr _ <- /= [#] -> -> _ _ _ _ _ [] //.
rcondf{1} 15; first auto.
rcondt{2} 1; first auto; smt().
rcondt{2} 2; first auto.
move => |> &hr dec_sim_wait <- /= [#] -> <- -> -> ->
        _ _ [] /= _ [#] _ _ _ _ _ ->>.
rewrite /is_fw_ok /dec_fw_ok /=.
case
  (mod{hr} = Dir \/ n1{hr} <> 1 \/ pt2{hr}.`2 <> adv_fw_pi \/
   u{hr} <> UnivUnit) => //.
rewrite /= oget_some /=.
rewrite /= oget_some /= in dec_sim_wait.
elim dec_sim_wait => -> //.
rcondf{2} 5; first auto.
rcondf{2} 8; first auto.
move => |> &hr dec_sim_wait_eq <- /= [#] -> -> _ _ _ _
        pre [] /= _ [#] _ _ _ _ _ ->>.
rewrite /= oget_some /= in dec_sim_wait_eq.
elim dec_sim_wait_eq => -> _ /negb_or [#].
rewrite not_dir.
progress.
rewrite oget_some negb_or /ke_sim_rsp /=.
smt(not_leP inc_sym).
rcondf{2} 8; first auto.
move => |> &hr dec_sim_wait_eq <- /= [#] -> -> _ _ _ _
        pre [] /= _ [#] _ _ _ _ _ ->>.
rewrite /= oget_some /= in dec_sim_wait_eq.
elim dec_sim_wait_eq => ->.
smt(le_refl).
rcondt{2} 8; first auto.
rcondt{2} 10; first auto.
move => |> &hr dec_sim_wait_eq <- /= [#] -> -> _ _ _ _
        pre [] /= _ [#] _ _ _ _ _ ->>.
rewrite /= oget_some /= in dec_sim_wait_eq.
elim dec_sim_wait_eq => ->.
smt(le_refl).
inline{2} (1) KEIdeal.invoke.
rcondt{2} 14; first auto.
move => |> &hr dec_sim_wait_eq <- /= [#] -> -> _ _ _ _
        pre [] /= _ [#] _ _ _ _ _ ->>.
rewrite /= oget_some /= in dec_sim_wait_eq.
elim dec_sim_wait_eq => -> //.
inline{2} (1) KEIdeal.parties.
rcondf{2} 16; first auto; smt().
rcondt{2} 16; first auto; smt(is_ke_ideal_state_wait_sim1).
rcondt{2} 17; first auto.
rcondf{2} 22; first auto.
rcondf{2} 25; first auto.
move => |> &hr _ <- /= [#] -> -> _ _ _ _
        _ [] /= _ [#] _ _ _ _ ->> //.
rcondt{2} 25; first auto.
rcondf{2} 26; first auto.
move => |> &hr _ <- /= [#] -> -> _ _ _ _
        _ [] /= _ [#] _ _ _ _ ->> //.
rcondf{2} 26; first auto.
wp; sp; swap{2} 16 -14; wp; rnd; rnd.
auto => |> &1 &2 addr1R _ dec_hybrid_wait_eq _
        dec_sim_wait_eq <- /= [#] -> -> -> -> -> _
        pre [] /= pt1'_out1 [#] pt2'_out1 pt1'_out2 pt2'_out2
        ->> -> ->>.
rewrite /= oget_some /= in dec_hybrid_wait_eq.
rewrite /= oget_some /= in dec_sim_wait_eq.
elim dec_hybrid_wait_eq => -> [#] -> ->.
elim dec_sim_wait_eq => -> ->.
progress.
rewrite (KEHybridIdealSimRel2 _ pt1' pt2' q1' q2L q3L)
        /ke_hybrid_ideal_sim_rel2 /= oget_some /= /#.
seq 2 0 :
  (r{1} = None /\ r{2} = None /\
   (addr{2} ++ [1] <> m{2}.`2.`1 \/
   ! (Fwd1.is_fw_ok m{2})) /\
   (mod{2}, pt1{2}, pt2{2}, u{2}) = m{2} /\
   (addr1{2}, n1{2}) = pt1{2} /\
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   KEHybrid.self{1} = MI.func{1} /\ KEHybrid.adv{1} = MI.adv{1} /\
   KEIdeal.self{2} = MI.func{1} /\ KEIdeal.adv{2} = MI.adv{1} /\
   KESim.self{2} = MI.adv{1} /\ KESim.adv{2} = [] /\ ={glob Adv} /\
   ke_hybrid_ideal_sim_rel1
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2};|}
   pt1' pt2' q1').
if{1}.
inline KEHybrid.parties.
sp 2 0.
rcondf{1} 1; first auto; smt().
rcondt{1} 1; first auto; smt(is_ke_hybrid_state_wait_adv1).
sp 1 0.
if{1}.
rcondf{1} 2; first auto.
move => |> &hr _ _ <- /= [#] -> -> -> -> -> _ _ _ _ _.
rewrite /is_fw_ok /dec_fw_ok /=.
case
  (mod{m} = Dir \/ n1{m} <> 1 \/ pt2{m}.`2 <> adv_fw_pi \/
   u{m} <> UnivUnit) => //=.
rewrite oget_some /= /#.
auto; progress; smt().
auto; progress; smt().
auto; progress; smt().
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
if{2}.
rcondf{2} 2; first auto.
move => |> &hr [] //.
rewrite /is_fw_ok /dec_fw_ok /=.
case
  (mod{hr} = Dir \/ n1{hr} <> 1 \/ pt2{hr}.`2 <> adv_fw_pi \/
   u{hr} <> UnivUnit) => //.
rewrite {2}oget_some /= /#.
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
auto; progress; by apply (KEHybridIdealSimRel1 _ pt1' pt2' q1').
rcondt{2} 1; first auto.
rcondf{2} 2; first auto.
auto; progress; by apply (KEHybridIdealSimRel1 _ pt1' pt2' q1').
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 1; first auto.
move => |> &hr dec_sim_wait_eq <- /= [#] -> -> _ _ _ _
        pre [] /= _ [#] _ _ _ _ _ ->>.
rewrite /= oget_some /= in dec_sim_wait_eq.
elim dec_sim_wait_eq => //.
rcondf{2} 1; first auto.
rcondf{2} 4; first auto; smt().
rcondt{2} 4; first auto.
move => |> &hr dec_sim_wait_eq <- /= [#] -> -> _ _ _ _
        pre [] //.
rcondf{2} 5; first auto.
auto; progress; by apply (KEHybridIdealSimRel1 _ pt1' pt2' q1').
qed.

local lemma MI_KEHybrid_KEIdeal_KESim_after_adv_2
            (pt1' pt2' : port, q1' q2' q3' : exp) :
  equiv
  [MI_KEHybrid_AfterAdv.after_adv ~
   MI_KEIdeal_KESim_AfterAdv.after_adv :
   ={r} /\ r{1} <> None /\ ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   KEHybrid.self{1} = MI.func{1} /\ KEHybrid.adv{1} = MI.adv{1} /\
   KEIdeal.self{2} = MI.func{1} /\ KEIdeal.adv{2} = MI.adv{1} /\
   KESim.self{2} = MI.adv{1} /\ KESim.adv{2} = [] /\ ={glob Adv} /\
   ke_hybrid_ideal_sim_rel3
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2};|}
   pt1' pt2' q1' q2' q3' ==>
   ={res, glob Adv} /\
   ke_hybrid_ideal_sim_rel
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2};|}].
proof.
proc.
sp 4 5.
if; first smt().
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondt{2} 2; first auto.
auto; progress; by apply (KEHybridIdealSimRel3 _ pt1' pt2' q1' q2' q3').
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_ke_sim_state_wait_adv2).
sp 0 1.
case ((MI.func <= addr1){1}).
rcondf{1} 1; first auto.
rcondt{2} 1; first auto.
move => |> &hr dec_sim_state <- /= [#] -> -> _ _ _ _ _
        [] /= [#] _ [#] _ _ _ _ _ ->>.
rewrite /= oget_some /= in dec_sim_state.
elim dec_sim_state => -> _ //.
rcondt{1} 1; first auto.
sp 2 1.
rcondt{1} 1; first auto.
inline{1} (1) KEHybrid.invoke.
sp 4 0.
case ((KEHybrid.self ++ [2] = addr10 /\ Fwd2.is_fw_ok m){1}).
rcondt{1} 1; first auto.
move => |> &hr _ <- /= [#] -> -> -> _ _ _ _ _ /negb_or [#]
        _ /not_dir -> /=.
smt(le_refl).
inline{1} (1) KEHybrid.parties.
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondt{1} 3; first auto; smt(is_ke_hybrid_state_wait_adv2).
rcondt{1} 4; first auto.
rcondt{1} 5; first auto.
move => |> &hr _ <- /= [#] -> -> -> -> _ _ _ _ /negb_or [#]
        _ /not_dir.
rewrite /is_fw_ok /dec_fw_ok /=.
case
  (mod{m} = Dir \/ n1{m} <> 1 \/ pt2{m}.`2 <> adv_fw_pi \/
   u0{hr} <> UnivUnit) => //.
rcondf{1} 9; first auto.
rcondf{1} 12; first auto.
move => |> &hr _ <- /= [#] -> -> -> -> _ _ _ [] /= _ [#] _ _ _
        -> //.
rcondt{1} 12; first auto.
rcondf{1} 13; first auto.
move => |> &hr _ <- /= [#] -> -> _ _ _ _ _ [] //.
rcondf{1} 13; first auto.
rcondt{2} 1; first auto; smt().
rcondt{2} 2; first auto.
move => |> &hr dec_sim_wait _ <- _ _ [] /= _ [#] _ _ _ _ _ ->>.
rewrite /= oget_some /= in dec_sim_wait.
elim dec_sim_wait => -> [#] _ _.
rewrite /is_fw_ok /dec_fw_ok /=.
case
  (mod0{m} = Dir \/ n10{m} <> 1 \/
   pt20{m}.`2 <> adv_fw_pi \/ u0{m} <> UnivUnit) => //.
rcondf{2} 4; first auto.
rcondf{2} 7; first auto.
move => |> &hr dec_sim_wait_eq <- /= [#] -> -> _ _ _ _
        pre [] /= _ [#] _ _ _ _ _ ->>.
rewrite /= oget_some /= in dec_sim_wait_eq.
elim dec_sim_wait_eq => -> _ /negb_or [#].
rewrite not_dir.
progress.
rewrite oget_some negb_or /ke_sim_rsp /=.
smt(not_leP inc_sym).
rcondf{2} 7; first auto.
move => |> &hr dec_sim_wait_eq <- /= [#] -> -> _ _ _ _
        pre [] /= _ [#] _ _ _ _ _ ->>.
rewrite /= oget_some /= in dec_sim_wait_eq.
elim dec_sim_wait_eq => ->.
smt(le_refl).
rcondt{2} 7; first auto.
rcondt{2} 9; first auto.
move => |> &hr dec_sim_wait_eq <- /= [#] -> -> _ _ _ _
        pre [] /= _ [#] _ _ _ _ _ ->>.
rewrite /= oget_some /= in dec_sim_wait_eq.
elim dec_sim_wait_eq => ->.
smt(le_refl).
inline{2} (1) KEIdeal.invoke.
rcondt{2} 13; first auto.
move => |> &hr dec_sim_wait_eq <- /= [#] -> -> _ _ _ _
        pre [] /= _ [#] _ _ _ _ _ ->>.
rewrite /= oget_some /= in dec_sim_wait_eq.
elim dec_sim_wait_eq => -> //.
inline{2} (1) KEIdeal.parties.
rcondf{2} 15; first auto; smt().
rcondf{2} 15; first auto; smt().
rcondf{2} 15; first auto; smt().
rcondt{2} 15; first auto; smt(is_ke_ideal_state_wait_sim2).
rcondt{2} 16; first auto.
rcondf{2} 20; first auto.
rcondf{2} 23; first auto.
move => |> &hr _ <- /= [#] -> -> _ _ _ _
        _ [] /= _ [#] _ _ _ _ ->> //.
rcondt{2} 23; first auto.
rcondf{2} 24; first auto.
move => |> &hr _ <- /= [#] -> -> _ _ _ _
        _ [] /= _ [#] _ _ _ _ ->> //.
rcondf{2} 24; first auto.
auto => |> &1 &2 dec_sim_wait_eq _ _ _ _ [] /=
        pt1'_out1 [#] pt2'_out1 pt1'_out2 pt2'_out2
        -> -> ->>.
rewrite /= oget_some /= in dec_sim_wait_eq.
elim dec_sim_wait_eq => -> [#] -> ->.
progress; rewrite !oget_some.
rewrite (KEHybridIdealSimRel4 _ pt1' pt2' q1' q2' q3')
        /ke_hybrid_ideal_sim_rel4 /= /#.
seq 2 0 :
  (r{1} = None /\ r{2} = None /\
   (addr{2} ++ [2] <> m{2}.`2.`1 \/
   ! (Fwd2.is_fw_ok m{2})) /\
   (mod{2}, pt1{2}, pt2{2}, u{2}) = m{2} /\
   (addr1{2}, n1{2}) = pt1{2} /\
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   KEHybrid.self{1} = MI.func{1} /\ KEHybrid.adv{1} = MI.adv{1} /\
   KEIdeal.self{2} = MI.func{1} /\ KEIdeal.adv{2} = MI.adv{1} /\
   KESim.self{2} = MI.adv{1} /\ KESim.adv{2} = [] /\ ={glob Adv} /\
   ke_hybrid_ideal_sim_rel3
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2};|}
   pt1' pt2' q1' q2' q3').
if{1}.
inline KEHybrid.parties.
sp 2 0.
rcondf{1} 1; first auto; smt().
rcondf{1} 1; first auto; smt().
rcondf{1} 1; first auto; smt().
rcondt{1} 1; first auto; smt(is_ke_hybrid_state_wait_adv2).
sp 1 0.
if{1}.
rcondf{1} 2; first auto.
move => |> &hr _ _ <- /= [#] -> -> -> -> -> _ _ _ _ _.
rewrite /is_fw_ok /dec_fw_ok /=.
case
  (mod{m} = Dir \/ n1{m} <> 1 \/ pt2{m}.`2 <> adv_fw_pi \/
   u{m} <> UnivUnit) => //=.
rewrite oget_some /= /#.
auto; progress; smt().
auto; progress; smt().
auto; progress; smt().
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
if{2}.
rcondf{2} 2; first auto.
move => |> &hr [] //.
rewrite /is_fw_ok /dec_fw_ok /=.
case
  (mod{hr} = Dir \/ n1{hr} <> 1 \/ pt2{hr}.`2 <> adv_fw_pi \/
   u{hr} <> UnivUnit) => //.
rewrite {2}oget_some /= /#.
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
auto; progress; by apply (KEHybridIdealSimRel3 _ pt1' pt2' q1' q2' q3').
rcondt{2} 1; first auto.
rcondf{2} 2; first auto.
auto; progress; by apply (KEHybridIdealSimRel3 _ pt1' pt2' q1' q2' q3').
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 1; first auto.
move => |> &hr dec_sim_wait_eq <- /= [#] -> -> _ _ _ _
        pre [] /= _ [#] _ _ _ _ _ ->>.
rewrite /= oget_some /= in dec_sim_wait_eq.
elim dec_sim_wait_eq => //.
rcondf{2} 1; first auto.
rcondf{2} 4; first auto; smt().
rcondt{2} 4; first auto.
move => |> &hr dec_sim_wait_eq <- /= [#] -> -> _ _ _ _
        pre [] //.
rcondf{2} 5; first auto.
auto; progress; by apply (KEHybridIdealSimRel3 _ pt1' pt2' q1' q2' q3').
qed.

local lemma MI_KEHybrid_KEIdeal_Sim_invoke :
  equiv
  [MI(KEHybrid, Adv).invoke ~ MI(KEIdeal, KESim(Adv)).invoke :
   ={m} /\ ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\ KEHybrid.self{1} = MI.func{1} /\
   KEHybrid.adv{1} = MI.adv{1} /\ KEIdeal.self{2} = MI.func{1} /\
   KEIdeal.adv{2} = MI.adv{1} /\  KESim.self{2} = MI.adv{1} /\
   KESim.adv{2} = [] /\ ={glob Adv} /\
   ke_hybrid_ideal_sim_rel
     {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
       ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
       ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
       ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
       ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2}|} ==>
   ={res, glob Adv} /\
   ke_hybrid_ideal_sim_rel
     {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
       ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
       ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
       ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
       ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2}|}].
proof.
proc.
case
  (ke_hybrid_ideal_sim_rel0
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2}|}).
sp 2 2.
if => //.
inline MI(KEHybrid, Adv).loop MI(KEIdeal, KESim(Adv)).loop.
sp 3 3.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
sp 2 2.
if => //.
inline{1} (1) KEHybrid.invoke.
inline{2} (1) KEIdeal.invoke.
sp 4 4.
if => //.
progress; smt().
inline{1} (1) KEHybrid.parties.
inline{2} (1) KEIdeal.parties.
rcondt{1} 3; first auto; smt().
rcondt{2} 3; first auto; smt().
sp 2 2.
if => //.
sp 1 1.
if.
move => &1 &2 |> <- //.
rcondf{2} 5; first auto.
rcondf{2} 8; first auto.
move => &hr |> <- /= [#] _ -> ->.
rewrite oget_some /ke_sim_req1 /= /#.
rcondf{2} 8; first auto.
rcondf{2} 8; first auto.
move => &hr |> <- /= [#] _ -> ->.
rewrite oget_some /ke_sim_req1 /=.
smt(ke_pi_uniq).
rcondt{2} 8; first auto.
rcondf{2} 10; first auto.
move => &hr |> <- /= [#] _ -> ->.
rewrite oget_some /ke_sim_req1 /= /#.
sp 0 9.
inline{2} (1) KESim(Adv).invoke.
rcondt{2} 4; first auto.
inline{2} (1) KESim(Adv).loop.
rcondt{2} 7; first auto.
rcondt{2} 7; first auto.
rcondt{2} 8; first auto; smt().
rcondt{2} 8; first auto.
sp 0 8.
rcondf{1} 7; first auto.
rcondf{1} 10; first auto.
progress.
rewrite oget_some /fw_obs /= /#.
rcondf{1} 10; first auto.
rcondf{1} 10; first auto.
progress.
rewrite oget_some /fw_obs /=.
smt(ke_pi_uniq).
rcondt{1} 10; first auto.
rcondf{1} 12; first auto.
progress.
rewrite oget_some /fw_obs /= /#.
rcondf{2} 4; first auto.
rcondt{2} 5; first auto.
rcondf{2} 5; first auto.
progress.
rewrite oget_some /fw_obs /=.
smt(ke_pi_uniq).
seq 11 4 :
  (not_done{1} /\ not_done{2} /\ not_done0{2} /\
   m0{1} = m4{2} /\
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\ KEHybrid.self{1} = MI.func{1} /\
   KEHybrid.adv{1} = MI.adv{1} /\ KEIdeal.self{2} = MI.func{1} /\
   KEIdeal.adv{2} = MI.adv{1} /\  KESim.self{2} = MI.adv{1} /\
   KESim.adv{2} = [] /\ ={glob Adv} /\
   ke_hybrid_ideal_sim_rel1
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2}|}
   pt12{1} pt22{1} q1{1}).
wp; rnd.
auto => |> &1 &2 dec_sim_req1_eq st_R.
rewrite oget_some.
move => enc_ke_sim_req1_eq.
move : dec_sim_req1_eq.
rewrite enc_ke_sim_req1_eq enc_dec_ke_sim_req1.
rewrite oget_some /=.
by move => [#] <<- <<- <<- <<- <- /= [#].
seq 1 1 :
  (r0{1} = r4{2} /\ not_done{1} /\ not_done{2} /\ not_done0{2} /\
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\ KEHybrid.self{1} = MI.func{1} /\
   KEHybrid.adv{1} = MI.adv{1} /\ KEIdeal.self{2} = MI.func{1} /\
   KEIdeal.adv{2} = MI.adv{1} /\ KESim.self{2} = MI.adv{1} /\
   KESim.adv{2} = [] /\ ={glob Adv} /\
   ke_hybrid_ideal_sim_rel1
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2};|}
   pt12{1} pt22{1} q1{1}).
call (_ : true); first auto.
sp 0 1.
rcondf{2} 2; first auto.
sp.
if.
sp.
if.
auto.
if.
sp.
if; [sp; if; [sp; if; auto | auto] | auto].
auto.
auto.
case (r0{1} = None).
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 1; first auto.
rcondt{2} 3; first auto.
rcondf{2} 4; first auto.
auto; by progress;
  rewrite (KEHybridIdealSimRel1 _ pt12{1} pt22{1} q1{1}).
rcondf{1} 1; first auto.
rcondt{2} 1; first auto.
transitivity{1}
  {r <- MI_KEHybrid_AfterAdv.after_adv(r0);}
  (={r0, MI.func, MI.adv, MI.in_guard,
     KEHybrid.self, KEHybrid.adv, KEHybrid.st, glob Adv} /\
     not_done{1} ==>
   ={r, MI.func, MI.adv, MI.in_guard,
     KEHybrid.self, KEHybrid.adv, KEHybrid.st, glob Adv})
  (r0{1} = r4{2} /\ r0{1} <> None /\ not_done{1} /\ not_done{2} /\
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\ KEHybrid.self{1} = MI.func{1} /\
   KEHybrid.adv{1} = MI.adv{1} /\ KEIdeal.self{2} = MI.func{1} /\
   KEIdeal.adv{2} = MI.adv{1} /\ KESim.self{2} = MI.adv{1} /\
   KESim.adv{2} = [] /\ ={glob Adv} /\
   ke_hybrid_ideal_sim_rel1
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2};|}
     pt12{1} pt22{1} q1{1} ==>
   ={r, glob Adv} /\
   ke_hybrid_ideal_sim_rel
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2};|}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{2} KEHybrid.st{1}
          MI.adv{2} MI.func{2} (fset1 adv_fw_pi)
          not_done{1} pt12{1} pt22{1} q1{1} r4{2}.
inline MI_KEHybrid_AfterAdv.after_adv.
sim; auto => |>.
transitivity{2}
  {r <- MI_KEIdeal_KESim_AfterAdv.after_adv(r0);}
  (={r0, MI.func, MI.adv, MI.in_guard} /\ r0{1} <> None /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   KEHybrid.self{1} = MI.func{1} /\ KEHybrid.adv{1} = MI.adv{1} /\
   KEIdeal.self{2} = MI.func{1} /\ KEIdeal.adv{2} = MI.adv{1} /\
   KESim.self{2} = MI.adv{1} /\ KESim.adv{2} = [] /\ ={glob Adv} /\
   ke_hybrid_ideal_sim_rel1
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2};|}
   pt12{1} pt22{1} q1{1} ==>
   ={r, glob Adv} /\
   ke_hybrid_ideal_sim_rel
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2};|})
  (r0{1} = r4{2} /\
   ={MI.func, MI.adv, MI.in_guard,
     KEIdeal.self, KEIdeal.adv, KEIdeal.st,
     KESim.self, KESim.adv, KESim.st, glob Adv} /\
   not_done{2} ==>
   ={r, MI.func, MI.adv, MI.in_guard,
     KEIdeal.self, KEIdeal.adv, KEIdeal.st,
     KESim.self, KESim.adv, KESim.st, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{2} KEIdeal.st{2}
          [] MI.adv{2} KESim.st{2} MI.adv{2} MI.func{2}
          (fset1 adv_fw_pi) r4{2}.
exists* pt12{1}, pt22{1}, q1{1}; elim* => pt1' pt2' q1'.
call (MI_KEHybrid_KEIdeal_KESim_after_adv_1 pt1' pt2' q1').
auto.
inline MI_KEIdeal_KESim_AfterAdv.after_adv.
sp 3 0.
seq 4 4 :
  (r5{1} = r4{2} /\ not_done1{1} = not_done{2} /\
   ={MI.func, MI.adv, MI.in_guard,
   KEIdeal.self, KEIdeal.adv, KEIdeal.st,
   KESim.self, KESim.adv, KESim.st, glob Adv}).
sim => |>.
sp 0 2.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
rcondt{1} 3; first auto.
rcondt{2} 3; first auto.
rcondf{1} 4; first auto.
rcondf{2} 4; first auto.
auto.
rcondt{1} 3; first auto.
rcondt{2} 3; first auto.
rcondf{1} 4; first auto.
rcondf{2} 4; first auto.
auto.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
inline{2} (1) KESim(Adv).invoke.
rcondt{2} 4; first auto; smt().
inline{2} (1) KESim(Adv).loop.
rcondt{2} 7; first auto.
rcondf{2} 7; first auto; progress.
have /= := ke_pi_uniq; smt(in_fset1).
sp 0 6.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ r0{1} = r2{2} /\
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\ KEHybrid.self{1} = MI.func{1} /\
   KEHybrid.adv{1} = MI.adv{1} /\ KEIdeal.self{2} = MI.func{1} /\
   KEIdeal.adv{2} = MI.adv{1} /\  KESim.self{2} = MI.adv{1} /\
   KESim.adv{2} = [] /\ ={glob Adv} /\
   ke_hybrid_ideal_sim_rel0
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2}|}).
call (_ : true); auto.
sp 0 1.
case (r0{1} = None).
rcondt{1} 1; first auto.
rcondf{2} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 1; first auto.
rcondt{2} 3; first auto.
rcondf{2} 4; first auto.
auto; progress; by rewrite KEHybridIdealSimRel0.
rcondf{1} 1; first auto.
rcondt{2} 1; first auto.
sp 3 3.
if; first move => |> &1 &2 <- /#.
rcondf{1} 3; first auto.
rcondf{2} 2; first auto.
rcondt{2} 4; first auto.
rcondf{2} 5; first auto.
auto; progress; by rewrite KEHybridIdealSimRel0.
case ((MI.func <= addr10){1}).
rcondf{1} 1; first auto.
rcondt{1} 1; first auto.
sp 2 0.
rcondt{1} 1; first auto.
inline{1} (1) KEHybrid.invoke.
sp 4 0.
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto.
rcondf{2} 3; first auto.
sp 0 5.
elim* => addr10_L n10_L mod0_L pt10_L pt20_L u0_L.
seq 2 0 :
  (r0{1} = None /\ mod0{2} = Adv /\ MI.func{2} <= addr10{2} /\
   m0{2}.`1 = mod0{2} /\ m0{2}.`2.`1 = addr10{2} /\ not_done{2} /\
   ={MI.func, MI.adv, MI.in_guard} /\ KEHybrid.self{1} = MI.func{1} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\ KEHybrid.self{1} = MI.func{1} /\
   KEHybrid.adv{1} = MI.adv{1} /\ KEIdeal.self{2} = MI.func{1} /\
   KEIdeal.adv{2} = MI.adv{1} /\  KESim.self{2} = MI.adv{1} /\
   KESim.adv{2} = [] /\ ={glob Adv} /\
   ke_hybrid_ideal_sim_rel0
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2}|}).
if{1}.
wp; inline KEHybrid.parties.
rcondt{1} 3; first auto; smt().
rcondf{1} 3; first auto; progress.
rewrite /is_ke_req1 /dec_ke_req1 /= /#.
auto; smt().
auto => |> &1 &2 <- [#] <- _ _ _ /= _ [#] -> _ _ _ _ _ _ 
        _ _ _ /negb_or [#] _ /not_dir -> _ _ /#.
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 1; first auto; smt(inc_le2_not_lr).
rcondf{2} 1; first auto.
rcondt{2} 1; first auto.
sp 2 2.
rcondt{2} 1; first auto.
inline{2} (1) KEIdeal.invoke.
sp 0 4.
if{2}.
inline{2} (1) KEIdeal.parties.
sp 0 2.
rcondt{2} 1; first auto; smt().
rcondf{2} 1; first auto.
rcondt{2} 3; first auto.
rcondf{2} 4; first auto.
auto; progress; by rewrite KEHybridIdealSimRel0.
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
auto; progress; by rewrite KEHybridIdealSimRel0.
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt(is_ke_sim_state_wait_req2).
rcondf{2} 1; first auto.
rcondf{2} 3; first auto.
rcondf{2} 6; first auto; smt().
rcondt{2} 6; first auto; smt().
rcondf{2} 7; first auto.
auto; progress; by rewrite KEHybridIdealSimRel0.
auto.
case
  (exists (pt1 pt2 : port) (q1 : exp),
   ke_hybrid_ideal_sim_rel1
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2}|}
   pt1 pt2 q1).
elim* => pt1' pt2' q1'.
sp 2 2.
if => //.
inline MI(KEHybrid, Adv).loop MI(KEIdeal, KESim(Adv)).loop.
sp 3 3.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
sp 2 2.
if => //.
inline KEHybrid.invoke KEIdeal.invoke.
sp 4 4.
seq 1 0 :
  (r1{1} = None /\ ={r1, m1, m0} /\ m1{2}.`1 = mod1{2} /\
   m1{2}.`2 = (addr11, n11){2} /\ mod1{2} = Dir /\
   MI.func{1} <= addr11{2} /\
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\ KEHybrid.self{1} = MI.func{1} /\
   KEHybrid.adv{1} = MI.adv{1} /\ KEIdeal.self{2} = MI.func{1} /\
   KEIdeal.adv{2} = MI.adv{1} /\  KESim.self{2} = MI.adv{1} /\
   KESim.adv{2} = [] /\ ={glob Adv} /\
   ke_hybrid_ideal_sim_rel1
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2}|}
   pt1' pt2' q1').
if{1}.
inline KEHybrid.parties.
rcondf{1} 3; first auto; smt().
rcondt{1} 3; first auto; smt(is_ke_hybrid_state_wait_adv1).
rcondf{1} 4; first auto; progress.
rewrite /is_fw_ok /dec_fw_ok /= /#.
auto; smt().
auto; smt().
if{2}.
inline KEIdeal.parties.
rcondf{2} 3; first auto; smt().
rcondt{2} 3; first auto; smt(is_ke_ideal_state_wait_sim1).
rcondf{2} 4; first auto; progress.
rewrite /is_ke_sim_rsp /dec_ke_sim_rsp /= /#.
sp 1 5.
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
rcondt{2} 1; first auto.
rcondf{2} 2; first auto.
auto; progress; by apply (KEHybridIdealSimRel1 _ pt1' pt2' q1').
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
auto; progress; by apply (KEHybridIdealSimRel1 _ pt1' pt2' q1').
inline{2} (1) KESim(Adv).invoke.
rcondt{2} 4; first auto; smt().
inline{2} (1) KESim(Adv).loop.
rcondt{2} 7; first auto.
rcondf{2} 7; first auto; progress.
have /= := ke_pi_uniq; smt(in_fset1).
sp 0 6.
seq 1 1 :
   (r0{1} = r2{2} /\ not_done{1} /\ not_done{2} /\ not_done0{2} /\
    ={MI.func, MI.adv, MI.in_guard} /\
    exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
    MI.in_guard{1} = fset1 adv_fw_pi /\ KEHybrid.self{1} = MI.func{1} /\
    KEHybrid.adv{1} = MI.adv{1} /\ KEIdeal.self{2} = MI.func{1} /\
    KEIdeal.adv{2} = MI.adv{1} /\  KESim.self{2} = MI.adv{1} /\
    KESim.adv{2} = [] /\ ={glob Adv} /\
   ke_hybrid_ideal_sim_rel1
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2}|}
   pt1' pt2' q1').
call (_ : true); first auto.
sp 0 1.
rcondf{2} 2; first auto.
sp.
if.
sp.
if.
auto.
if.
sp.
if; [sp; if; [sp; if; auto | auto] | auto].
auto.
auto.
case (r0{1} = None).
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 1; first auto.
rcondt{2} 3; first auto.
rcondf{2} 4; first auto.
auto; progress; by apply (KEHybridIdealSimRel1 _ pt1' pt2' q1').
rcondf{1} 1; first auto.
rcondt{2} 1; first auto.
transitivity{1}
  {r <- MI_KEHybrid_AfterAdv.after_adv(r0);}
  (={r0, MI.func, MI.adv, MI.in_guard,
     KEHybrid.self, KEHybrid.adv, KEHybrid.st, glob Adv} /\
     not_done{1} ==>
   ={r, MI.func, MI.adv, MI.in_guard,
     KEHybrid.self, KEHybrid.adv, KEHybrid.st, glob Adv})
  (r0{1} = r2{2} /\ r0{1} <> None /\
   not_done{1} /\ not_done{2} /\
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\ KEHybrid.self{1} = MI.func{1} /\
   KEHybrid.adv{1} = MI.adv{1} /\ KEIdeal.self{2} = MI.func{1} /\
   KEIdeal.adv{2} = MI.adv{1} /\  KESim.self{2} = MI.adv{1} /\
   KESim.adv{2} = [] /\ ={glob Adv} /\
   ke_hybrid_ideal_sim_rel1
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2};|}
   pt1' pt2' q1' ==>
   ={r, glob Adv} /\
   ke_hybrid_ideal_sim_rel
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2};|}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{2} KEHybrid.st{1}
          MI.adv{2} MI.func{2} (fset1 adv_fw_pi)
          not_done{1} r2{2}.
inline MI_KEHybrid_AfterAdv.after_adv.
sim; auto => |>.
transitivity{2}
  {r <- MI_KEIdeal_KESim_AfterAdv.after_adv(r2);}
  (r0{1} = r2{2} /\ r0{1} <> None /\
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\ KEHybrid.self{1} = MI.func{1} /\
   KEHybrid.adv{1} = MI.adv{1} /\ KEIdeal.self{2} = MI.func{1} /\
   KEIdeal.adv{2} = MI.adv{1} /\  KESim.self{2} = MI.adv{1} /\
   KESim.adv{2} = [] /\ ={glob Adv} /\
   ke_hybrid_ideal_sim_rel1
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2};|}
   pt1' pt2' q1' ==>
   ={r, glob Adv} /\
   ke_hybrid_ideal_sim_rel
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2};|})
  (={r2, MI.func, MI.adv, MI.in_guard,
     KEIdeal.self, KEIdeal.adv, KEIdeal.st,
     KESim.self, KESim.adv, KESim.st, glob Adv} /\
   not_done{2} ==>
   ={r, MI.func, MI.adv, MI.in_guard,
     KEIdeal.self, KEIdeal.adv, KEIdeal.st,
     KESim.self, KESim.adv, KESim.st, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{2} KEIdeal.st{2}
          [] MI.adv{2} KESim.st{2} MI.adv{2} MI.func{2}
          (fset1 adv_fw_pi) r2{2}.
call (MI_KEHybrid_KEIdeal_KESim_after_adv_1 pt1' pt2' q1').
auto.
inline MI_KEIdeal_KESim_AfterAdv.after_adv.
sp 3 0.
seq 4 4 :
  (r3{1} = r2{2} /\ not_done1{1} = not_done{2} /\
   ={MI.func, MI.adv, MI.in_guard,
   KEIdeal.self, KEIdeal.adv, KEIdeal.st,
   KESim.self, KESim.adv, KESim.st, glob Adv}).
sim => |>.
sp 0 2.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
auto.
case
  (exists (pt1 pt2 : port) (q1 q2 q3 : exp),
   ke_hybrid_ideal_sim_rel2
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2}|}
   pt1 pt2 q1 q2 q3).
elim* => pt1'' pt2'' q1' q2' q3'.
sp 2 2.
if => //.
inline MI(KEHybrid, Adv).loop MI(KEIdeal, KESim(Adv)).loop.
sp 3 3.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
sp 2 2.
if => //.
inline{1} (1) KEHybrid.invoke.
inline{2} (1) KEIdeal.invoke.
sp 4 4.
if => //.
progress; smt().
inline{1} (1) KEHybrid.parties.
inline{2} (1) KEIdeal.parties.
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondt{1} 3; first auto; smt(is_ke_hybrid_state_wait_req2).
rcondf{2} 3; first auto; smt().
rcondf{2} 3; first auto; smt().
rcondt{2} 3; first auto; smt(is_ke_ideal_state_wait_req2).
sp 3 3.
if => //.
sp 1 1.
if.
move => &1 &2 [#] dec_req_2 dec_req_1 ->> _ dec_ideal_wait_eq
        ->> _ dec_hybrid_wait_eq ->> _ _ _ ->> _ _ _ _ _
        _ _ ->> _ _ ->> _ _ _ _ _ _ ->> _ _ _ _ _ _ _ _ _
        _ _ _ _ _ _.
rewrite -dec_req_2 /= in dec_req_1.
elim dec_req_1 => ->> ->>.
move => [] /= _ [#] _ _ _ ->> ->> _.
rewrite /= oget_some /= in dec_ideal_wait_eq.
rewrite /= oget_some /= in dec_hybrid_wait_eq.
elim dec_hybrid_wait_eq => ->> [#] ->> _ _ _.
elim dec_ideal_wait_eq => _ [#] -> //.
rcondf{2} 5; first auto.
rcondf{2} 8; first auto.
move => &hr |> <- /= [#] _ ->.
rewrite oget_some /ke_sim_req2 /= /#.
rcondf{2} 8; first auto.
rcondf{2} 8; first auto.
move => &hr |> <- /= [#] _ ->.
rewrite oget_some /ke_sim_req2 /=.
smt(ke_pi_uniq).
rcondt{2} 8; first auto.
rcondf{2} 10; first auto.
move => &hr |> <- /= [#] _ ->.
rewrite oget_some /ke_sim_req2 /= /#.
sp 0 9.
inline{2} (1) KESim(Adv).invoke.
rcondt{2} 4; first auto.
inline{2} (1) KESim(Adv).loop.
rcondt{2} 7; first auto.
rcondt{2} 7; first auto.
rcondf{2} 8; first auto; smt().
rcondt{2} 8; first auto; smt(is_ke_sim_state_wait_req2).
rcondt{2} 9; first auto.
rcondf{2} 12; first auto.
rcondt{2} 13; first auto.
rcondf{2} 13; first auto; progress.
rewrite oget_some /= /fw_obs /=; smt(ke_pi_uniq).
sp 0 12.
rcondf{1} 6; first auto.
rcondf{1} 9; first auto; progress.
rewrite oget_some /fw_obs /= /#.
rcondf{1} 9; first auto.
rcondf{1} 9; first auto; progress.
rewrite oget_some /fw_obs /=; smt(ke_pi_uniq).
rcondt{1} 9; first auto.
rcondf{1} 11; first auto; progress.
rewrite oget_some /fw_obs /= /#.
sp 10 0.
conseq
  (_ :
   m0{1} = m4{2} /\ not_done{1} /\ not_done{2} /\
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\ KEHybrid.self{1} = MI.func{1} /\
   KEHybrid.adv{1} = MI.adv{1} /\ KEIdeal.self{2} = MI.func{1} /\
   KEIdeal.adv{2} = MI.adv{1} /\ KESim.self{2} = MI.adv{1} /\
   KESim.adv{2} = [] /\ ={glob Adv} /\
   ke_hybrid_ideal_sim_rel3
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2};|}
   pt1'' pt2'' q1' q2' q3' ==>
   _).
move => |> &1 &2 mod0_L pt10_L pt20_L u0_L st_L.
rewrite !oget_some /=.
move => ^H <- [#] <<- <<- <<- <<- st_R.
move : H.
rewrite /fw_obs /=.
move => [#] -> -> -> -> -> dec_sim_wait_eq _ st_R0
        _ _ _ dec_ideal_wait_eq dec_ke_req_eq pre _ _ _
        [] /= out_pt1''1 [#] out_pt2''1 out_pt1''2 out_pt2''2
        ->> ->> ->>.
rewrite /= oget_some /= in dec_sim_wait_eq.
elim dec_sim_wait_eq => ->> [#] ->> ->>.
rewrite /= oget_some /= in dec_ke_req_eq.
elim dec_ke_req_eq => ->> [#] ->> ->> ->> ->> /=.
rewrite /ke_hybrid_ideal_sim_rel3 /=.
rewrite /= oget_some /= in dec_ideal_wait_eq.
elim dec_ideal_wait_eq => ->> [#] ->> ->> //.
seq 1 1 :
  (r0{1} = r4{2} /\ not_done{1} /\ not_done{2} /\
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\ KEHybrid.self{1} = MI.func{1} /\
   KEHybrid.adv{1} = MI.adv{1} /\ KEIdeal.self{2} = MI.func{1} /\
   KEIdeal.adv{2} = MI.adv{1} /\ KESim.self{2} = MI.adv{1} /\
   KESim.adv{2} = [] /\ ={glob Adv} /\
   ke_hybrid_ideal_sim_rel3
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2};|}
   pt1'' pt2'' q1' q2' q3').
call (_ : true).
auto.
sp 0 1.
rcondf{2} 2; first auto.
sp.
if.
sp.
if.
auto.
if.
sp.
if; [sp; if; [sp; if; auto | auto] | auto].
auto.
auto.
case (r0{1} = None).
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 1; first auto.
rcondt{2} 3; first auto.
rcondf{2} 4; first auto.
auto; by progress;
  rewrite (KEHybridIdealSimRel3 _ pt1'' pt2'' q1' q2' q3').
rcondf{1} 1; first auto.
rcondt{2} 1; first auto.
transitivity{1}
  {r <- MI_KEHybrid_AfterAdv.after_adv(r0);}
  (={r0, MI.func, MI.adv, MI.in_guard,
     KEHybrid.self, KEHybrid.adv, KEHybrid.st, glob Adv} /\
     not_done{1} ==>
   ={r, MI.func, MI.adv, MI.in_guard,
     KEHybrid.self, KEHybrid.adv, KEHybrid.st, glob Adv})
  (r0{1} = r4{2} /\ r0{1} <> None /\ not_done{1} /\ not_done{2} /\
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\ KEHybrid.self{1} = MI.func{1} /\
   KEHybrid.adv{1} = MI.adv{1} /\ KEIdeal.self{2} = MI.func{1} /\
   KEIdeal.adv{2} = MI.adv{1} /\ KESim.self{2} = MI.adv{1} /\
   KESim.adv{2} = [] /\ ={glob Adv} /\
   ke_hybrid_ideal_sim_rel3
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2};|}
   pt1'' pt2'' q1' q2' q3' ==>
   ={r, glob Adv} /\
   ke_hybrid_ideal_sim_rel
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2};|}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{2} KEHybrid.st{1}
          MI.adv{2} MI.func{2} (fset1 adv_fw_pi)
          not_done{1} r4{2}.
inline MI_KEHybrid_AfterAdv.after_adv.
sim; auto => |>.
transitivity{2}
  {r <- MI_KEIdeal_KESim_AfterAdv.after_adv(r0);}
  (={r0, MI.func, MI.adv, MI.in_guard} /\ r0{1} <> None /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   KEHybrid.self{1} = MI.func{1} /\ KEHybrid.adv{1} = MI.adv{1} /\
   KEIdeal.self{2} = MI.func{1} /\ KEIdeal.adv{2} = MI.adv{1} /\
   KESim.self{2} = MI.adv{1} /\ KESim.adv{2} = [] /\ ={glob Adv} /\
   ke_hybrid_ideal_sim_rel3
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2};|}
   pt1'' pt2'' q1' q2' q3' ==>
   ={r, glob Adv} /\
   ke_hybrid_ideal_sim_rel
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2};|})
  (r0{1} = r4{2} /\
   ={MI.func, MI.adv, MI.in_guard,
     KEIdeal.self, KEIdeal.adv, KEIdeal.st,
     KESim.self, KESim.adv, KESim.st, glob Adv} /\
   not_done{2} ==>
   ={r, MI.func, MI.adv, MI.in_guard,
     KEIdeal.self, KEIdeal.adv, KEIdeal.st,
     KESim.self, KESim.adv, KESim.st, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{2} KEIdeal.st{2}
          [] MI.adv{2} KESim.st{2} MI.adv{2} MI.func{2}
          (fset1 adv_fw_pi) r4{2}.
call (MI_KEHybrid_KEIdeal_KESim_after_adv_2 pt1'' pt2'' q1' q2' q3').
auto.
inline MI_KEIdeal_KESim_AfterAdv.after_adv.
sp 3 0.
seq 4 4 :
  (r5{1} = r4{2} /\ not_done1{1} = not_done{2} /\
   ={MI.func, MI.adv, MI.in_guard,
   KEIdeal.self, KEIdeal.adv, KEIdeal.st,
   KESim.self, KESim.adv, KESim.st, glob Adv}).
sim => |>.
sp 0 2.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
rcondt{1} 3; first auto.
rcondt{2} 3; first auto.
rcondf{1} 4; first auto.
rcondf{2} 4; first auto.
auto.
rcondt{1} 3; first auto.
rcondt{2} 3; first auto.
rcondf{1} 4; first auto.
rcondf{2} 4; first auto.
auto.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
inline{2} (1) KESim(Adv).invoke.
rcondt{2} 4; first auto; smt().
inline{2} (1) KESim(Adv).loop.
rcondt{2} 7; first auto.
rcondf{2} 7; first auto; progress.
have /= := ke_pi_uniq; smt(in_fset1).
sp 0 6.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ not_done0{2} /\ r0{1} = r2{2} /\
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\ KEHybrid.self{1} = MI.func{1} /\
   KEHybrid.adv{1} = MI.adv{1} /\ KEIdeal.self{2} = MI.func{1} /\
   KEIdeal.adv{2} = MI.adv{1} /\  KESim.self{2} = MI.adv{1} /\
   KESim.adv{2} = [] /\ ={glob Adv} /\
   ke_hybrid_ideal_sim_rel2
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2}|}
   pt1'' pt2'' q1' q2' q3').
call (_ : true); auto.
sp 0 1.
case (r0{1} = None).
rcondt{1} 1; first auto.
rcondf{2} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 1; first auto.
rcondt{2} 3; first auto.
rcondf{2} 4; first auto.
auto; progress; by rewrite (KEHybridIdealSimRel2 _ pt1'' pt2'' q1' q2' q3').
rcondf{1} 1; first auto.
rcondt{2} 1; first auto.
sp 3 3.
if; first move => |> &1 &2 <- /#.
rcondf{1} 3; first auto.
rcondf{2} 2; first auto.
rcondt{2} 4; first auto.
rcondf{2} 5; first auto.
auto; progress; by rewrite (KEHybridIdealSimRel2 _ pt1'' pt2'' q1' q2' q3').
case ((MI.func <= addr10){1}).
rcondf{1} 1; first auto.
rcondt{1} 1; first auto.
sp 2 0.
rcondt{1} 1; first auto.
inline{1} (1) KEHybrid.invoke.
sp 4 0.
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_ke_sim_state_wait_req2).
rcondt{2} 2; first auto.
move => |> &hr <- /= [#] -> -> _ _ _ _ _ _ _ _
        [] /= [#] _ [#] _ _ _ _ _ -> /=.
by rewrite oget_some.
rcondf{2} 3; first auto; smt().
rcondt{2} 5; first auto.
rcondf{2} 6; first auto.
wp.
elim* => addr10_L n10_L mod0_L pt10_L pt20_L u0_L not_done0_R.
if{1}.
wp; inline{1} (1) KEHybrid.parties.
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondt{1} 3; first auto; smt(is_ke_hybrid_state_wait_req2).
rcondf{1} 4; first auto; progress.
rewrite /is_ke_req2 /dec_ke_req2 /= /#.
rcondt{1} 6; first auto.
rcondf{1} 7; first auto.
auto; progress;
  by rewrite (KEHybridIdealSimRel2 _ pt1'' pt2'' q1' q2' q3').
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto; progress;
  by rewrite (KEHybridIdealSimRel2 _ pt1'' pt2'' q1' q2' q3').
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 1; first auto; smt(inc_le2_not_lr).
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_ke_sim_state_wait_req2).
rcondf{2} 2; first auto.
move => |> &hr <- /= [#] -> -> _ _ _ not_done0_R _ _ _
        _ [] /= _ [#] _ _ _ _ _ -> /=.
by rewrite oget_some.
rcondf{2} 2; first auto.
rcondf{2} 4; first auto.
rcondf{2} 7; first auto; smt().
rcondt{2} 7; first auto; smt().
rcondf{2} 8; first auto.
auto; progress;
  by rewrite (KEHybridIdealSimRel2 _ pt1'' pt2'' q1' q2' q3').
auto.
case
  (exists (pt1 pt2 : port) (q1 q2 q3 : exp),
   ke_hybrid_ideal_sim_rel3
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2}|}
   pt1 pt2 q1 q2 q3).
elim* => pt1'' pt2'' q1' q2' q3'.
sp 2 2.
if => //.
inline MI(KEHybrid, Adv).loop MI(KEIdeal, KESim(Adv)).loop.
sp 3 3.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
sp 2 2.
if => //.
inline KEHybrid.invoke KEIdeal.invoke.
sp 4 4.
seq 1 0 :
  (r1{1} = None /\ ={r1, m1, m0} /\ m1{2}.`1 = mod1{2} /\
   m1{2}.`2 = (addr11, n11){2} /\ mod1{2} = Dir /\
   MI.func{1} <= addr11{2} /\
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\ KEHybrid.self{1} = MI.func{1} /\
   KEHybrid.adv{1} = MI.adv{1} /\ KEIdeal.self{2} = MI.func{1} /\
   KEIdeal.adv{2} = MI.adv{1} /\  KESim.self{2} = MI.adv{1} /\
   KESim.adv{2} = [] /\ ={glob Adv} /\
   ke_hybrid_ideal_sim_rel3
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2}|}
   pt1'' pt2'' q1' q2' q3').
if{1}.
inline KEHybrid.parties.
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondt{1} 3; first auto; smt(is_ke_hybrid_state_wait_adv2).
rcondf{1} 4; first auto; progress.
rewrite /is_fw_ok /dec_fw_ok /= /#.
auto; smt().
auto; smt().
if{2}.
inline KEIdeal.parties.
rcondf{2} 3; first auto; smt().
rcondf{2} 3; first auto; smt().
rcondf{2} 3; first auto; smt().
rcondt{2} 3; first auto; smt(is_ke_ideal_state_wait_sim2).
rcondf{2} 4; first auto; progress.
rewrite /is_ke_sim_rsp /dec_ke_sim_rsp /= /#.
sp 1 5.
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
rcondt{2} 1; first auto.
rcondf{2} 2; first auto.
auto; progress;
  by apply (KEHybridIdealSimRel3 _ pt1'' pt2'' q1' q2' q3').
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
auto; progress;
  by apply (KEHybridIdealSimRel3 _ pt1'' pt2'' q1' q2' q3').
inline{2} (1) KESim(Adv).invoke.
rcondt{2} 4; first auto; smt().
inline{2} (1) KESim(Adv).loop.
rcondt{2} 7; first auto.
rcondf{2} 7; first auto; progress.
have /= := ke_pi_uniq; smt(in_fset1).
sp 0 6.
seq 1 1 :
   (r0{1} = r2{2} /\ not_done{1} /\ not_done{2} /\ not_done0{2} /\
    ={MI.func, MI.adv, MI.in_guard} /\
    exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
    MI.in_guard{1} = fset1 adv_fw_pi /\ KEHybrid.self{1} = MI.func{1} /\
    KEHybrid.adv{1} = MI.adv{1} /\ KEIdeal.self{2} = MI.func{1} /\
    KEIdeal.adv{2} = MI.adv{1} /\  KESim.self{2} = MI.adv{1} /\
    KESim.adv{2} = [] /\ ={glob Adv} /\
   ke_hybrid_ideal_sim_rel3
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2}|}
   pt1'' pt2'' q1' q2' q3').
call (_ : true); first auto.
sp 0 1.
rcondf{2} 2; first auto.
sp.
if.
sp.
if.
auto.
if.
sp.
if; [sp; if; [sp; if; auto | auto] | auto].
auto.
auto.
case (r0{1} = None).
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 1; first auto.
rcondt{2} 3; first auto.
rcondf{2} 4; first auto.
auto; progress;
  by apply (KEHybridIdealSimRel3 _ pt1'' pt2'' q1' q2' q3').
rcondf{1} 1; first auto.
rcondt{2} 1; first auto.
transitivity{1}
  {r <- MI_KEHybrid_AfterAdv.after_adv(r0);}
  (={r0, MI.func, MI.adv, MI.in_guard,
     KEHybrid.self, KEHybrid.adv, KEHybrid.st, glob Adv} /\
     not_done{1} ==>
   ={r, MI.func, MI.adv, MI.in_guard,
     KEHybrid.self, KEHybrid.adv, KEHybrid.st, glob Adv})
  (r0{1} = r2{2} /\ r0{1} <> None /\
   not_done{1} /\ not_done{2} /\
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\ KEHybrid.self{1} = MI.func{1} /\
   KEHybrid.adv{1} = MI.adv{1} /\ KEIdeal.self{2} = MI.func{1} /\
   KEIdeal.adv{2} = MI.adv{1} /\  KESim.self{2} = MI.adv{1} /\
   KESim.adv{2} = [] /\ ={glob Adv} /\
   ke_hybrid_ideal_sim_rel3
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2};|}
   pt1'' pt2'' q1' q2' q3' ==>
   ={r, glob Adv} /\
   ke_hybrid_ideal_sim_rel
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2};|}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{2} KEHybrid.st{1}
          MI.adv{2} MI.func{2} (fset1 adv_fw_pi)
          not_done{1} r2{2}.
inline MI_KEHybrid_AfterAdv.after_adv.
sim; auto => |>.
transitivity{2}
  {r <- MI_KEIdeal_KESim_AfterAdv.after_adv(r2);}
  (r0{1} = r2{2} /\ r0{1} <> None /\
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\ KEHybrid.self{1} = MI.func{1} /\
   KEHybrid.adv{1} = MI.adv{1} /\ KEIdeal.self{2} = MI.func{1} /\
   KEIdeal.adv{2} = MI.adv{1} /\  KESim.self{2} = MI.adv{1} /\
   KESim.adv{2} = [] /\ ={glob Adv} /\
   ke_hybrid_ideal_sim_rel3
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2};|}
   pt1'' pt2'' q1' q2' q3' ==>
   ={r, glob Adv} /\
   ke_hybrid_ideal_sim_rel
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2};|})
  (={r2, MI.func, MI.adv, MI.in_guard,
     KEIdeal.self, KEIdeal.adv, KEIdeal.st,
     KESim.self, KESim.adv, KESim.st, glob Adv} /\
   not_done{2} ==>
   ={r, MI.func, MI.adv, MI.in_guard,
     KEIdeal.self, KEIdeal.adv, KEIdeal.st,
     KESim.self, KESim.adv, KESim.st, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{2} KEIdeal.st{2}
          [] MI.adv{2} KESim.st{2} MI.adv{2} MI.func{2}
          (fset1 adv_fw_pi) r2{2}.
call (MI_KEHybrid_KEIdeal_KESim_after_adv_2 pt1'' pt2'' q1' q2' q3').
auto.
inline MI_KEIdeal_KESim_AfterAdv.after_adv.
sp 3 0.
seq 4 4 :
  (r3{1} = r2{2} /\ not_done1{1} = not_done{2} /\
   ={MI.func, MI.adv, MI.in_guard,
   KEIdeal.self, KEIdeal.adv, KEIdeal.st,
   KESim.self, KESim.adv, KESim.st, glob Adv}).
sim => |>.
sp 0 2.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
auto.
case
  (exists (pt1 pt2 : port) (q1 q2 q3 : exp),
   ke_hybrid_ideal_sim_rel4
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2}|}
   pt1 pt2 q1 q2 q3).
elim* => pt1'' pt2'' q1' q2' q3'.
sp 2 2.
if => //.
inline MI(KEHybrid, Adv).loop MI(KEIdeal, KESim(Adv)).loop.
rcondt{1} 4; first auto.
rcondt{2} 4; first auto.
sp 5 5.
if => //.
inline{1} (1) KEHybrid.invoke.
inline{2} (1) KEIdeal.invoke.
seq 6 0 :
  (={m} /\ r0{1} = None /\
   MI.func{1} <= m{1}.`2.`1 /\ m{1}.`1 = Dir /\
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\ KEHybrid.self{1} = MI.func{1} /\
   KEHybrid.adv{1} = MI.adv{1} /\ KEIdeal.self{2} = MI.func{1} /\
   KEIdeal.adv{2} = MI.adv{1} /\  KESim.self{2} = MI.adv{1} /\
   KESim.adv{2} = [] /\ ={glob Adv} /\
   ke_hybrid_ideal_sim_rel4
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2}|}
   pt1'' pt2'' q1' q2' q3').
sp 4 0.
if{1}.
inline KEHybrid.parties.
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
auto; progress; smt().
auto; progress; smt().
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
wp.
sp 0 4.
if{2}.
inline{2} (1) KEIdeal.parties.
rcondf{2} 3; first auto; smt().
rcondf{2} 3; first auto; smt().
rcondf{2} 3; first auto; smt().
rcondf{2} 3; first auto; smt().
rcondt{2} 5; first auto.
rcondf{2} 6; first auto.
auto; progress;
  by apply (KEHybridIdealSimRel4 _ pt1'' pt2'' q1' q2' q3').
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
auto; progress;
  by apply (KEHybridIdealSimRel4 _ pt1'' pt2'' q1' q2' q3').
inline KESim(Adv).invoke.
sp 0 3.
rcondt{2} 1; first auto; smt().
inline KESim(Adv).loop.
rcondt{2} 4; first auto.
rcondf{2} 4; first auto.
move => |> &hr _ _ _ _ _ _ _.
have /= := ke_pi_uniq.
smt(in_fset1).
sp 0 3.
seq 1 1 :
  (r0{1} = r3{2} /\ not_done{1} /\ not_done{2} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   ={MI.func, MI.adv, MI.in_guard} /\
   MI.in_guard{1} = fset1 adv_fw_pi /\ KEHybrid.self{1} = MI.func{1} /\
   KEHybrid.adv{1} = MI.adv{1} /\ KEIdeal.self{2} = MI.func{1} /\
   KEIdeal.adv{2} = MI.adv{1} /\  KESim.self{2} = MI.adv{1} /\
   KESim.adv{2} = [] /\ ={glob Adv} /\
   ke_hybrid_ideal_sim_rel4
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2}|}
   pt1'' pt2'' q1' q2' q3').
call (_ : true); first auto.
sp 0 1.
case (r0{1} = None).
rcondt{1} 1; first auto.
rcondf{2} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 1; first auto.
rcondt{2} 3; first auto.
rcondf{2} 4; first auto.
auto; progress;
  by apply (KEHybridIdealSimRel4 _ pt1'' pt2'' q1' q2' q3').
rcondf{1} 1; first auto.
rcondt{2} 1; first auto.
sp 3 3.
if; first auto => |> &1 &2 <- /#.
rcondf{1} 3; first auto.
rcondf{2} 2; first auto.
rcondt{2} 4; first auto.
rcondf{2} 5; first auto.
auto; progress;
  by apply (KEHybridIdealSimRel4 _ pt1'' pt2'' q1' q2' q3').
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 3; first auto.
rcondf{2} 6; first auto.
move => |> &hr /= <- [#] <- <- //.
sp 0 5.
if; first move => |> &1 &2 <- //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto; progress;
  by apply (KEHybridIdealSimRel4 _ pt1'' pt2'' q1' q2' q3').
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
sp 2 2.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto; move => |> &hr <- //.
inline{1} (1) KEHybrid.invoke.
inline{2} (1) KEIdeal.invoke.
sp 4 4.
seq 2 0 :
  (r0{1} = None /\ r5{2} = None /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   ={MI.func, MI.adv, MI.in_guard} /\
   MI.in_guard{1} = fset1 adv_fw_pi /\ KEHybrid.self{1} = MI.func{1} /\
   KEHybrid.adv{1} = MI.adv{1} /\ KEIdeal.self{2} = MI.func{1} /\
   KEIdeal.adv{2} = MI.adv{1} /\  KESim.self{2} = MI.adv{1} /\
   KESim.adv{2} = [] /\ ={glob Adv} /\
   ke_hybrid_ideal_sim_rel4
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2}|}
   pt1'' pt2'' q1' q2' q3').
if{1}.
inline{1} (1) KEHybrid.parties.
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
auto.
auto.
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
wp.
if{2}.
inline{2} (1) KEIdeal.parties.
rcondf{2} 3; first auto; smt().
rcondf{2} 3; first auto; smt().
rcondf{2} 3; first auto; smt().
rcondf{2} 3; first auto; smt().
rcondt{2} 5; first auto.
rcondf{2} 6; first auto.
auto; progress;
  by apply (KEHybridIdealSimRel4 _ pt1'' pt2'' q1' q2' q3').
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
auto; progress;
  by apply (KEHybridIdealSimRel4 _ pt1'' pt2'' q1' q2' q3').
auto.
exfalso => &1 &2 [#] _ _ _ _ _ _ _ _ _ _ _ _ _ []; smt().
qed.

local lemma Exper_KEHybrid_KEIdeal_KESim (func' adv' : addr) &m :
  exper_pre func' adv' (fset1 adv_fw_pi) =>
  Pr[Exper(MI(KEHybrid, Adv), Env).main
       (func', adv', fset1 adv_fw_pi) @ &m : res] =
  Pr[Exper(MI(KEIdeal, KESim(Adv)), Env).main
       (func', adv', fset1 adv_fw_pi) @ &m : res].
proof.
move => pre.
byequiv => //.
proc.
inline MI(KEHybrid, Adv).init MI(KEIdeal, KESim(Adv)).init
       KEHybrid.init KEIdeal.init KESim(Adv).init.
seq 12 17 :
  (={func, adv, in_guard, MI.func, MI.adv, MI.in_guard} /\
   func{1} = MI.func{1} /\ adv{1} = MI.adv{1} /\
   in_guard{1} = MI.in_guard{1} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   KEHybrid.self{1} = MI.func{1} /\ KEHybrid.adv{1} = MI.adv{1} /\
   KEIdeal.self{2} = MI.func{1} /\ KEIdeal.adv{2} = MI.adv{1} /\
   KESim.self{2} = MI.adv{1} /\ KESim.adv{2} = [] /\
   ={glob Adv} /\
   KEHybrid.st{1} = KEHybridStateWaitReq1 /\
   KEIdeal.st{2} = KEIdealStateWaitReq1 /\
   KESim.st{2} = KESimStateWaitReq1).
swap{2} 16 1.
call (_ : true).
auto.
call
  (_ :
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   KEHybrid.self{1} = MI.func{1} /\ KEHybrid.adv{1} = MI.adv{1} /\
   KEIdeal.self{2} = MI.func{1} /\ KEIdeal.adv{2} = MI.adv{1} /\
   KESim.self{2} = MI.adv{1} /\ KESim.adv{2} = [] /\
   ={glob Adv} /\
   ke_hybrid_ideal_sim_rel
   {|ke_hybrid_ideal_sim_rel_st_func = MI.func{1};
     ke_hybrid_ideal_sim_rel_st_adv  = MI.adv{1};
     ke_hybrid_ideal_sim_rel_st_hs   = KEHybrid.st{1};
     ke_hybrid_ideal_sim_rel_st_is   = KEIdeal.st{2};
     ke_hybrid_ideal_sim_rel_st_ss   = KESim.st{2}|}).
conseq MI_KEHybrid_KEIdeal_Sim_invoke => //.
auto; progress; by rewrite KEHybridIdealSimRel0.
qed.

lemma ke_sec (func adv : addr) &m :
  exper_pre func adv (fset1 adv_fw_pi) =>
  DDH_Adv.func{m} = func => DDH_Adv.adv{m} = adv =>
  `|Pr[Exper(MI(KEReal, Adv), Env).main
         (func, adv, fset1 adv_fw_pi) @ &m : res] -
    Pr[Exper(MI(KEIdeal, KESim(Adv)), Env).main
         (func, adv, fset1 adv_fw_pi) @ &m : res]| <=
  `|Pr[DDH1(DDH_Adv(Env, Adv)).main() @ &m : res] -
    Pr[DDH2(DDH_Adv(Env, Adv)).main() @ &m : res]|.
proof.
move => pre func_eq adv_eq.
by rewrite (Exper_KEReal_KERealSimp func adv (fset1 adv_fw_pi) &m Adv Env)
           1:/#
           (Exper_KERealSimp_GOptHashing_KERealSimpHashingAdv
            func adv &m) //
           -(RH.GNonOptHashing_GOptHashing KERealSimpHashingAdv &m)
           (KERealSimpHashingAdv_NonOptHashing_DDH1_DDH_Adv
            func adv &m) //
           -(Exper_KEHybrid_KEIdeal_KESim func adv &m) //
           (Exper_KEHybrid_KEHybridHashingAdv_OptHashing func adv &m) //
           -(RH.GNonOptHashing_GOptHashing KEHybridHashingAdv &m) //
           -(KEHybridHashingAdv_NonOptHashing_DDH2_DDH_Adv
             func adv &m).
qed.

end section.

lemma ke_security
      (Adv <: FUNC{MI, KEReal, KEIdeal, KESim, DDH_Adv})
      (Env <: ENV{Adv, MI, KEReal, KEIdeal, KESim, DDH_Adv})
      (func adv : addr) &m :
  exper_pre func adv (fset1 adv_fw_pi) =>
  DDH_Adv.func{m} = func => DDH_Adv.adv{m} = adv =>
  `|Pr[Exper(MI(KEReal, Adv), Env).main
         (func, adv, fset1 adv_fw_pi) @ &m : res] -
    Pr[Exper(MI(KEIdeal, KESim(Adv)), Env).main
         (func, adv, fset1 adv_fw_pi) @ &m : res]| <=
  `|Pr[DDH1(DDH_Adv(Env, Adv)).main() @ &m : res] -
    Pr[DDH2(DDH_Adv(Env, Adv)).main() @ &m : res]|.
proof.
move => pre func_eq adv_eq.
by apply (ke_sec Adv Env func adv &m).
qed.

(* termination metric and proof for KEReal *)

type real_term_rel_st = {
  real_term_rel_st_func : addr;
  real_term_rel_st_r1s  : ke_real_p1_state;
  real_term_rel_st_r2s  : ke_real_p2_state;
  real_term_rel_st_fws1 : Fwd1.fw_state;
  real_term_rel_st_fws2 : Fwd2.fw_state;
}.

op real_term_rel_metric_max : int = 4.

pred real_term_rel0 (met : int, st : real_term_rel_st) =
  met = 4 /\
  (st.`real_term_rel_st_r1s  = KERealP1StateWaitReq1) /\
  (st.`real_term_rel_st_r2s  = KERealP2StateWaitFwd1) /\
  (st.`real_term_rel_st_fws1 = Fwd1.FwStateInit) /\
  (st.`real_term_rel_st_fws2 = Fwd2.FwStateInit).

pred real_term_rel1 (met : int, st : real_term_rel_st, pt1 pt2 : port, q1 : exp) =
  met = 3 /\
  ! (st.`real_term_rel_st_func <= pt1.`1) /\
  ! (st.`real_term_rel_st_func <= pt2.`1) /\
  (st.`real_term_rel_st_r1s  = KERealP1StateWaitFwd2 (pt1, pt2, q1)) /\
  (st.`real_term_rel_st_r2s  = KERealP2StateWaitFwd1) /\
  (st.`real_term_rel_st_fws1 =
     Fwd1.FwStateWait
     ((st.`real_term_rel_st_func, 3), (st.`real_term_rel_st_func, 4),
      univ_triple (UnivPort pt1) (UnivPort pt2)
                  (UnivBase (BaseKey (g ^ q1))))) /\
  (st.`real_term_rel_st_fws2 = Fwd2.FwStateInit).

pred real_term_rel2 (met : int, st : real_term_rel_st, pt1 pt2 : port, q1 q2 : exp) =
  met = 2 /\
  ! (st.`real_term_rel_st_func <= pt1.`1) /\
  ! (st.`real_term_rel_st_func <= pt2.`1) /\
  (st.`real_term_rel_st_r1s  = KERealP1StateWaitFwd2 (pt1, pt2, q1)) /\
  (st.`real_term_rel_st_r2s  = KERealP2StateWaitReq2 (pt1, pt2, q2)) /\
  (st.`real_term_rel_st_fws1 =
     Fwd1.FwStateFinal
     ((st.`real_term_rel_st_func, 3), (st.`real_term_rel_st_func, 4),
      univ_triple (UnivPort pt1) (UnivPort pt2)
                  (UnivBase (BaseKey (g ^ q1))))) /\
  (st.`real_term_rel_st_fws2 = Fwd2.FwStateInit).

pred real_term_rel3 (met : int, st : real_term_rel_st, pt1 pt2 : port, q1 q2 : exp) =
  met = 1 /\
  ! (st.`real_term_rel_st_func <= pt1.`1) /\
  ! (st.`real_term_rel_st_func <= pt2.`1) /\
  (st.`real_term_rel_st_r1s  = KERealP1StateWaitFwd2 (pt1, pt2, q1)) /\
  (st.`real_term_rel_st_r2s  = KERealP2StateFinal (pt1, pt2, q2)) /\
  (st.`real_term_rel_st_fws1 =
     Fwd1.FwStateFinal
     ((st.`real_term_rel_st_func, 3), (st.`real_term_rel_st_func, 4),
      univ_triple (UnivPort pt1) (UnivPort pt2)
                  (UnivBase (BaseKey (g ^ q1))))) /\
  (st.`real_term_rel_st_fws2 =
     Fwd2.FwStateWait
     ((st.`real_term_rel_st_func, 4), (st.`real_term_rel_st_func, 3),
      UnivBase (BaseKey (g ^ q2)))).

pred real_term_rel4 (met : int, st : real_term_rel_st, pt1 pt2 : port, q1 q2 : exp) =
  met = 0 /\
  ! (st.`real_term_rel_st_func <= pt1.`1) /\
  ! (st.`real_term_rel_st_func <= pt2.`1) /\
  (st.`real_term_rel_st_r1s  = KERealP1StateFinal (pt1, pt2, q1)) /\
  (st.`real_term_rel_st_r2s  = KERealP2StateFinal (pt1, pt2, q2)) /\
  (st.`real_term_rel_st_fws1 =
     Fwd1.FwStateFinal
     ((st.`real_term_rel_st_func, 3), (st.`real_term_rel_st_func, 4),
      univ_triple (UnivPort pt1) (UnivPort pt2)
                  (UnivBase (BaseKey (g ^ q1))))) /\
  (st.`real_term_rel_st_fws2 =
     Fwd2.FwStateFinal
     ((st.`real_term_rel_st_func, 4), (st.`real_term_rel_st_func, 3),
      UnivBase (BaseKey (g ^ q2)))).

inductive real_term_rel (met : int, st : real_term_rel_st) =
    RealTermRel0 of (real_term_rel0 met st)
  | RealTermRel1 (pt1 pt2 : port, q1 : exp) of
      (real_term_rel1 met st pt1 pt2 q1)
  | RealTermRel2 (pt1 pt2 : port, q1 q2 : exp) of
      (real_term_rel2 met st pt1 pt2 q1 q2)
  | RealTermRel3 (pt1 pt2 : port, q1 q2 : exp) of
      (real_term_rel3 met st pt1 pt2 q1 q2)
  | RealTermRel4 (pt1 pt2 : port, q1 q2 : exp) of
      (real_term_rel4 met st pt1 pt2 q1 q2).

lemma real_term_rel_ge0_met (met : int, st : real_term_rel_st) :
  real_term_rel met st => 0 <= met.
proof. by case; delta. qed.

lemma KEReal_term_init (func adv : addr) :
  equiv
  [KEReal.init ~ KEReal.init :
   ={self_, adv_} /\ self_{1} = func /\ adv_{1} = adv ==>
   ={glob KEReal} /\
   KEReal.self{1} = func /\ KEReal.adv{1} = adv /\
   Fwd1.Forw.self{1} = func ++ [1] /\ Fwd1.Forw.adv{1} = adv /\
   Fwd2.Forw.self{1} = func ++ [2] /\ Fwd2.Forw.adv{1} = adv /\
   real_term_rel real_term_rel_metric_max
   {|real_term_rel_st_func = func;
     real_term_rel_st_r1s  = KEReal.st1{1};
     real_term_rel_st_r2s  = KEReal.st2{1};
     real_term_rel_st_fws1 = Fwd1.Forw.st{1};
     real_term_rel_st_fws2 = Fwd2.Forw.st{1}|}].
proof.
proc; inline*; auto; progress; by rewrite RealTermRel0.
qed.

lemma KEReal_term_invoke (func adv : addr, met : int) :
  equiv
  [KEReal.invoke ~ KEReal.invoke :
   ! func <= adv /\ ={m, glob KEReal} /\
   KEReal.self{1} = func /\ KEReal.adv{1} = adv /\
   Fwd1.Forw.self{1} = func ++ [1] /\ Fwd1.Forw.adv{1} = adv /\
   Fwd2.Forw.self{1} = func ++ [2] /\ Fwd2.Forw.adv{1} = adv /\
   real_term_rel met
   {|real_term_rel_st_func = func;
     real_term_rel_st_r1s  = KEReal.st1{1};
     real_term_rel_st_r2s  = KEReal.st2{1};
     real_term_rel_st_fws1 = Fwd1.Forw.st{1};
     real_term_rel_st_fws2 = Fwd2.Forw.st{1}|} ==>
   ={res, glob KEReal} /\
   ((exists met',
     met' < met /\
     real_term_rel met'
     {|real_term_rel_st_func = func;
       real_term_rel_st_r1s  = KEReal.st1{1};
       real_term_rel_st_r2s  = KEReal.st2{1};
       real_term_rel_st_fws1 = Fwd1.Forw.st{1};
       real_term_rel_st_fws2 = Fwd2.Forw.st{1}|}) \/
    res{1} = None /\
    real_term_rel met
    {|real_term_rel_st_func = func;
      real_term_rel_st_r1s  = KEReal.st1{1};
      real_term_rel_st_r2s  = KEReal.st2{1};
      real_term_rel_st_fws1 = Fwd1.Forw.st{1};
      real_term_rel_st_fws2 = Fwd2.Forw.st{1}|})].
proof.
proc.
case
  (real_term_rel0 met
   {|real_term_rel_st_func = func;
     real_term_rel_st_r1s  = KEReal.st1{1};
     real_term_rel_st_r2s  = KEReal.st2{1};
     real_term_rel_st_fws1 = Fwd1.Forw.st{1};
     real_term_rel_st_fws2 = Fwd2.Forw.st{1}|}).
sp 3 3.
if => //.
inline KEReal.loop.
wp; sp 3 3.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
if => //.
inline{1} (1) KEReal.party1. inline{2} (1) KEReal.party1.
rcondt{1} 3; first auto; smt(). rcondt{2} 3; first auto; smt().
sp 2 2.
if => //.
sp 1 1.
if; first move => |> &1 &2 <- //.
seq 1 1 :
  (! func <= adv /\ ={m, glob KEReal} /\
   KEReal.self{1} = func /\ KEReal.adv{1} = adv /\
   Fwd1.Forw.self{1} = func ++ [1] /\ Fwd1.Forw.adv{1} = adv /\
   Fwd2.Forw.self{1} = func ++ [2] /\ Fwd2.Forw.adv{1} = adv /\
   real_term_rel0 met
   {|real_term_rel_st_func = func;
     real_term_rel_st_r1s  = KEReal.st1{1};
     real_term_rel_st_r2s  = KEReal.st2{1};
     real_term_rel_st_fws1 = Fwd1.Forw.st{1};
     real_term_rel_st_fws2 = Fwd2.Forw.st{1}|} /\
   ={q1, pt10, pt20} /\ not_done{1} /\ not_done{2} /\
   ! KEReal.self{1} <= pt10{1}.`1 /\
   ! KEReal.self{1} <= pt20{1}.`1).
by auto => |> &1 &2 <-.
rcondf{1} 4; first auto;
  progress; rewrite oget_some /fw_req /= le_ext_r.
rcondf{2} 4; first auto;
  progress; rewrite oget_some /fw_req /= le_ext_r.
rcondt{1} 5; first auto. rcondt{2} 5; first auto.
rcondf{1} 5; first auto; progress;
  by rewrite oget_some /fw_req /= ne_cat_nonnil_r.
rcondf{2} 5; first auto; progress;
  by rewrite oget_some /fw_req /= ne_cat_nonnil_r.
rcondf{1} 5; first auto; progress;
  by rewrite oget_some /fw_req /= ne_cat_nonnil_r.
rcondf{2} 5; first auto; progress;
  by rewrite oget_some /fw_req /= ne_cat_nonnil_r.
rcondt{1} 5; first auto; progress;
  rewrite oget_some /fw_req /= le_refl.
rcondt{2} 5; first auto; progress;
  rewrite oget_some /fw_req /= le_refl.
inline{1} (1) Fwd1.Forw.invoke. inline{2} (1) Fwd1.Forw.invoke.
rcondt{1} 7; first auto; smt(). rcondt{2} 7; first auto; smt().
rcondt{1} 7; first auto. rcondt{2} 7; first auto.
rcondt{1} 8; first auto; progress;
  [by rewrite oget_some Fwd1.enc_dec_fw_req oget_some |
   by rewrite oget_some Fwd1.enc_dec_fw_req oget_some /=
              not_le_ext_nonnil_l |
   by rewrite oget_some Fwd1.enc_dec_fw_req oget_some /=
              not_le_ext_nonnil_l].
rcondt{2} 8; first auto; progress;
  [by rewrite oget_some Fwd1.enc_dec_fw_req oget_some |
   by rewrite oget_some Fwd1.enc_dec_fw_req oget_some /=
              not_le_ext_nonnil_l |
   by rewrite oget_some Fwd1.enc_dec_fw_req oget_some /=
              not_le_ext_nonnil_l].
rcondt{1} 11; first auto. rcondt{2} 11; first auto.
rcondf{1} 12; first auto. rcondf{2} 12; first auto.
auto; progress; exists (met - 1).
split; first smt().
rewrite oget_some Fwd1.enc_dec_fw_req oget_some /=
        (RealTermRel1 (met - 1) _ pt10{2} pt20{2} q1{2})
        /#.
rcondt{1} 2; first auto. rcondt{2} 2; first auto.
rcondf{1} 3; first auto. rcondf{2} 3; first auto.
auto; progress; right; trivial.
rcondt{1} 2; first auto. rcondt{2} 2; first auto.
rcondf{1} 3; first auto. rcondf{2} 3; first auto.
auto; progress; right; trivial.
if => //.
inline{1} (1) KEReal.party2. inline{2} (1) KEReal.party2.
rcondt{1} 3; first auto; smt(). rcondt{2} 3; first auto; smt().
sp 2 2.
if => //.
rcondf{1} 2; first auto => &hr |> _ _ _ [];
  [smt(Fwd1.dest_good_fw_rsp) |
   move => [#] -> _;
   rewrite /Fwd1.is_fw_rsp /Fwd1.dec_fw_rsp /#].
rcondf{2} 2; first auto => &hr |> _ _ _ [];
  [smt(Fwd1.dest_good_fw_rsp) |
   move => [#] -> _;
   rewrite /Fwd1.is_fw_rsp /Fwd1.dec_fw_rsp /#].
rcondt{1} 3; first auto. rcondt{2} 3; first auto.
rcondf{1} 4; first auto. rcondf{2} 4; first auto.
auto; progress; right; trivial.
rcondt{1} 2; first auto. rcondt{2} 2; first auto.
rcondf{1} 3; first auto. rcondf{2} 3; first auto.
auto; progress; right; trivial.
if => //.
inline{1} (1) Fwd1.Forw.invoke. inline{2} (1) Fwd1.Forw.invoke.
rcondt{1} 3; first auto; smt(). rcondt{2} 3; first auto; smt().
rcondf{1} 3; first auto; smt(). rcondf{2} 3; first auto; smt().
rcondt{1} 4; first auto. rcondt{2} 4; first auto.
rcondf{1} 5; first auto. rcondf{2} 5; first auto.
auto; progress; right; trivial.
inline{1} (1) Fwd2.Forw.invoke. inline{2} (1) Fwd2.Forw.invoke.
rcondt{1} 3; first auto; smt(). rcondt{2} 3; first auto; smt().
rcondf{1} 3; first auto; smt(). rcondf{2} 3; first auto; smt().
rcondt{1} 4; first auto. rcondt{2} 4; first auto.
rcondf{1} 5; first auto. rcondf{2} 5; first auto.
auto; progress; right; trivial.
auto; progress; right; trivial.
case
  (exists pt1 pt2 q1,
   real_term_rel1 met
   {|real_term_rel_st_func = func;
     real_term_rel_st_r1s  = KEReal.st1{1};
     real_term_rel_st_r2s  = KEReal.st2{1};
     real_term_rel_st_fws1 = Fwd1.Forw.st{1};
     real_term_rel_st_fws2 = Fwd2.Forw.st{1}|}
   pt1 pt2 q1).
elim* => pt1' pt2' q1'.
sp 3 3.
if => //.
inline KEReal.loop.
wp; sp 3 3.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
if => //.
inline{1} (1) KEReal.party1. inline{2} (1) KEReal.party1.
rcondf{1} 3; first auto; smt(). rcondf{2} 3; first auto; smt().
rcondt{1} 3; first auto; smt(is_ke_real_p1_state_wait_fwd2).
rcondt{2} 3; first auto; smt(is_ke_real_p1_state_wait_fwd2).
sp 3 3.
if => //.
rcondf{1} 2; first auto => &hr |> _ _ _ _ _ _ [];
  [smt(Fwd2.dest_good_fw_rsp) |
   rewrite /Fwd2.is_fw_rsp /Fwd2.dec_fw_rsp /#].
rcondf{2} 2; first auto => &hr |> _ _ _ _ _ _ [];
  [smt(Fwd2.dest_good_fw_rsp) |
   rewrite /Fwd2.is_fw_rsp /Fwd2.dec_fw_rsp /#].
rcondt{1} 3; first auto. rcondt{2} 3; first auto.
rcondf{1} 4; first auto. rcondf{2} 4; first auto.
auto; progress; right; trivial.
rcondt{1} 2; first auto. rcondt{2} 2; first auto.
rcondf{1} 3; first auto. rcondf{2} 3; first auto.
auto; progress; right; trivial.
if => //.
inline{1} (1) KEReal.party2. inline{2} (1) KEReal.party2.
rcondt{1} 3; first auto; smt().
rcondt{2} 3; first auto; smt().
sp 2 2.
if => //.
rcondf{1} 2; first auto => &hr |> _ _ _ _ _ _ [];
  [smt(Fwd1.dest_good_fw_rsp) |
   rewrite /Fwd1.is_fw_rsp /Fwd1.dec_fw_rsp /#].
rcondf{2} 2; first auto => &hr |> _ _ _ _ _ _ [];
  [smt(Fwd1.dest_good_fw_rsp) |
   rewrite /Fwd1.is_fw_rsp /Fwd1.dec_fw_rsp /#].
rcondt{1} 3; first auto. rcondt{2} 3; first auto.
rcondf{1} 4; first auto. rcondf{2} 4; first auto.
auto; progress; right; trivial.
rcondt{1} 2; first auto. rcondt{2} 2; first auto.
rcondf{1} 3; first auto. rcondf{2} 3; first auto.
auto; progress; right; trivial.
if => //.
inline{1} (1) Fwd1.Forw.invoke. inline{2} (1) Fwd1.Forw.invoke.
rcondf{1} 3; first auto; smt(). rcondf{2} 3; first auto; smt().
rcondt{1} 3; first auto; smt(Fwd1.is_fw_state_wait).
rcondt{2} 3; first auto; smt(Fwd1.is_fw_state_wait).
sp 3 3.
if => //.
sp 1 1.
if.
auto => &1 &2 [#] dec_fw_ok2 dec_fw_ok1 ->> _ _ ->> _ _
        ->> _ _ ->> _ _ _ _ _ _ _ _ _ ->> _ _ _ _ _ _ _
        _ _ -> _ _ _ _ _ _ _ _ _ _ _ _ _ _.
rewrite -dec_fw_ok2 in dec_fw_ok1.
by elim dec_fw_ok1 => ->.
rcondf{1} 4; first auto => |> &hr.
rewrite oget_some /Fwd1.fw_rsp /=.
move => _ _ ^ dec_fwd_state <- [#] _ -> _ _ _ _
        [] /= _ [#] _ _ _ _ ->> _ _ _ _ _ _.
rewrite /= oget_some /= in dec_fwd_state.
elim dec_fwd_state => _ [#] -> _ /=.
rewrite le_refl.
rcondf{2} 4; first auto => |> &hr.
rewrite oget_some /Fwd1.fw_rsp /=.
move => _ _ ^ dec_fwd_state _ _ _ _ _ [] _ /=
        [#] _ _ _ _ ->> _ _ _ _ _ _.
rewrite /= oget_some /= in dec_fwd_state.
elim dec_fwd_state => _ [#] -> _ /=.
rewrite le_refl.
rcondt{1} 5; first auto. rcondt{2} 5; first auto.
rcondf{1} 5; first auto => |> &hr.
rewrite oget_some /Fwd1.fw_rsp /=.
move => _ _ ^ dec_fwd_state <- [#] _ -> _ _ _ _ []
        _ /= [#] _ _ _ _ ->> _ _ _ _ _ _.
rewrite /= oget_some /= in dec_fwd_state.
by elim dec_fwd_state => _ [#] -> _.
rcondf{2} 5; first auto => |> &hr.
rewrite oget_some /Fwd1.fw_rsp /=.
move => _ _ ^ dec_fwd_state <- [#] _ _ _ _ _ _ []
        _ /= [#] _ _ _ _ ->> _ _ _ _ _ _.
rewrite /= oget_some /= in dec_fwd_state.
by elim dec_fwd_state => _ [#] -> _.
rcondt{1} 5; first auto => |> &hr.
rewrite oget_some /Fwd1.fw_rsp /=.
move => _ _ ^ dec_fwd_state <- [#] _ -> _ _ _ _ []
        _ /= [#] _ _ _ _ ->> _ _ _ _ _ _.
rewrite /= oget_some /= in dec_fwd_state.
by elim dec_fwd_state => _ [#] -> _.
rcondt{2} 5; first auto => |> &hr.
rewrite oget_some /Fwd1.fw_rsp /=.
move => _ _ ^ dec_fwd_state <- [#] _ _ _ _ _ _ []
        _ /= [#] _ _ _ _ ->> _ _ _ _ _ _.
rewrite /= oget_some /= in dec_fwd_state.
by elim dec_fwd_state => _ [#] -> _.
inline{1} (1) KEReal.party2. inline{2} (1) KEReal.party2.
rcondt{1} 7; first auto; smt(). rcondt{2} 7; first auto; smt().
rcondt{1} 7; first auto; smt(). rcondt{2} 7; first auto; smt().
rcondt{1} 8; first auto => |> &hr.
rewrite oget_some Fwd1.enc_dec_fw_rsp oget_some /=.
move => _ _ ^ dec_fwd_state <- [#] _ -> _ _ _ _ []
        _ /= [#] _ _ _ _ ->> _ _ _ _ _ _.
rewrite /= oget_some /= in dec_fwd_state.
by elim dec_fwd_state => _ [#] -> _.
rcondt{2} 8; first auto => |> &hr.
rewrite oget_some Fwd1.enc_dec_fw_rsp oget_some /=.
move => _ _ ^ dec_fwd_state <- [#] _ _ _ _ _ _ []
        _ /= [#] _ _ _ _ ->> _ _ _ _ _ _.
rewrite /= oget_some /= in dec_fwd_state.
by elim dec_fwd_state => _ [#].
rcondt{1} 16; first auto.
move => |> &hr _ _ ^ dec_fwd_state <- [#] -> -> ->
        _ _ _ [] _ /= [#] _ _ _ _ ->> _ _ _ _ _ _ q20 _.
rewrite !oget_some /= Fwd1.enc_dec_fw_rsp oget_some /ke_rsp1 /=.
rewrite /= oget_some /= in dec_fwd_state.
elim dec_fwd_state => _ [#] _ -> /=.
by rewrite enc_dec_univ_triple oget_some /= oget_some.
rcondt{2} 16; first auto.
move => |> &hr _ _ ^ dec_fwd_state <- [#] _ _ _
        _ _ _ [] _ /= [#] _ _ _ _ ->> _ _ _ _ _ _ q20 _.
rewrite !oget_some /= Fwd1.enc_dec_fw_rsp oget_some /ke_rsp1 /=.
rewrite /= oget_some /= in dec_fwd_state.
elim dec_fwd_state => _ [#] _ -> /=.
by rewrite enc_dec_univ_triple oget_some /= oget_some.
rcondf{1} 17; first auto. rcondf{2} 17; first auto.
auto => |> &1 &2 _ _ ^ dec_fwd_state <- [#] -> -> -> _ _ _
        [] -> /= [#] pt1'_out pt2'_out -> _ ->> ->
        _ _ _ _ _ q2L _.
rewrite !oget_some !Fwd1.enc_dec_fw_rsp !oget_some /=.
rewrite /= oget_some /= in dec_fwd_state.
elim dec_fwd_state => -> [#] -> ->.
exists 2. split => //.
by rewrite /= enc_dec_univ_triple oget_some /= !oget_some
          (RealTermRel2 _ _ pt1' pt2' q1' q2L)
          /real_term_rel2.
rcondt{1} 2; first auto. rcondt{2} 2; first auto.
rcondf{1} 3; first auto. rcondf{2} 3; first auto.
auto; progress; right; trivial.
rcondt{1} 2; first auto. rcondt{2} 2; first auto.
rcondf{1} 3; first auto. rcondf{2} 3; first auto.
auto; progress; right; trivial.
inline{1} (1) Fwd2.Forw.invoke. inline{2} (1) Fwd2.Forw.invoke.
rcondt{1} 3; first auto; smt(). rcondt{2} 3; first auto; smt().
rcondf{1} 3; first auto; smt(). rcondf{2} 3; first auto; smt().
rcondt{1} 4; first auto. rcondt{2} 4; first auto.
rcondf{1} 5; first auto. rcondf{2} 5; first auto.
auto; progress; right; trivial.
auto; progress; right; trivial.
case
  (exists pt1 pt2 q1 q2,
   real_term_rel2 met
   {|real_term_rel_st_func = func;
     real_term_rel_st_r1s  = KEReal.st1{1};
     real_term_rel_st_r2s  = KEReal.st2{1};
     real_term_rel_st_fws1 = Fwd1.Forw.st{1};
     real_term_rel_st_fws2 = Fwd2.Forw.st{1}|}
   pt1 pt2 q1 q2).
elim* => pt1' pt2' q1' q2'.
sp 3 3.
if => //.
inline KEReal.loop.
wp; sp 3 3.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
if => //.
inline{1} (1) KEReal.party1. inline{2} (1) KEReal.party1.
rcondf{1} 3; first auto; smt(). rcondf{2} 3; first auto; smt().
rcondt{1} 3; first auto; smt(is_ke_real_p1_state_wait_fwd2).
rcondt{2} 3; first auto; smt(is_ke_real_p1_state_wait_fwd2).
sp 3 3.
if => //.
rcondf{1} 2; first auto => &hr |> _ _ _ _ _ _ _ [];
  [smt(Fwd2.dest_good_fw_rsp) |
   move => [#] -> _;
   rewrite /Fwd2.is_fw_rsp /Fwd2.dec_fw_rsp /#].
rcondf{2} 2; first auto => &hr |> _ _ _ _ _ _ _ [];
  [smt(Fwd2.dest_good_fw_rsp) |
   move => [#] -> _;
   rewrite /Fwd2.is_fw_rsp /Fwd2.dec_fw_rsp /#].
rcondt{1} 3; first auto. rcondt{2} 3; first auto.
rcondf{1} 4; first auto. rcondf{2} 4; first auto.
auto; progress; right; trivial.
rcondt{1} 2; first auto. rcondt{2} 2; first auto.
rcondf{1} 3; first auto. rcondf{2} 3; first auto.
auto; progress; right; trivial.
if => //.
inline{1} (1) KEReal.party2. inline{2} (1) KEReal.party2.
rcondf{1} 3; first auto; smt(). rcondf{2} 3; first auto; smt().
rcondt{1} 3; first auto; smt(is_ke_real_p2_state_wait_req2).
rcondt{2} 3; first auto; smt(is_ke_real_p2_state_wait_req2).
sp 3 3.
if => //.
sp 1 1.
if.
move => &1 &2 [#] dec_req2_2 dec_req2_1 ->> _ dec_p2_wait_req2_2 ->>
        _ dec_p2_wait_req2_1 ->> _ _ ->> _ _ _ _ _ _ _ _ _ ->> ->>.
rewrite -dec_req2_2 in dec_req2_1.
elim dec_req2_1 => _ ->.
rewrite -dec_p2_wait_req2_2 in dec_p2_wait_req2_1.
by elim dec_p2_wait_req2_1 => _ ->.
rcondf{1} 4; first auto;
  progress; rewrite oget_some /fw_req /= le_ext_r.
rcondf{2} 4; first auto;
  progress; rewrite oget_some /fw_req /= le_ext_r.
rcondt{1} 5; first auto. rcondt{2} 5; first auto.
rcondf{1} 5; first auto; progress;
  by rewrite oget_some /fw_req /= ne_cat_nonnil_r.
rcondf{2} 5; first auto; progress;
  by rewrite oget_some /fw_req /= ne_cat_nonnil_r.
rcondf{1} 5; first auto; progress;
  by rewrite oget_some /fw_req /= ne_cat_nonnil_r.
rcondf{2} 5; first auto; progress;
  by rewrite oget_some /fw_req /= ne_cat_nonnil_r.
rcondf{1} 5; first auto; progress;
  rewrite oget_some /fw_req /=
          (not_le_other_branch KEReal.self{m}
           (KEReal.self{m} ++ [2]) 2 1) // le_refl.
rcondf{2} 5; first auto; progress;
  rewrite oget_some /fw_req /=
          (not_le_other_branch KEReal.self{hr}
           (KEReal.self{hr} ++ [2]) 2 1) // le_refl.
inline{1} (1) Fwd2.Forw.invoke. inline{2} (1) Fwd2.Forw.invoke.
rcondt{1} 7; first auto; smt(). rcondt{2} 7; first auto; smt().
rcondt{1} 7; first auto. rcondt{2} 7; first auto.
rcondt{1} 8; first auto; progress;
  [by rewrite oget_some Fwd2.enc_dec_fw_req oget_some |
   by rewrite oget_some Fwd2.enc_dec_fw_req oget_some /=
              not_le_ext_nonnil_l |
   by rewrite oget_some Fwd2.enc_dec_fw_req oget_some /=
              not_le_ext_nonnil_l].
rcondt{2} 8; first auto; progress;
  [by rewrite oget_some Fwd2.enc_dec_fw_req oget_some |
   by rewrite oget_some Fwd2.enc_dec_fw_req oget_some /=
              not_le_ext_nonnil_l |
   by rewrite oget_some Fwd2.enc_dec_fw_req oget_some /=
              not_le_ext_nonnil_l].
rcondt{1} 11; first auto. rcondt{2} 11; first auto.
rcondf{1} 12; first auto. rcondf{2} 12; first auto.
auto => |> &1 &2 _ _.
rewrite !oget_some !Fwd2.enc_dec_fw_req !/Fwd2.fw_obs !oget_some /=.
move => ^ dec_p2_wait_req2 <- [#] -> -> -> _ _ _ _
        [] -> /= [#] pt1'_out pt2'_out -> ->> _ _ _ _ _ _.
rewrite /= oget_some in dec_p2_wait_req2.
elim dec_p2_wait_req2 => -> -> ->.
exists 1; split => //.
by rewrite (RealTermRel3 1 _ pt1' pt2' q1' q2').
rcondt{1} 2; first auto. rcondt{2} 2; first auto.
rcondf{1} 3; first auto. rcondf{2} 3; first auto.
auto; progress; right; trivial.
rcondt{1} 2; first auto. rcondt{2} 2; first auto.
rcondf{1} 3; first auto. rcondf{2} 3; first auto.
auto; progress; right; trivial.
if => //.
inline{1} (1) Fwd1.Forw.invoke. inline{2} (1) Fwd1.Forw.invoke.
rcondf{1} 3; first auto; smt(). rcondf{2} 3; first auto; smt().
rcondf{1} 3; first auto; smt(Fwd1.is_fw_state_wait).
rcondf{2} 3; first auto; smt(Fwd1.is_fw_state_wait).
rcondt{1} 4; first auto. rcondt{2} 4; first auto.
rcondf{1} 5; first auto. rcondf{2} 5; first auto.
auto; progress; right; trivial.
inline{1} (1) Fwd2.Forw.invoke. inline{2} (1) Fwd2.Forw.invoke.
rcondt{1} 3; first auto; smt(). rcondt{2} 3; first auto; smt().
rcondf{1} 3; first auto; smt(). rcondf{2} 3; first auto; smt().
rcondt{1} 4; first auto. rcondt{2} 4; first auto.
rcondf{1} 5; first auto. rcondf{2} 5; first auto.
auto; progress; right; trivial.
auto; progress; right; trivial.
case
  (exists pt1 pt2 q1 q2,
   real_term_rel3 met
   {|real_term_rel_st_func = func;
     real_term_rel_st_r1s  = KEReal.st1{1};
     real_term_rel_st_r2s  = KEReal.st2{1};
     real_term_rel_st_fws1 = Fwd1.Forw.st{1};
     real_term_rel_st_fws2 = Fwd2.Forw.st{1}|}
   pt1 pt2 q1 q2).
elim* => pt1' pt2' q1' q2'.
sp 3 3.
if => //.
inline KEReal.loop.
wp; sp 3 3.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
if => //.
inline{1} (1) KEReal.party1. inline{2} (1) KEReal.party1.
rcondf{1} 3; first auto; smt(). rcondf{2} 3; first auto; smt().
rcondt{1} 3; first auto; smt(is_ke_real_p1_state_wait_fwd2).
rcondt{2} 3; first auto; smt(is_ke_real_p1_state_wait_fwd2).
sp 3 3.
if => //.
rcondf{1} 2; first auto => &hr |> _ _ _ _ _ _ _ _ [];
  [smt(Fwd2.dest_good_fw_rsp) |
   rewrite /Fwd2.is_fw_rsp /Fwd2.dec_fw_rsp /#].
rcondf{2} 2; first auto => &hr |> _ _ _ _ _ _ _ _ [];
  [smt(Fwd2.dest_good_fw_rsp) |
   rewrite /Fwd2.is_fw_rsp /Fwd2.dec_fw_rsp /#].
rcondt{1} 3; first auto. rcondt{2} 3; first auto.
rcondf{1} 4; first auto. rcondf{2} 4; first auto.
auto; progress; right; trivial.
rcondt{1} 2; first auto. rcondt{2} 2; first auto.
rcondf{1} 3; first auto. rcondf{2} 3; first auto.
auto; progress; right; trivial.
if => //.
inline{1} (1) KEReal.party2. inline{2} (1) KEReal.party2.
rcondf{1} 3; first auto; smt(). rcondf{2} 3; first auto; smt().
rcondf{1} 3; first auto; smt(is_ke_real_p2_state_wait_req2).
rcondf{2} 3; first auto; smt(is_ke_real_p2_state_wait_req2).
rcondt{1} 4; first auto. rcondt{2} 4; first auto.
rcondf{1} 5; first auto. rcondf{2} 5; first auto.
auto; progress; right; trivial.
if => //.
inline{1} (1) Fwd1.Forw.invoke. inline{2} (1) Fwd1.Forw.invoke.
rcondf{1} 3; first auto; smt(). rcondf{2} 3; first auto; smt().
rcondf{1} 3; first auto; smt(Fwd1.is_fw_state_wait).
rcondf{2} 3; first auto; smt(Fwd1.is_fw_state_wait).
rcondt{1} 4; first auto. rcondt{2} 4; first auto.
rcondf{1} 5; first auto. rcondf{2} 5; first auto.
auto; progress; right; trivial.
inline{1} (1) Fwd2.Forw.invoke. inline{2} (1) Fwd2.Forw.invoke.
rcondf{1} 3; first auto; smt(). rcondf{2} 3; first auto; smt().
rcondt{1} 3; first auto; smt(Fwd2.is_fw_state_wait).
rcondt{2} 3; first auto; smt(Fwd2.is_fw_state_wait).
sp 3 3.
if => //.
sp 1 1.
if.
auto => &1 &2 [#] dec_fw_ok2 dec_fw_ok1 ->> _ _ ->> _ _
        ->> _ _ ->> _ _ _ _ _ _ _ _ _ ->> _ _ _ _ _ _ ->
        _ _ -> _ _ _ _ _ _ _ _ _ _ _ _ _ _.
rewrite -dec_fw_ok2 in dec_fw_ok1.
by elim dec_fw_ok1 => ->.
rcondf{1} 4; first auto => |> &hr.
rewrite oget_some /Fwd2.fw_rsp /=.
move => _ _ ^ dec_fwd_state <- [#] _ -> _ _ _ _ _ _
        [] /= _ [#] _ _ _ _ _ ->> _ _ _ _ _.
rewrite /= oget_some /= in dec_fwd_state.
elim dec_fwd_state => _ [#] -> _ /=.
rewrite le_refl.
rcondf{2} 4; first auto => |> &hr.
rewrite oget_some /Fwd2.fw_rsp /=.
move => _ _ ^ dec_fwd_state _ _ _ _ _ _ _ [] _ /=
        [#] _ _ _ _ _ ->> _ _ _ _ _.
rewrite /= oget_some /= in dec_fwd_state.
elim dec_fwd_state => _ [#] -> _ /=.
rewrite le_refl.
rcondt{1} 5; first auto. rcondt{2} 5; first auto.
rcondt{1} 5; first auto => |> &hr.
rewrite oget_some /Fwd2.fw_rsp /=.
move => _ _ ^ dec_fwd_state <- [#] _ -> _ _ _ _ _ _ []
        _ /= [#] _ _ _ _ _ ->> _ _ _ _ _.
rewrite /= oget_some /= in dec_fwd_state.
by elim dec_fwd_state => _ [#] -> _.
rcondt{2} 5; first auto => |> &hr.
rewrite oget_some /Fwd2.fw_rsp /=.
move => _ _ ^ dec_fwd_state <- [#] _ _ _ _ _ _ _ _ []
        _ /= [#] _ _ _ _ _ ->> _ _ _ _ _.
rewrite /= oget_some /= in dec_fwd_state.
by elim dec_fwd_state => _ [#] -> _.
inline{1} (1) KEReal.party1. inline{2} (1) KEReal.party1.
rcondf{1} 7; first auto; smt(). rcondf{2} 7; first auto; smt().
rcondt{1} 7; first auto; smt(is_ke_real_p1_state_wait_fwd2).
rcondt{2} 7; first auto; smt(is_ke_real_p1_state_wait_fwd2).
rcondt{1} 8; first auto; smt(). rcondt{2} 8; first auto; smt().
rcondt{1} 9; first auto => |> &hr.
rewrite oget_some Fwd2.enc_dec_fw_rsp oget_some /=.
move => _ _ ^ dec_fwd_state <- [#] _ -> _ _ _ _ _ _ []
        _ /= [#] _ _ _ _ _ ->> _ _ _ _ _.
rewrite /= oget_some /= in dec_fwd_state.
by elim dec_fwd_state => _ [#] -> _.
rcondt{2} 9; first auto => |> &hr.
rewrite oget_some Fwd2.enc_dec_fw_rsp oget_some /=.
move => _ _ ^ dec_fwd_state <- [#] _ _ _ _ _ _ _ _ []
        _ /= [#] _ _ _ _ _ ->> _ _ _ _ _.
rewrite /= oget_some /= in dec_fwd_state.
by elim dec_fwd_state => _ [#].
rcondt{1} 13; first auto.
move => |> &hr _ _ <- [#] -> -> -> _ _ _ _ _ [] _ /=
        [#] pt1'_out pt2'_out -> //.
rcondt{2} 13; first auto.
move => |> &hr _ _ <- [#] _ _ _  _ _ _ _ _ [] _ /=
        [#] pt1'_out pt2'_out -> //.
rcondf{1} 14; first auto. rcondf{2} 14; first auto.
auto => |> &1 &2 _ _ ^ dec_fwd_state <- [#] -> -> -> _ _ _ _ _
        [] -> /= [#] pt1'_out pt2'_out -> _ _ ->>
        _ _ _ _ _.
rewrite /= oget_some /= in dec_fwd_state.
elim dec_fwd_state => -> [#] -> ->.
exists 0; split => //.
rewrite /= oget_some (RealTermRel4 _ _ pt1' pt2' q1' q2')
        /real_term_rel4 /= /#.
rcondt{1} 2; first auto. rcondt{2} 2; first auto.
rcondf{1} 3; first auto. rcondf{2} 3; first auto.
auto; progress; right; trivial.
rcondt{1} 2; first auto. rcondt{2} 2; first auto.
rcondf{1} 3; first auto. rcondf{2} 3; first auto.
auto; progress; right; trivial.
auto; progress; right; trivial.
case
  (exists pt1 pt2 q1 q2,
   real_term_rel4 met
   {|real_term_rel_st_func = func;
     real_term_rel_st_r1s  = KEReal.st1{1};
     real_term_rel_st_r2s  = KEReal.st2{1};
     real_term_rel_st_fws1 = Fwd1.Forw.st{1};
     real_term_rel_st_fws2 = Fwd2.Forw.st{1}|}
   pt1 pt2 q1 q2).
elim* => pt1' pt2' q1' q2'.
sp 3 3.
if => //.
inline KEReal.loop.
wp; sp 3 3.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
if => //.
inline{1} (1) KEReal.party1. inline{2} (1) KEReal.party1.
rcondf{1} 3; first auto; smt(). rcondf{2} 3; first auto; smt().
rcondf{1} 3; first auto; smt(is_ke_real_p1_state_wait_fwd2).
rcondf{2} 3; first auto; smt(is_ke_real_p1_state_wait_fwd2).
rcondt{1} 4; first auto. rcondt{2} 4; first auto.
rcondf{1} 5; first auto. rcondf{2} 5; first auto.
auto; progress; right; trivial.
if => //.
inline{1} (1) KEReal.party2. inline{2} (1) KEReal.party2.
rcondf{1} 3; first auto; smt(). rcondf{2} 3; first auto; smt().
rcondf{1} 3; first auto; smt(is_ke_real_p1_state_wait_fwd2).
rcondf{2} 3; first auto; smt(is_ke_real_p1_state_wait_fwd2).
rcondt{1} 4; first auto. rcondt{2} 4; first auto.
rcondf{1} 5; first auto. rcondf{2} 5; first auto.
auto; progress; right; trivial.
if => //.
inline{1} (1) Fwd1.Forw.invoke. inline{2} (1) Fwd1.Forw.invoke.
rcondf{1} 3; first auto; smt(). rcondf{2} 3; first auto; smt().
rcondf{1} 3; first auto; smt(Fwd1.is_fw_state_wait).
rcondf{2} 3; first auto; smt(Fwd1.is_fw_state_wait).
rcondt{1} 4; first auto. rcondt{2} 4; first auto.
rcondf{1} 5; first auto. rcondf{2} 5; first auto.
auto; progress; right; trivial.
inline{1} (1) Fwd2.Forw.invoke. inline{2} (1) Fwd2.Forw.invoke.
rcondf{1} 3; first auto; smt(). rcondf{2} 3; first auto; smt().
rcondf{1} 3; first auto; smt(Fwd2.is_fw_state_wait).
rcondf{2} 3; first auto; smt(Fwd2.is_fw_state_wait).
rcondt{1} 4; first auto. rcondt{2} 4; first auto.
rcondf{1} 5; first auto. rcondf{2} 5; first auto.
auto; progress; right; trivial.
auto; progress; right; trivial.
exfalso => &1 &2 [#] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ []; smt().
qed.

(* termination metric and proof for KEIdeal *)

type ideal_term_rel_st = {
  ideal_term_rel_st_is   : ke_ideal_state;
}.

op ideal_term_rel_metric_max : int = 4.

pred ideal_term_rel0 (met : int, st : ideal_term_rel_st) =
  met = 4 /\
  (st.`ideal_term_rel_st_is = KEIdealStateWaitReq1).

pred ideal_term_rel1 (met : int, st : ideal_term_rel_st, pt1 pt2 : port) =
  met = 3 /\
  (st.`ideal_term_rel_st_is = KEIdealStateWaitSim1 (pt1, pt2)).

pred ideal_term_rel2 (met : int, st : ideal_term_rel_st, pt1 pt2 : port, q : exp) =
  met = 2 /\
  (st.`ideal_term_rel_st_is = KEIdealStateWaitReq2 (pt1, pt2, q)).

pred ideal_term_rel3 (met : int, st : ideal_term_rel_st, pt1 pt2 : port, q : exp) =
  met = 1 /\
  (st.`ideal_term_rel_st_is = KEIdealStateWaitSim2 (pt1, pt2, q)).

pred ideal_term_rel4 (met : int, st : ideal_term_rel_st, pt1 pt2 : port, q : exp) =
  met = 0 /\
  (st.`ideal_term_rel_st_is = KEIdealStateFinal (pt1, pt2, q)).

inductive ideal_term_rel (met : int, st : ideal_term_rel_st) =
    IdealTermRel0 of (ideal_term_rel0 met st)
  | IdealTermRel1 (pt1 pt2 : port) of
      (ideal_term_rel1 met st pt1 pt2)
  | IdealTermRel2 (pt1 pt2 : port, q : exp) of
      (ideal_term_rel2 met st pt1 pt2 q)
  | IdealTermRel3 (pt1 pt2 : port, q : exp) of
      (ideal_term_rel3 met st pt1 pt2 q)
  | IdealTermRel4 (pt1 pt2 : port, q : exp) of
      (ideal_term_rel4 met st pt1 pt2 q).

lemma ideal_term_rel_ge0_met (met : int, st : ideal_term_rel_st) :
  ideal_term_rel met st => 0 <= met.
proof. by case; delta. qed.

lemma KEIdeal_term_init (func : addr) :
  equiv
  [KEIdeal.init ~ KEIdeal.init :
   ={self_, adv_} /\ self_{1} = func ==>
   ={glob KEIdeal} /\ KEIdeal.self{1} = func /\
   ideal_term_rel ideal_term_rel_metric_max
   {|ideal_term_rel_st_is = KEIdeal.st{1};|}].
proof.
proc; inline*; auto; progress; by rewrite IdealTermRel0.
qed.

lemma KEIdeal_term_invoke (func adv : addr, met : int) :
  equiv
  [KEIdeal.invoke ~ KEIdeal.invoke :
   ={m, glob KEIdeal} /\ KEIdeal.self{1} = func /\
   ideal_term_rel met
   {|ideal_term_rel_st_is = KEIdeal.st{1};|} ==>
   ={res, glob KEIdeal} /\
   ((exists met',
     met' < met /\
     ideal_term_rel met'
     {|ideal_term_rel_st_is = KEIdeal.st{1}|}) \/
    res{1} = None /\
    ideal_term_rel met
    {|ideal_term_rel_st_is = KEIdeal.st{1}|})].
proof.
proc.
case
  (ideal_term_rel0 met
   {|ideal_term_rel_st_is = KEIdeal.st{1}|}).
sp 3 3.
if => //.
inline KEIdeal.parties.
rcondt{1} 3; first auto; smt(). rcondt{2} 3; first auto; smt().
sp 2 2.
if => //.
sp 1 1.
if; first move => |> &1 &2 <- //.
auto => |> &1 &2 <- [#] _ -> -> _ []-> /=.
progress; exists 3.
by rewrite (IdealTermRel1 3 _ pt10{2} pt20{2}).
auto; progress; right; trivial.
auto; progress; right; trivial.
auto; progress; right; trivial.
case
  (exists pt1 pt2,
   ideal_term_rel1 met
   {|ideal_term_rel_st_is = KEIdeal.st{1}|}
   pt1 pt2).
elim* => pt1' pt2'.
sp 3 3.
if => //.
inline KEIdeal.parties.
rcondf{1} 3; first auto; smt(). rcondf{2} 3; first auto; smt().
rcondt{1} 3; first auto; smt(is_ke_ideal_state_wait_sim1).
rcondt{2} 3; first auto; smt(is_ke_ideal_state_wait_sim1).
sp 3 3.
if => //.
auto => |> &1 &2 <- [#] -> -> _ _ [] -> /=.
progress; exists 2.
by rewrite (IdealTermRel2 2 _ pt10{2} pt20{2} qL).
auto; progress; right; trivial.
auto; progress; right; trivial.
case
  (exists pt1 pt2 q,
   ideal_term_rel2 met
   {|ideal_term_rel_st_is = KEIdeal.st{1}|}
   pt1 pt2 q).
elim* => pt1' pt2' q'.
sp 3 3.
if => //.
inline KEIdeal.parties.
rcondf{1} 3; first auto; smt(). rcondf{2} 3; first auto; smt().
rcondf{1} 3; first auto; smt(is_ke_ideal_state_wait_sim1).
rcondf{2} 3; first auto; smt(is_ke_ideal_state_wait_sim1).
rcondt{1} 3; first auto; smt(is_ke_ideal_state_wait_req2).
rcondt{2} 3; first auto; smt(is_ke_ideal_state_wait_req2).
sp 3 3.
if => //.
sp 1 1.
if.
move => &1 &2 [#] dec_req2_2 dec_req2_1 ->> _ dec_wait_req2_2
        ->> _ dec_wait_req2_1 _ _ _ _ _ _ ->> ->> _ _ _ _ _ _
        [] _ /= _ _ _.
rewrite -dec_req2_2 in dec_req2_1.
elim dec_req2_1 => _ ->.
rewrite -dec_wait_req2_2 in dec_wait_req2_1.
elim dec_wait_req2_1 => _ -> _ //.
auto => |> &1 &2 <- [#] _ -> <- [#] -> -> -> _ _ _ [] ->.
progress; exists 1.
by rewrite (IdealTermRel3 1 _ pt10{2} pt20{2} q{2}).
auto; progress; right; trivial.
auto; progress; right; trivial.
auto; progress; right; trivial.
case
  (exists pt1 pt2 q,
   ideal_term_rel3 met
   {|ideal_term_rel_st_is = KEIdeal.st{1}|}
   pt1 pt2 q).
elim* => pt1' pt2' q'.
sp 3 3.
if => //.
inline KEIdeal.parties.
rcondf{1} 3; first auto; smt(). rcondf{2} 3; first auto; smt().
rcondf{1} 3; first auto; smt(is_ke_ideal_state_wait_sim1).
rcondf{2} 3; first auto; smt(is_ke_ideal_state_wait_sim1).
rcondf{1} 3; first auto; smt(is_ke_ideal_state_wait_req2).
rcondf{2} 3; first auto; smt(is_ke_ideal_state_wait_req2).
rcondt{1} 3; first auto; smt(is_ke_ideal_state_wait_sim2).
rcondt{2} 3; first auto; smt(is_ke_ideal_state_wait_sim2).
sp 3 3.
if => //.
auto => |> &1 &2 <- [#] -> -> -> _ _ _ _ [] ->.
progress; exists 0.
by rewrite (IdealTermRel4 0 _ pt10{2} pt20{2} q{2}).
auto; progress; right; trivial.
auto; progress; right; trivial.
case
  (exists pt1 pt2 q,
   ideal_term_rel4 met
   {|ideal_term_rel_st_is = KEIdeal.st{1}|}
   pt1 pt2 q).
elim* => pt1' pt2' q'.
sp 3 3.
if => //.
inline KEIdeal.parties.
rcondf{1} 3; first auto; smt(). rcondf{2} 3; first auto; smt().
rcondf{1} 3; first auto; smt(is_ke_ideal_state_wait_sim1).
rcondf{2} 3; first auto; smt(is_ke_ideal_state_wait_sim1).
rcondf{1} 3; first auto; smt(is_ke_ideal_state_wait_req2).
rcondf{2} 3; first auto; smt(is_ke_ideal_state_wait_req2).
rcondf{1} 3; first auto; smt(is_ke_ideal_state_wait_sim2).
rcondf{2} 3; first auto; smt(is_ke_ideal_state_wait_sim2).
auto; progress; right; trivial.
auto; progress; right; trivial.
exfalso => &1 &2 [#] _ _ _ _ _ []; smt().
qed.
