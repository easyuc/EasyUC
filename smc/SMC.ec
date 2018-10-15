(* SMC.ec *)

(* Secure Message Communication *)

prover quorum=2 ["Alt-Ergo" "Z3"].

require import AllCore List FSet SmtMap Distr ListAux ListPO.
require import UCCoreDiffieHellman.
require Forward KeyExchange RedundantHashing.

(* theory parameters *)

(* port index of adversary that forwarding functionalities communicate
   with *)

op adv_fw_pi : int.

(* port index of adversary for key exchange's simulator *)

op ke_sim_adv_pi : int.

(* port index of adversary for SMC's simulator *)

op smc_sim_adv_pi : int.

axiom smc_pi_uniq : uniq [smc_sim_adv_pi; ke_sim_adv_pi; adv_fw_pi; 0].

(* end theory parameters *)

(* request sent to port index 1 of SMC functionality: pt1 wants to
   send t to pt2 *)

op smc_req (func : addr, pt1 pt2 : port, t : text) : msg =
     (Dir, (func, 1), pt1,
      UnivPair (UnivPort pt2, UnivBase (BaseText t))).

op dec_smc_req (m : msg) : (addr * port * port * text) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Adv \/ pt1.`2 <> 1 \/ ! is_univ_pair v) ?
        None :
        let (v1, v2) = oget (dec_univ_pair v)
        in (! is_univ_port v1 \/ ! is_univ_base v2) ?
           None :
           let bse = oget (dec_univ_base v2)
           in (! is_base_text bse) ?
              None :
              Some (pt1.`1, pt2, oget (dec_univ_port v1),
                    oget (dec_base_text bse)).

lemma enc_dec_smc_req (func : addr, pt1 pt2 : port, t : text) :
  dec_smc_req (smc_req func pt1 pt2 t) = Some (func, pt1, pt2, t).
proof.
by rewrite /smc_req /dec_smc_req /=
           (is_univ_pair (UnivPort pt2, UnivBase (BaseText t))) /=
           oget_some /= (is_univ_port pt2) /= oget_some.
qed.

op is_smc_req (m : msg) : bool =
     dec_smc_req m <> None.

lemma is_smc_req (func : addr, pt1 pt2 : port, t : text) :
  is_smc_req (smc_req func pt1 pt2 t).
proof.
by rewrite /is_smc_req enc_dec_smc_req.
qed.

(* response sent from port index 2 of SMC functionality to pt2,
   completing the sending of t from pt1 *)

op smc_rsp (func : addr, pt1 pt2 : port, t : text) : msg =
     (Dir, pt2, (func, 2), UnivPair (UnivPort pt1, UnivBase (BaseText t))).

op dec_smc_rsp (m : msg) : (addr * port * port * text) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Adv \/ pt2.`2 <> 2 \/ ! is_univ_pair v) ?
        None :
        let (v1, v2) = oget (dec_univ_pair v)
        in (! is_univ_port v1 \/ ! is_univ_base v2) ?
           None :
           let b = oget (dec_univ_base v2)
           in (! is_base_text b) ?
              None :
              Some (pt2.`1, oget (dec_univ_port v1), pt1, oget (dec_base_text b)).

lemma enc_dec_smc_rsp (func : addr, pt1 pt2 : port, t : text) :
  dec_smc_rsp (smc_rsp func pt1 pt2 t) = Some (func, pt1, pt2, t).
proof.
by rewrite /smc_rsp /dec_smc_rsp /=
           (is_univ_pair (UnivPort pt1, UnivBase (BaseText t))) /=
           oget_some /= (is_univ_port pt1) /= oget_some.
qed.

op is_smc_rsp (m : msg) : bool =
     dec_smc_rsp m <> None.

lemma is_smc_rsp (func : addr, pt1 pt2 : port, t : text) :
  is_smc_rsp (smc_rsp func pt1 pt2 t).
proof.
by rewrite /is_smc_rsp enc_dec_smc_rsp.
qed.

(* Real Functionality *)

clone Forward as Fwd
  with op adv_pi <- adv_fw_pi
proof *.
realize fwd_pi_uniq. by have := smc_pi_uniq. qed.

clone KeyExchange as KeyEx with
  op adv_fw_pi <- adv_fw_pi,
  op ke_sim_adv_pi <- ke_sim_adv_pi
proof *.
realize ke_pi_uniq. by have := smc_pi_uniq. qed.

(* state for Party 1 *)

type smc_real_p1_state = [
    SMCRealP1StateWaitReq
  | SMCRealP1StateWaitKE2 of (port * port * text)
  | SMCRealP1StateFinal   of (port * port * text)
].

op dec_smc_real_p1_state_wait_ke2 (st : smc_real_p1_state) :
     (port * port * text) option =
     with st = SMCRealP1StateWaitReq   => None
     with st = SMCRealP1StateWaitKE2 x => Some x
     with st = SMCRealP1StateFinal _   => None.

lemma enc_dec_smc_real_p1_state_wait_ke2 (x : port * port * text) :
  dec_smc_real_p1_state_wait_ke2 (SMCRealP1StateWaitKE2 x) = Some x.
proof. done. qed.

op is_smc_real_p1_state_wait_ke2 (st : smc_real_p1_state) : bool =
  dec_smc_real_p1_state_wait_ke2 st <> None.

lemma is_smc_real_p1_state_wait_ke2 (x : port * port * text) :
  is_smc_real_p1_state_wait_ke2 (SMCRealP1StateWaitKE2 x).
proof. done. qed.

op dec_smc_real_p1_state_final (st : smc_real_p1_state) :
     (port * port * text) option =
     with st = SMCRealP1StateWaitReq   => None
     with st = SMCRealP1StateWaitKE2 _ => None
     with st = SMCRealP1StateFinal x   => Some x.

lemma enc_dec_smc_real_p1_state_final (x : port * port * text) :
  dec_smc_real_p1_state_final (SMCRealP1StateFinal x) = Some x.
proof. done. qed.

op is_smc_real_p1_state_final (st : smc_real_p1_state) : bool =
  dec_smc_real_p1_state_final st <> None.

lemma is_smc_real_p1_state_final (x : port * port * text) :
  is_smc_real_p1_state_final (SMCRealP1StateFinal x).
proof. done. qed.

(* state for Party 2 *)

type smc_real_p2_state = [
    SMCRealP2StateWaitKE1
  | SMCRealP2StateWaitFwd of key
  | SMCRealP2StateFinal   of key
].

op dec_smc_real_p2_state_wait_fwd (st : smc_real_p2_state) :
     key option =
     with st = SMCRealP2StateWaitKE1   => None
     with st = SMCRealP2StateWaitFwd x => Some x
     with st = SMCRealP2StateFinal _   => None.

lemma enc_dec_smc_real_p2_state_wait_fwd (x : key) :
  dec_smc_real_p2_state_wait_fwd (SMCRealP2StateWaitFwd x) = Some x.
proof. done. qed.

op is_smc_real_p2_state_wait_fwd (st : smc_real_p2_state) : bool =
  dec_smc_real_p2_state_wait_fwd st <> None.

lemma is_smc_real_p2_state_wait_fwd (x : key) :
  is_smc_real_p2_state_wait_fwd (SMCRealP2StateWaitFwd x).
proof. done. qed.

op dec_smc_real_p2_state_final (st : smc_real_p2_state) :
     key option =
     with st = SMCRealP2StateWaitKE1   => None
     with st = SMCRealP2StateWaitFwd _ => None
     with st = SMCRealP2StateFinal x    => Some x.

lemma enc_dec_smc_real_p2_state_final (x : key) :
  dec_smc_real_p2_state_final (SMCRealP2StateFinal x) = Some x.
proof. done. qed.

op is_smc_real_p2_state_final (st : smc_real_p2_state) : bool =
  dec_smc_real_p2_state_final st <> None.

lemma is_smc_real_p2_state_final (x : key) :
  is_smc_real_p2_state_final (SMCRealP2StateFinal x).
proof. done. qed.

module SMCReal (KE : FUNC) = {
  var self, adv : addr
  var st1 : smc_real_p1_state
  var st2 : smc_real_p2_state

  (* Party 1 (P1) manages ports (self, 1) and (self, 3)
     Party 2 (P2) manages ports (self, 2) and (self, 4)
     Forwarder (Fwd) is at address self ++ [1]
     Key Exchanger (KE) is at address self ++ [2] *)

  proc init(self_ adv_ : addr) : unit = {
    self <- self_; adv <- adv_;
    Fwd.Forw.init(self ++ [1], adv); KE.init(self ++ [2], adv);
    st1 <- SMCRealP1StateWaitReq; st2 <- SMCRealP2StateWaitKE1;
  }

  proc party1(m : msg) : msg option = {
    var pt1, pt2, pt1', pt2' : port; var addr : addr;
    var t : text; var k : key;
    var r : msg option <- None;
    if (st1 = SMCRealP1StateWaitReq) {
      if (is_smc_req m) {
        (* destination of m is (self, 1) *)
        (addr, pt1, pt2, t) <- oget (dec_smc_req m);
        if (! self <= pt1.`1 /\ ! self <= pt2.`1 /\
            ! adv <= pt1.`1 /\ ! adv <= pt2.`1) {
          r <-
            Some (KeyEx.ke_req1 (self ++ [2]) (self, 3) (self, 4));
          st1 <- SMCRealP1StateWaitKE2 (pt1, pt2, t);
        }
      }
    }
    elif (is_smc_real_p1_state_wait_ke2 st1) {
      (pt1, pt2, t) <- oget (dec_smc_real_p1_state_wait_ke2 st1);
      if (KeyEx.is_ke_rsp2 m) {
        (addr, pt1', k) <- oget (KeyEx.dec_ke_rsp2 m);
        if (pt1' = (self, 3)) {
          (* destination of m is (self, 3) *)
          r <-
            Some
            (Fwd.fw_req (self ++ [1]) (self, 3) (self, 4)
             (univ_triple (UnivPort pt1) (UnivPort pt2)
              (UnivBase (BaseKey (inj t ^^ k)))));
          st1 <- SMCRealP1StateFinal (pt1, pt2, t);
        }
      }
    }
    else {  (* is_smc_real_p1_state_final st1 *)
    }
    return r;
  }

  proc party2(m : msg) : msg option = {
    var pt1, pt2, pt1', pt2' : port; var addr : addr;
    var u, v1, v2, v3 : univ; var x, k : key;
    var r : msg option <- None;
    if (st2 = SMCRealP2StateWaitKE1) {
      if (KeyEx.is_ke_rsp1 m) {
        (addr, pt1', pt2', k) <- oget (KeyEx.dec_ke_rsp1 m);
        if (pt2' = (self, 4)) {
          (* destination of m is (self, 4) *)
          r <- Some (KeyEx.ke_req2 (self ++ [2]) (self, 4));
          st2 <- SMCRealP2StateWaitFwd k;
        }
      }
    }
    elif (is_smc_real_p2_state_wait_fwd st2) {
      k <- oget (dec_smc_real_p2_state_wait_fwd st2);
      if (Fwd.is_fw_rsp m) {
        (addr, pt1', pt2', u) <- oget (Fwd.dec_fw_rsp m);
        if (pt2' = (self, 4)) {
          (* destination of m is (self, 4) *)
          (v1, v2, v3) <- oget (dec_univ_triple u);
          pt1 <- oget (dec_univ_port v1);
          pt2 <- oget (dec_univ_port v2);
          x <- oget (dec_base_key (oget (dec_univ_base v3)));
          r <- Some (smc_rsp self pt1 pt2 (oget (proj (x ^^ kinv k))));
          st2 <- SMCRealP2StateFinal k;
        }
      }
    }
    else {  (* is_smc_real_p2_state_final st2 *)
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
        r <- Fwd.Forw.invoke(m);
      }
      else {  (* self ++ [2] <= m.`2.`1 *)
        r <- KE.invoke(m);
        if (r <> None /\
            let (mod, pt1, pt2, u) = oget r in
            let (addr1, n1) = pt1
            in !(mod = Dir /\ addr1 = self /\ (n1 = 3 \/ n1 = 4)) /\
               !(mod = Adv /\ ! self <= addr1)) {
          r <- None;
        }
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
    if ((mod = Dir /\ addr1 = self /\ n1 = 1) \/
        (mod = Adv /\ (self ++ [1] <= addr1 \/ self ++ [2] <= addr1))) {
      r <- loop(m);
    }
    return r;
  }
}.

(* Ideal Functionality *)

(* request sent from port index 3 of SMC ideal functionality to port
   index smc_sim_adv_pi of SMC simulator *)

op smc_sim_req (ideal adv : addr, pt1 pt2 : port) : msg =
     (Adv, (adv, smc_sim_adv_pi), (ideal, 3),
      UnivPair (UnivPort pt1, UnivPort pt2)).

op dec_smc_sim_req (m : msg) : (addr * addr * port * port) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Dir \/ pt1.`2 <> smc_sim_adv_pi \/ pt2.`2 <> 3 \/
         ! is_univ_pair v) ?
        None :
        let (v1, v2) = oget (dec_univ_pair v)
        in (! is_univ_port v1 \/ ! is_univ_port v2) ?
           None :
           Some (pt2.`1, pt1.`1,
                 oget (dec_univ_port v1), oget (dec_univ_port v2)).

lemma enc_dec_smc_sim_req (ideal adv : addr, pt1 pt2 : port) :
  dec_smc_sim_req (smc_sim_req ideal adv pt1 pt2) =
  Some (ideal, adv, pt1, pt2).
proof. done. qed.

op is_smc_sim_req (m : msg) : bool =
     dec_smc_sim_req m <> None.

lemma is_smc_sim_req (ideal adv : addr, pt1 pt2 : port) :
  is_smc_sim_req (smc_sim_req ideal adv pt1 pt2).
proof. done. qed.

(* response sent from port index smc_sim_adv_pi of SMC simulator to
   port index 3 of SMC ideal functionality *)

op smc_sim_rsp (ideal adv : addr) : msg =
     (Adv, (ideal, 3), (adv, smc_sim_adv_pi), UnivUnit).

op dec_smc_sim_rsp (m : msg) : (addr * addr) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Dir \/ pt1.`2 <> 3 \/ pt2.`2 <> smc_sim_adv_pi \/
         ! v = UnivUnit) ?
        None :
        Some (pt1.`1, pt2.`1).

lemma enc_dec_smc_sim_rsp (ideal adv : addr) :
  dec_smc_sim_rsp (smc_sim_rsp ideal adv) = Some (ideal, adv).
proof. done. qed.

op is_smc_sim_rsp (m : msg) : bool =
     dec_smc_sim_rsp m <> None.

lemma is_smc_sim_rsp (ideal adv : addr) :
  is_smc_sim_rsp (smc_sim_rsp ideal adv).
proof. done. qed.

type smc_ideal_state = [
    SMCIdealStateWaitReq
  | SMCIdealStateWaitSim of (port * port * text)
  | SMCIdealStateFinal   of (port * port * text)
].

op dec_smc_ideal_state_wait_sim (st : smc_ideal_state) :
     (port * port * text) option =
     with st = SMCIdealStateWaitReq   => None
     with st = SMCIdealStateWaitSim x => Some x
     with st = SMCIdealStateFinal _   => None.

lemma enc_dec_smc_ideal_state_wait_sim (x : port * port * text) :
  dec_smc_ideal_state_wait_sim (SMCIdealStateWaitSim x) = Some x.
proof. done. qed.

op is_smc_ideal_state_wait_sim (st : smc_ideal_state) : bool =
  dec_smc_ideal_state_wait_sim st <> None.

lemma is_smc_ideal_state_wait_sim (x : port * port * text) :
  is_smc_ideal_state_wait_sim (SMCIdealStateWaitSim x).
proof. done. qed.

op dec_smc_ideal_state_final (st : smc_ideal_state) :
     (port * port * text) option =
     with st = SMCIdealStateWaitReq   => None
     with st = SMCIdealStateWaitSim _ => None
     with st = SMCIdealStateFinal x   => Some x.

lemma enc_dec_smc_ideal_state_final (x : port * port * text) :
  dec_smc_ideal_state_final (SMCIdealStateFinal x) = Some x.
proof. done. qed.

op is_smc_ideal_state_final (st : smc_ideal_state) : bool =
  dec_smc_ideal_state_final st <> None.

lemma is_smc_ideal_state_final (x : port * port * text) :
  is_smc_ideal_state_final (SMCIdealStateFinal x).
proof. done. qed.

module SMCIdeal : FUNC = {
  var self, adv : addr
  var st : smc_ideal_state

  proc init(self_ adv_ : addr) : unit = {
    self <- self_; adv <- adv_;
    st <- SMCIdealStateWaitReq;
  }

  proc parties(m : msg) : msg option = {
    var pt1, pt2, pt1', pt2' : port; var addr, addr1, addr2 : addr;
    var t : text;
    var r : msg option <- None;
    if (st = SMCIdealStateWaitReq) {
      if (is_smc_req m) {
        (* destination of m is (self, 1) *)
        (addr, pt1, pt2, t) <- oget (dec_smc_req m);
        if (! self <= pt1.`1 /\ ! self <= pt2.`1 /\
            ! adv <= pt1.`1 /\ ! adv <= pt2.`1) {
          r <- Some (smc_sim_req self adv pt1 pt2);
          st <- SMCIdealStateWaitSim (pt1, pt2, t);
        }
      }
    }
    elif (is_smc_ideal_state_wait_sim st) {
      (pt1, pt2, t) <- oget (dec_smc_ideal_state_wait_sim st);
      if (is_smc_sim_rsp m) {
        (* destination of m is (self, 3) *)
        (addr1, addr2) <- oget (dec_smc_sim_rsp m);
        r <- Some (smc_rsp self pt1 pt2 t);
        st <- SMCIdealStateFinal (pt1, pt2, t);
      }
    }
    return r;
  }

  proc invoke(m : msg) : msg option = {
    var mod : mode; var pt1, pt2 : port; var u : univ;
    var addr1 : addr; var n1 : int;
    var r : msg option <- None;
    (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
    if ((mod = Dir /\ addr1 = self /\ n1 = 1) \/
        (mod = Adv /\ addr1 = self /\ n1 = 3)) {
      r <- parties(m);
    }
    return r;
  }
}.

(* Simulator *)

type smc_sim_state = [
    SMCSimStateWaitReq
  | SMCSimStateWaitAdv1 of (port * port * addr * exp)
  | SMCSimStateWaitAdv2 of (port * port * addr * exp)
  | SMCSimStateWaitAdv3 of (port * port * addr * exp)
  | SMCSimStateFinal    of (port * port * addr * exp)
].

op dec_smc_sim_state_wait_adv1 (st : smc_sim_state) :
     (port * port * addr * exp) option =
     with st = SMCSimStateWaitReq    => None
     with st = SMCSimStateWaitAdv1 x => Some x
     with st = SMCSimStateWaitAdv2 _ => None
     with st = SMCSimStateWaitAdv3 _ => None
     with st = SMCSimStateFinal _    => None.

lemma enc_dec_smc_sim_state_wait_adv1 (x : port * port * addr * exp) :
  dec_smc_sim_state_wait_adv1 (SMCSimStateWaitAdv1 x) = Some x.
proof. done. qed.

op is_smc_sim_state_wait_adv1 (st : smc_sim_state) : bool =
  dec_smc_sim_state_wait_adv1 st <> None.

lemma is_smc_sim_state_wait_adv1 (x : port * port * addr * exp) :
  is_smc_sim_state_wait_adv1 (SMCSimStateWaitAdv1 x).
proof. done. qed.

op dec_smc_sim_state_wait_adv2 (st : smc_sim_state) :
     (port * port * addr * exp) option =
     with st = SMCSimStateWaitReq    => None
     with st = SMCSimStateWaitAdv1 _ => None
     with st = SMCSimStateWaitAdv2 x => Some x
     with st = SMCSimStateWaitAdv3 _ => None
     with st = SMCSimStateFinal _    => None.

lemma enc_dec_smc_sim_state_wait_adv2 (x : port * port * addr * exp) :
  dec_smc_sim_state_wait_adv2 (SMCSimStateWaitAdv2 x) = Some x.
proof. done. qed.

op is_smc_sim_state_wait_adv2 (st : smc_sim_state) : bool =
  dec_smc_sim_state_wait_adv2 st <> None.

lemma is_smc_sim_state_wait_adv2 (x : port * port * addr * exp) :
  is_smc_sim_state_wait_adv2 (SMCSimStateWaitAdv2 x).
proof. done. qed.

op dec_smc_sim_state_wait_adv3 (st : smc_sim_state) :
     (port * port * addr * exp) option =
     with st = SMCSimStateWaitReq    => None
     with st = SMCSimStateWaitAdv1 _ => None
     with st = SMCSimStateWaitAdv2 _ => None
     with st = SMCSimStateWaitAdv3 x => Some x
     with st = SMCSimStateFinal _    => None.

lemma enc_dec_smc_sim_state_wait_adv3 (x : port * port * addr * exp) :
  dec_smc_sim_state_wait_adv3 (SMCSimStateWaitAdv3 x) = Some x.
proof. done. qed.

op is_smc_sim_state_wait_adv3 (st : smc_sim_state) : bool =
  dec_smc_sim_state_wait_adv3 st <> None.

lemma is_smc_sim_state_wait_adv3 (x : port * port * addr * exp) :
  is_smc_sim_state_wait_adv3 (SMCSimStateWaitAdv3 x).
proof. done. qed.

op dec_smc_sim_state_final (st : smc_sim_state) :
     (port * port * addr * exp) option =
     with st = SMCSimStateWaitReq    => None
     with st = SMCSimStateWaitAdv1 _ => None
     with st = SMCSimStateWaitAdv2 _ => None
     with st = SMCSimStateWaitAdv3 _ => None
     with st = SMCSimStateFinal x    => Some x.

lemma enc_dec_smc_sim_state_final (x : port * port * addr * exp) :
  dec_smc_sim_state_final (SMCSimStateFinal x) = Some x.
proof. done. qed.

op is_smc_sim_state_final (st : smc_sim_state) : bool =
  dec_smc_sim_state_final st <> None.

lemma is_smc_sim_state_final (x : port * port * addr * exp) :
  is_smc_sim_state_final (SMCSimStateFinal x).
proof. done. qed.

module SMCSim (Adv : FUNC) = {
  var self, adv : addr
  var st : smc_sim_state

  proc init(self_ adv_ : addr) : unit = {
    self <- self_; adv <- adv_;
    Adv.init(self, adv);
    st <- SMCSimStateWaitReq;
  }

  proc loop(m : msg) : msg option = {
    var mod : mode; var pt1, pt2 : port; var u : univ;
    var addr, addr1, addr2 : addr; var q : exp;
    var r : msg option <- None;
    var not_done : bool <- true;
    while (not_done) {
      (* mod = Adv /\ pt1.`1 = self *)
      (mod, pt1, pt2, u) <- m;
      if (pt1.`2 = smc_sim_adv_pi) {  (* simulator *)
        r <- None;
        if (st = SMCSimStateWaitReq) {
          if (is_smc_sim_req m) {
            (addr1, addr2, pt1, pt2) <- oget (dec_smc_sim_req m);
            q <$ dexp;
            r <-
              Some
              (KeyEx.ke_sim_req1 (addr1 ++ [2]) self
               (addr1, 3) (addr1, 4));
            st <- SMCSimStateWaitAdv1 (pt1, pt2, addr1, q);
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
        if (r = None) {
          not_done <- false;
        }
        else {
          m <- oget r; (mod, pt1, pt2, u) <- m;
          if (is_smc_sim_state_wait_adv1 st) {
            (pt1, pt2, addr, q) <- oget (dec_smc_sim_state_wait_adv1 st);
            r <- None; not_done <- false;
            if (KeyEx.is_ke_sim_rsp m) {
              (addr1, addr2) <- oget (KeyEx.dec_ke_sim_rsp m);
              if (addr1 = addr ++ [2]) {
                r <- Some (KeyEx.ke_sim_req2 (addr ++ [2]) self);
                not_done <- true;
                st <- SMCSimStateWaitAdv2 (pt1, pt2, addr, q);
              }
            }
          }
          elif (is_smc_sim_state_wait_adv2 st) {
            (pt1, pt2, addr, q) <- oget (dec_smc_sim_state_wait_adv2 st);
            r <- None; not_done <- false;
            if (KeyEx.is_ke_sim_rsp m) {
              (addr1, addr2) <- oget (KeyEx.dec_ke_sim_rsp m);
              if (addr1 = addr ++ [2]) {
                r <-
                  Some
                  (Fwd.fw_obs (addr ++ [1]) self (addr, 3) (addr, 4)
                   (univ_triple (UnivPort pt1) (UnivPort pt2)
                    (UnivBase (BaseKey (g ^ q)))));
                not_done <- true;
                st <- SMCSimStateWaitAdv3 (pt1, pt2, addr, q);
              }
            }
          }
          elif (is_smc_sim_state_wait_adv3 st) {
            (pt1, pt2, addr, q) <- oget (dec_smc_sim_state_wait_adv3 st);
            r <- None; not_done <- false;
            if (Fwd.is_fw_ok m) {
              (addr1, addr2) <- oget (Fwd.dec_fw_ok m);
              if (addr1 = addr ++ [1]) {
                r <- Some (smc_sim_rsp addr self);
                not_done <- true;
                st <- SMCSimStateFinal (pt1, pt2, addr, q);
              }
            }
          }
          else {  (* not waiting on adversary *)
            not_done <- false;
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

(* simplified version of SMCReal(KeyEx.KEIdeal) *)

abstract theory SMCRealKEIdealSimp.

type smc_real_ke_ideal_simp_state = [
    SMCRealKEIdealSimpStateWaitReq
  | SMCRealKEIdealSimpStateWaitAdv1 of (port * port * text)
  | SMCRealKEIdealSimpStateWaitAdv2 of (port * port * text * key)
  | SMCRealKEIdealSimpStateWaitAdv3 of (port * port * text * key)
  | SMCRealKEIdealSimpStateFinal    of (port * port * text * key)
].

op dec_smc_real_ke_ideal_simp_state_wait_adv1
   (st : smc_real_ke_ideal_simp_state) :
     (port * port * text) option =
     with st = SMCRealKEIdealSimpStateWaitReq    => None
     with st = SMCRealKEIdealSimpStateWaitAdv1 x => Some x
     with st = SMCRealKEIdealSimpStateWaitAdv2 _ => None
     with st = SMCRealKEIdealSimpStateWaitAdv3 _ => None
     with st = SMCRealKEIdealSimpStateFinal    _ => None.

lemma enc_dec_smc_real_ke_ideal_simp_state_wait_adv1 (x : port * port * text) :
  dec_smc_real_ke_ideal_simp_state_wait_adv1
  (SMCRealKEIdealSimpStateWaitAdv1 x) = Some x.
proof. done. qed.

op is_smc_real_ke_ideal_simp_state_wait_adv1
   (st : smc_real_ke_ideal_simp_state) : bool =
  dec_smc_real_ke_ideal_simp_state_wait_adv1 st <> None.

lemma is_smc_real_ke_ideal_simp_state_wait_adv1 (x : port * port * text) :
  is_smc_real_ke_ideal_simp_state_wait_adv1
  (SMCRealKEIdealSimpStateWaitAdv1 x).
proof. done. qed.

op dec_smc_real_ke_ideal_simp_state_wait_adv2
   (st : smc_real_ke_ideal_simp_state) :
     (port * port * text * key) option =
     with st = SMCRealKEIdealSimpStateWaitReq    => None
     with st = SMCRealKEIdealSimpStateWaitAdv1 _ => None
     with st = SMCRealKEIdealSimpStateWaitAdv2 x => Some x
     with st = SMCRealKEIdealSimpStateWaitAdv3 _ => None
     with st = SMCRealKEIdealSimpStateFinal    _ => None.

lemma enc_dec_smc_real_ke_ideal_simp_state_wait_adv2
      (x : port * port * text * key) :
  dec_smc_real_ke_ideal_simp_state_wait_adv2
  (SMCRealKEIdealSimpStateWaitAdv2 x) = Some x.
proof. done. qed.

op is_smc_real_ke_ideal_simp_state_wait_adv2
   (st : smc_real_ke_ideal_simp_state) : bool =
  dec_smc_real_ke_ideal_simp_state_wait_adv2 st <> None.

lemma is_smc_real_ke_ideal_simp_state_wait_adv2
      (x : port * port * text * key) :
  is_smc_real_ke_ideal_simp_state_wait_adv2
  (SMCRealKEIdealSimpStateWaitAdv2 x).
proof. done. qed.

op dec_smc_real_ke_ideal_simp_state_wait_adv3
   (st : smc_real_ke_ideal_simp_state) :
     (port * port * text * key) option =
     with st = SMCRealKEIdealSimpStateWaitReq    => None
     with st = SMCRealKEIdealSimpStateWaitAdv1 _ => None
     with st = SMCRealKEIdealSimpStateWaitAdv2 _ => None
     with st = SMCRealKEIdealSimpStateWaitAdv3 x => Some x
     with st = SMCRealKEIdealSimpStateFinal    _ => None.

lemma enc_dec_smc_real_ke_ideal_simp_state_wait_adv3
      (x : port * port * text * key) :
  dec_smc_real_ke_ideal_simp_state_wait_adv3
  (SMCRealKEIdealSimpStateWaitAdv3 x) = Some x.
proof. done. qed.

op is_smc_real_ke_ideal_simp_state_wait_adv3
   (st : smc_real_ke_ideal_simp_state) : bool =
  dec_smc_real_ke_ideal_simp_state_wait_adv3 st <> None.

lemma is_smc_real_ke_ideal_simp_state_wait_adv3
      (x : port * port * text * key) :
  is_smc_real_ke_ideal_simp_state_wait_adv3
  (SMCRealKEIdealSimpStateWaitAdv3 x).
proof. done. qed.

op dec_smc_real_ke_ideal_simp_state_final
   (st : smc_real_ke_ideal_simp_state) :
     (port * port * text * key) option =
     with st = SMCRealKEIdealSimpStateWaitReq    => None
     with st = SMCRealKEIdealSimpStateWaitAdv1 _ => None
     with st = SMCRealKEIdealSimpStateWaitAdv2 _ => None
     with st = SMCRealKEIdealSimpStateWaitAdv3 _ => None
     with st = SMCRealKEIdealSimpStateFinal    x => Some x.

lemma enc_dec_smc_real_ke_ideal_simp_state_final
      (x : port * port * text * key) :
  dec_smc_real_ke_ideal_simp_state_final
  (SMCRealKEIdealSimpStateFinal x) = Some x.
proof. done. qed.

op is_smc_real_ke_ideal_simp_state_final
   (st : smc_real_ke_ideal_simp_state) : bool =
  dec_smc_real_ke_ideal_simp_state_final st <> None.

lemma is_smc_real_ke_ideal_simp_state_final
      (x : port * port * text * key) :
  is_smc_real_ke_ideal_simp_state_final
  (SMCRealKEIdealSimpStateFinal x).
proof. done. qed.

module SMCRealKEIdealSimp : FUNC = {
  var self, adv : addr
  var st : smc_real_ke_ideal_simp_state

  proc init(self_ adv_ : addr) : unit = {
    self <- self_; adv <- adv_;
    st <- SMCRealKEIdealSimpStateWaitReq;
  }

  proc parties(m : msg) : msg option = {
    var pt1, pt2, pt1', pt2' : port; var addr, addr1, addr2 : addr;
    var t : text; var k : key; var q : exp;
    var r : msg option <- None;
    if (st = SMCRealKEIdealSimpStateWaitReq) {
      if (is_smc_req m) {
        (* destination of m is (self, 1) *)
        (addr, pt1, pt2, t) <- oget (dec_smc_req m);
        if (! self <= pt1.`1 /\ ! self <= pt2.`1 /\
            ! adv <= pt1.`1 /\ ! adv <= pt2.`1) {
          r <- Some (KeyEx.ke_sim_req1 (self ++ [2]) adv (self, 3) (self, 4));
          st <- SMCRealKEIdealSimpStateWaitAdv1 (pt1, pt2, t);
        }
      }
    }
    elif (is_smc_real_ke_ideal_simp_state_wait_adv1 st) {
      (pt1, pt2, t) <- oget (dec_smc_real_ke_ideal_simp_state_wait_adv1 st);
      if (KeyEx.is_ke_sim_rsp m) {
        (addr1, addr2) <- oget (KeyEx.dec_ke_sim_rsp m);
        if (addr1 = self ++ [2]) {
          (* destination of m is (self ++ [2], 3), mode of m is Adv *)
          q <$ dexp;
          r <- Some (KeyEx.ke_sim_req2 (self ++ [2]) adv);
          st <- SMCRealKEIdealSimpStateWaitAdv2 (pt1, pt2, t, g ^ q);
        }
      }
    }
    elif (is_smc_real_ke_ideal_simp_state_wait_adv2 st) {
      (pt1, pt2, t, k) <- oget (dec_smc_real_ke_ideal_simp_state_wait_adv2 st);
      if (KeyEx.is_ke_sim_rsp m) {
        (addr1, addr2) <- oget (KeyEx.dec_ke_sim_rsp m);
        if (addr1 = self ++ [2]) {
          (* destination of m is (self ++ [2], 3), mode of m is Adv *)
          r <- Some
               (Fwd.fw_obs
                (self ++ [1]) adv (self, 3) (self, 4)
                (univ_triple (UnivPort pt1) (UnivPort pt2)
                 (UnivBase (BaseKey (inj t ^^ k)))));
          st <- SMCRealKEIdealSimpStateWaitAdv3 (pt1, pt2, t, k);
        }
      }
    }
    elif (is_smc_real_ke_ideal_simp_state_wait_adv3 st) {
      (pt1, pt2, t, k) <- oget (dec_smc_real_ke_ideal_simp_state_wait_adv3 st);
      if (Fwd.is_fw_ok m) {
        (addr1, addr2) <- oget (Fwd.dec_fw_ok m);
        if (addr1 = self ++ [1]) {
          (* destination of m is (self ++ [1], 1), mode of m is Adv *)
          r <- Some (smc_rsp self pt1 pt2 t);
          st <- SMCRealKEIdealSimpStateFinal (pt1, pt2, t, k);
        }
      }
    }
    return r;
  }

  proc invoke(m : msg) : msg option = {
    var mod : mode; var pt1, pt2 : port; var u : univ;
    var addr1 : addr; var n1 : int;
    var r : msg option <- None;
    (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
    if ((mod = Dir /\ addr1 = self /\ n1 = 1) \/
        (mod = Adv /\ (self ++ [1] <= addr1 \/ self ++ [2] <= addr1))) {
      r <- parties(m);
    }
    return r;
  }
}.

(* relational invariant for connecting SMCReal(KeyEx.KEIdeal) and
   SMCRealKEIdealSimp *)

type smc_real_ke_ideal_simp_rel_st = {
  smc_real_ke_ideal_simp_rel_st_func : addr;
  smc_real_ke_ideal_simp_rel_st_r1s  : smc_real_p1_state;
  smc_real_ke_ideal_simp_rel_st_r2s  : smc_real_p2_state;
  smc_real_ke_ideal_simp_rel_st_fws  : Fwd.fw_state;
  smc_real_ke_ideal_simp_rel_st_keis : KeyEx.ke_ideal_state;
  smc_real_ke_ideal_simp_rel_st_riss : smc_real_ke_ideal_simp_state;
}.

pred smc_real_ke_ideal_simp_rel0 (st : smc_real_ke_ideal_simp_rel_st) =
  (st.`smc_real_ke_ideal_simp_rel_st_r1s  = SMCRealP1StateWaitReq) /\
  (st.`smc_real_ke_ideal_simp_rel_st_r2s  = SMCRealP2StateWaitKE1) /\
  (st.`smc_real_ke_ideal_simp_rel_st_fws  = Fwd.FwStateInit) /\
  (st.`smc_real_ke_ideal_simp_rel_st_keis = KeyEx.KEIdealStateWaitReq1) /\
  (st.`smc_real_ke_ideal_simp_rel_st_riss = SMCRealKEIdealSimpStateWaitReq).

pred smc_real_ke_ideal_simp_rel1
     (st : smc_real_ke_ideal_simp_rel_st, pt1 pt2 : port, t : text) =
  ! (st.`smc_real_ke_ideal_simp_rel_st_func <= pt1.`1) /\
  ! (st.`smc_real_ke_ideal_simp_rel_st_func <= pt2.`1) /\
  (st.`smc_real_ke_ideal_simp_rel_st_r1s  =
   SMCRealP1StateWaitKE2 (pt1, pt2, t)) /\
  (st.`smc_real_ke_ideal_simp_rel_st_r2s  = SMCRealP2StateWaitKE1) /\
  (st.`smc_real_ke_ideal_simp_rel_st_fws  = Fwd.FwStateInit) /\
  (st.`smc_real_ke_ideal_simp_rel_st_keis =
   KeyEx.KEIdealStateWaitSim1
   ((st.`smc_real_ke_ideal_simp_rel_st_func, 3),
    (st.`smc_real_ke_ideal_simp_rel_st_func, 4))) /\
  (st.`smc_real_ke_ideal_simp_rel_st_riss =
   SMCRealKEIdealSimpStateWaitAdv1 (pt1, pt2, t)).

pred smc_real_ke_ideal_simp_rel2
     (st : smc_real_ke_ideal_simp_rel_st, pt1 pt2 : port,
      t : text, q : exp) =
  ! (st.`smc_real_ke_ideal_simp_rel_st_func <= pt1.`1) /\
  ! (st.`smc_real_ke_ideal_simp_rel_st_func <= pt2.`1) /\
  (st.`smc_real_ke_ideal_simp_rel_st_r1s  =
   SMCRealP1StateWaitKE2 (pt1, pt2, t)) /\
  (st.`smc_real_ke_ideal_simp_rel_st_r2s  =
   SMCRealP2StateWaitFwd (g ^ q)) /\
  (st.`smc_real_ke_ideal_simp_rel_st_fws  = Fwd.FwStateInit) /\
  (st.`smc_real_ke_ideal_simp_rel_st_keis =
   KeyEx.KEIdealStateWaitSim2
   ((st.`smc_real_ke_ideal_simp_rel_st_func, 3),
    (st.`smc_real_ke_ideal_simp_rel_st_func, 4),
    q)) /\
  (st.`smc_real_ke_ideal_simp_rel_st_riss =
   SMCRealKEIdealSimpStateWaitAdv2 (pt1, pt2, t, g ^ q)).

pred smc_real_ke_ideal_simp_rel3
     (st : smc_real_ke_ideal_simp_rel_st, pt1 pt2 : port,
      t : text, q : exp) =
  ! (st.`smc_real_ke_ideal_simp_rel_st_func <= pt1.`1) /\
  ! (st.`smc_real_ke_ideal_simp_rel_st_func <= pt2.`1) /\
  (st.`smc_real_ke_ideal_simp_rel_st_r1s  =
   SMCRealP1StateFinal (pt1, pt2, t)) /\
  (st.`smc_real_ke_ideal_simp_rel_st_r2s  =
   SMCRealP2StateWaitFwd (g ^ q)) /\
  (st.`smc_real_ke_ideal_simp_rel_st_fws  =
   Fwd.FwStateWait
   ((st.`smc_real_ke_ideal_simp_rel_st_func, 3),
    (st.`smc_real_ke_ideal_simp_rel_st_func, 4),
    univ_triple (UnivPort pt1) (UnivPort pt2)
                (UnivBase (BaseKey (inj t ^^ (g ^ q)))))) /\
  (st.`smc_real_ke_ideal_simp_rel_st_keis =
   KeyEx.KEIdealStateFinal
   ((st.`smc_real_ke_ideal_simp_rel_st_func, 3),
    (st.`smc_real_ke_ideal_simp_rel_st_func, 4),
    q)) /\
  (st.`smc_real_ke_ideal_simp_rel_st_riss =
   SMCRealKEIdealSimpStateWaitAdv3 (pt1, pt2, t, g ^ q)).

pred smc_real_ke_ideal_simp_rel4
     (st : smc_real_ke_ideal_simp_rel_st, pt1 pt2 : port,
      t : text, q : exp) =
  ! (st.`smc_real_ke_ideal_simp_rel_st_func <= pt1.`1) /\
  ! (st.`smc_real_ke_ideal_simp_rel_st_func <= pt2.`1) /\
  (st.`smc_real_ke_ideal_simp_rel_st_r1s  =
   SMCRealP1StateFinal (pt1, pt2, t)) /\
  (st.`smc_real_ke_ideal_simp_rel_st_r2s  =
   SMCRealP2StateFinal (g ^ q)) /\
  (st.`smc_real_ke_ideal_simp_rel_st_fws  =
   Fwd.FwStateFinal
   ((st.`smc_real_ke_ideal_simp_rel_st_func, 3),
    (st.`smc_real_ke_ideal_simp_rel_st_func, 4),
    univ_triple (UnivPort pt1) (UnivPort pt2)
                (UnivBase (BaseKey (inj t ^^ (g ^ q)))))) /\
  (st.`smc_real_ke_ideal_simp_rel_st_keis =
   KeyEx.KEIdealStateFinal
   ((st.`smc_real_ke_ideal_simp_rel_st_func, 3),
    (st.`smc_real_ke_ideal_simp_rel_st_func, 4),
    q)) /\
  (st.`smc_real_ke_ideal_simp_rel_st_riss =
   SMCRealKEIdealSimpStateFinal (pt1, pt2, t, g ^ q)).

inductive smc_real_ke_ideal_simp_rel
          (st : smc_real_ke_ideal_simp_rel_st) =
    SMCRealKEIdealSimpRel0 of (smc_real_ke_ideal_simp_rel0 st)
  | SMCRealKEIdealSimpRel1 (pt1 pt2 : port, t : text) of
      (smc_real_ke_ideal_simp_rel1 st pt1 pt2 t)
  | SMCRealKEIdealSimpRel2 (pt1 pt2 : port, t : text, q : exp) of
      (smc_real_ke_ideal_simp_rel2 st pt1 pt2 t q)
  | SMCRealKEIdealSimpRel3 (pt1 pt2 : port, t : text, q : exp) of
      (smc_real_ke_ideal_simp_rel3 st pt1 pt2 t q)
  | SMCRealKEIdealSimpRel4 (pt1 pt2 : port, t : text, q : exp) of
      (smc_real_ke_ideal_simp_rel4 st pt1 pt2 t q).

lemma SMCReal_KEIdeal_SMCRealKEIdealSimp_invoke (func adv : addr) :
  equiv
  [SMCReal(KeyEx.KEIdeal).invoke ~ SMCRealKEIdealSimp.invoke :
   inc func adv /\ ={m} /\
   SMCReal.self{1} = func /\ SMCReal.adv{1} = adv /\
   Fwd.Forw.self{1} = func ++ [1] /\ Fwd.Forw.adv{1} = adv /\
   KeyEx.KEIdeal.self{1} = func ++ [2] /\ KeyEx.KEIdeal.adv{1} = adv /\
   SMCRealKEIdealSimp.self{2} = func /\ SMCRealKEIdealSimp.adv{2} = adv /\
   smc_real_ke_ideal_simp_rel
   {|smc_real_ke_ideal_simp_rel_st_func = func;
     smc_real_ke_ideal_simp_rel_st_r1s  = SMCReal.st1{1};
     smc_real_ke_ideal_simp_rel_st_r2s  = SMCReal.st2{1};
     smc_real_ke_ideal_simp_rel_st_fws  = Fwd.Forw.st{1};
     smc_real_ke_ideal_simp_rel_st_keis = KeyEx.KEIdeal.st{1};
     smc_real_ke_ideal_simp_rel_st_riss = SMCRealKEIdealSimp.st{2}|} ==>
   ={res} /\
   smc_real_ke_ideal_simp_rel
   {|smc_real_ke_ideal_simp_rel_st_func = func;
     smc_real_ke_ideal_simp_rel_st_r1s  = SMCReal.st1{1};
     smc_real_ke_ideal_simp_rel_st_r2s  = SMCReal.st2{1};
     smc_real_ke_ideal_simp_rel_st_fws  = Fwd.Forw.st{1};
     smc_real_ke_ideal_simp_rel_st_keis = KeyEx.KEIdeal.st{1};
     smc_real_ke_ideal_simp_rel_st_riss = SMCRealKEIdealSimp.st{2}|}].
proof.
proc.
case
  (smc_real_ke_ideal_simp_rel0
   {|smc_real_ke_ideal_simp_rel_st_func = func;
     smc_real_ke_ideal_simp_rel_st_r1s  = SMCReal.st1{1};
     smc_real_ke_ideal_simp_rel_st_r2s  = SMCReal.st2{1};
     smc_real_ke_ideal_simp_rel_st_fws  = Fwd.Forw.st{1};
     smc_real_ke_ideal_simp_rel_st_keis = KeyEx.KEIdeal.st{1};
     smc_real_ke_ideal_simp_rel_st_riss = SMCRealKEIdealSimp.st{2}|}).
sp 3 3.
if => //.
inline SMCReal(KeyEx.KEIdeal).loop SMCRealKEIdealSimp.parties.
sp 3 2.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto; smt().
case (mod{1} = Dir /\ addr1{1} = SMCReal.self{1} /\ n1{1} = 1).
rcondt{1} 1; first auto.
inline{1} (1) SMCReal(KeyEx.KEIdeal).party1.
rcondt{1} 3; first auto; smt().
sp 2 0.
if => //.
sp 1 1.
if; first move => /> &1 &2 <- //.
rcondf{1} 4; first auto.
move => /> &1 &2.
rewrite oget_some /ke_req1 /=.
smt(le_ext_r).
rcondt{1} 5; first auto.
rcondf{1} 5; first auto.
move => /> &hr <-.
rewrite oget_some /ke_req1 /=.
smt(ne_cat_nonnil_r).
rcondf{1} 5; first auto.
rcondf{1} 5; first auto.
move => /> &hr.
by rewrite oget_some /ke_req1 /= le_ext_comm.
inline{1} (1) KeyEx.KEIdeal.invoke.
rcondt{1} 9; first auto.
inline{1} (1) KeyEx.KEIdeal.parties.
rcondt{1} 11; first auto; smt().
rcondt{1} 11; first auto.
rcondt{1} 12; first auto.
move => /> &hr <-.
rewrite oget_some KeyEx.enc_dec_ke_req1 oget_some /=.
progress.
by rewrite not_le_ext_nonnil_l.
by rewrite not_le_ext_nonnil_l.
by rewrite inc_nle_r.
by rewrite inc_nle_r.
rcondf{1} 16; first auto; progress.
by rewrite inc_nle_l.
rcondt{1} 16; first auto.
move => /> &hr.
rewrite !oget_some KeyEx.enc_dec_ke_req1 oget_some /=
        /ke_sim_req1 /=.
progress; by rewrite inc_nle_l.
rcondf{1} 17; first auto.
auto => |> &1 &2.
rewrite !oget_some KeyEx.enc_dec_ke_req1 !oget_some /ke_simp_req1 /=.
move => <- [#] _ -> -> ->.
progress; rewrite (SMCRealKEIdealSimpRel1 _ pt10{2} pt20{2} t{2}) /#.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto.
rcondf{1} 1; first auto; smt(not_le_ext_nonnil_l).
rcondf{1} 1; first auto; smt(not_le_ext_nonnil_l).
rcondf{2} 1; first auto.
move => |> &hr inc_self_adv _ _.
progress; rewrite /is_smc_req /dec_smc_req; smt(not_dir).
if{1}.
inline{1} (1) Fwd.Forw.invoke.
rcondt{1} 3; first auto; smt().
rcondf{1} 3; first auto.
move => |> &hr.
progress; rewrite /is_fw_req /dec_fw_req; smt(not_dir).
rcondt{1} 4; first auto.
rcondf{1} 5; first auto.
auto.
inline{1} (1) KeyEx.KEIdeal.invoke.
sp 4 0.
if{1}.
inline KeyEx.KEIdeal.parties.
rcondt{1} 3; first auto; smt().
rcondf{1} 3; first auto.
move => |> &hr.
progress; rewrite /is_ke_req1 /dec_ke_req1; smt(not_dir).
rcondf{1} 5; first auto.
rcondt{1} 5; first auto.
rcondf{1} 6; first auto.
auto.
rcondf{1} 2; first auto.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto.
case
  (exists pt1' pt2' t',
   smc_real_ke_ideal_simp_rel1
   {|smc_real_ke_ideal_simp_rel_st_func = func;
     smc_real_ke_ideal_simp_rel_st_r1s  = SMCReal.st1{1};
     smc_real_ke_ideal_simp_rel_st_r2s  = SMCReal.st2{1};
     smc_real_ke_ideal_simp_rel_st_fws  = Fwd.Forw.st{1};
     smc_real_ke_ideal_simp_rel_st_keis = KeyEx.KEIdeal.st{1};
     smc_real_ke_ideal_simp_rel_st_riss = SMCRealKEIdealSimp.st{2}|}
   pt1' pt2' t').
elim* => pt1' pt2' t'.
sp 3 3.
if => //.
inline SMCReal(KeyEx.KEIdeal).loop SMCRealKEIdealSimp.parties.
sp 3 2.
rcondt{1} 1; first auto.
case (mod{1} = Dir /\ addr1{1} = SMCReal.self{1} /\ n1{1} = 1).
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_smc_real_ke_ideal_simp_state_wait_adv1).
rcondf{2} 2; first auto.
if{1}.
inline{1} (1) SMCReal(KeyEx.KEIdeal).party1.
rcondf{1} 3; first auto; smt().
rcondt{1} 3; first auto; smt(is_smc_real_p1_state_wait_ke2).
sp 3 0.
if{1}.
rcondf{1} 2; first auto.
move => |> &hr.
smt(KeyEx.dest_good_ke_rsp2).
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
auto.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto.
exfalso; smt().
rcondf{1} 1; first auto.
move => |> &hr.
smt(not_le_ext_nonnil_l).
rcondf{1} 1; first auto.
move => |> &hr.
smt(not_le_ext_nonnil_l).
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_smc_real_ke_ideal_simp_state_wait_adv1).
case (addr1{1} = SMCReal.self{1} ++ [2] /\ n1{1} = 3).
rcondf{1} 1; first auto; progress.
rewrite (not_le_other_branch SMCReal.self{hr}
         (SMCReal.self{hr} ++ [2]) 2 1) // le_refl.
inline KeyEx.KEIdeal.invoke.
rcondt{1} 5; first auto; smt().
inline{1} (1) KeyEx.KEIdeal.parties.
rcondf{1} 7; first auto; smt().
rcondt{1} 7; first auto; smt(KeyEx.is_ke_ideal_state_wait_sim1).
sp 7 1.
if => //.
rcondt{2} 2; first auto; smt(KeyEx.dest_good_ke_sim_rsp).
swap{2} 2 -1.
rcondf{1} 6; first auto.
move => |> &hr _ dec_ke_ideal_wait_sim1 _ _ _ [] /= _ [#] _
        _ _ _ ->> _ _ _ q _.
rewrite /= oget_some in dec_ke_ideal_wait_sim1.
by elim dec_ke_ideal_wait_sim1 => -> ->.
rcondf{1} 6; first auto.
move => |> &hr _ dec_ke_ideal_wait_sim1 _ _ _ [] /= _ [#] _
        _ _ _ ->> _ _ _ q _.
rewrite /= oget_some in dec_ke_ideal_wait_sim1.
elim dec_ke_ideal_wait_sim1 => -> -> /=.
rewrite le_refl.
rcondt{1} 7; first auto.
rcondf{1} 7; first auto.
move => |> &hr _ dec_ke_ideal_wait_sim1 _ _ _ [] /= _ [#] _
        _ _ _ ->> _ _ _ q _.
rewrite /= oget_some in dec_ke_ideal_wait_sim1.
by elim dec_ke_ideal_wait_sim1 => -> ->.
rcondt{1} 7; first auto.
move => |> &hr _ dec_ke_ideal_wait_sim1 _ _ _ [] /= _ [#] _
        _ _ _ ->> _ _ _ q _.
rewrite /= oget_some in dec_ke_ideal_wait_sim1.
by elim dec_ke_ideal_wait_sim1 => -> ->.
inline{1} (1) SMCReal(KeyEx.KEIdeal).party2.
rcondt{1} 9; first auto; smt().
rcondt{1} 9; first auto.
move => |> &hr _ dec_ke_ideal_wait_sim1 _ _ _ [] /= _ [#] _
        _ _ _ ->> _ _ _ q _.
rewrite /= oget_some in dec_ke_ideal_wait_sim1.
elim dec_ke_ideal_wait_sim1 => -> ->.
rewrite oget_some KeyEx.is_ke_rsp1.
rcondt{1} 10; first auto.
move => |> &hr _ dec_ke_ideal_wait_sim1 _ _ _ [] /= _ [#] _
        _ _ _ ->> _ _ _ q _.
rewrite /= oget_some in dec_ke_ideal_wait_sim1.
elim dec_ke_ideal_wait_sim1 => -> ->.
by rewrite oget_some KeyEx.enc_dec_ke_rsp1 oget_some.
rcondf{1} 13; first auto; progress.
by rewrite oget_some /KeyEx.ke_req2 /= le_ext_r.
rcondt{1} 14; first auto.
rcondf{1} 14; first auto.
rcondf{1} 14; first auto.
move => |> &hr.
rewrite oget_some /KeyEx.ke_req2 /=.
smt(ne_cat_nonnil_r).
rcondf{1} 14; first auto.
progress.
rewrite oget_some /KeyEx.ke_req2 /=.
rewrite (not_le_other_branch SMCReal.self{hr}
         (SMCReal.self{hr} ++ [2]) 2 1) // le_refl.
rcondt{1} 18; first auto; smt().
inline{1} (1) KeyEx.KEIdeal.parties.
rcondf{1} 20; first auto; smt().
rcondf{1} 20; first auto; smt(is_ke_ideal_state_wait_sim1).
rcondt{1} 20; first auto; smt().
rcondt{1} 21; first auto.
rcondt{1} 22; first auto.
move => |> &hr _ dec_ke_ideal_wait_sim1 _ _ _ [] /= _ [#] _
        _ _ _ ->> _ _ _ q _.
rewrite /= oget_some in dec_ke_ideal_wait_sim1.
elim dec_ke_ideal_wait_sim1 => -> ->.
by rewrite oget_some KeyEx.enc_dec_ke_req2 !oget_some.
rcondf{1} 26; first auto; progress; smt(inc_le1_not_lr).
rcondt{1} 26; first auto; progress.
rewrite oget_some /KeyEx.ke_sim_req2 /=.
smt(inc_le1_not_lr).
rcondf{1} 27; first auto.
auto => |> &1 &2 _ dec_ke_ideal_wait_sim1 _ _ _ [] /= _ [#] _
        _ _ _ ->> _ _ _ q _.
rewrite /= oget_some in dec_ke_ideal_wait_sim1.
elim dec_ke_ideal_wait_sim1 => -> ->.
rewrite !oget_some /= KeyEx.enc_dec_ke_rsp1 oget_some /=.
rewrite (SMCRealKEIdealSimpRel2 _ pt10{2} pt20{2} t{2} q)
        /smc_real_ke_ideal_simp_rel2 /#.
rcondf{1} 3; first auto.
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
auto.
seq 0 3 :
  (smc_real_ke_ideal_simp_rel1
   {|smc_real_ke_ideal_simp_rel_st_func = func;
     smc_real_ke_ideal_simp_rel_st_r1s = SMCReal.st1{1};
     smc_real_ke_ideal_simp_rel_st_r2s = SMCReal.st2{1};
     smc_real_ke_ideal_simp_rel_st_fws = Fwd.Forw.st{1};
     smc_real_ke_ideal_simp_rel_st_keis = KeyEx.KEIdeal.st{1};
     smc_real_ke_ideal_simp_rel_st_riss = SMCRealKEIdealSimp.st{2};|}
     pt1' pt2' t' /\
   SMCReal.self{1} ++ [2] = KeyEx.KEIdeal.self{1} /\
   (mod{1} = Dir /\ addr1{1} = SMCReal.self{1} /\ n1{1} = 1 \/
    mod{1} = Adv /\
    (SMCReal.self{1} ++ [1] <= addr1{1} \/
     SMCReal.self{1} ++ [2] <= addr1{1})) /\
   ! (mod{1} = Dir /\ addr1{1} = SMCReal.self{1} /\ n1{1} = 1) /\
   ! (addr1{1} = SMCReal.self{1} ++ [2] /\ n1{1} = 3) /\
   r{2} = None /\
   m0{1} = (mod{1}, pt1{1}, pt2{1}, u{1}) /\
   (addr1{1}, n1{1}) = pt1{1}).
sp 0 1.
if{2}.
rcondf{2} 2; first auto.
move => |> &hr.
progress; smt(KeyEx.dest_good_ke_sim_rsp KeyEx.port_good_ke_sim_rsp).
auto.
auto.
if{1}.
inline{1} (1) Fwd.Forw.invoke.
rcondt{1} 3; first auto; smt().
rcondf{1} 3; first auto.
move => |> &hr.
rewrite /Fwd.is_fw_req /Fwd.dec_fw_req.
smt(not_dir).
rcondt{1} 4; first auto.
rcondf{1} 5; first auto.
auto; progress; rewrite (SMCRealKEIdealSimpRel1 _ pt1' pt2' t') /#.
inline{1} (1) KeyEx.KEIdeal.invoke.
rcondf{1} 5; first auto; smt().
rcondf{1} 6; first auto.
rcondt{1} 6; first auto.
rcondf{1} 7; first auto.
auto; progress; rewrite (SMCRealKEIdealSimpRel1 _ pt1' pt2' t') /#.
case
  (exists pt1' pt2' t' q',
   smc_real_ke_ideal_simp_rel2
   {|smc_real_ke_ideal_simp_rel_st_func = func;
     smc_real_ke_ideal_simp_rel_st_r1s  = SMCReal.st1{1};
     smc_real_ke_ideal_simp_rel_st_r2s  = SMCReal.st2{1};
     smc_real_ke_ideal_simp_rel_st_fws  = Fwd.Forw.st{1};
     smc_real_ke_ideal_simp_rel_st_keis = KeyEx.KEIdeal.st{1};
     smc_real_ke_ideal_simp_rel_st_riss = SMCRealKEIdealSimp.st{2}|}
   pt1' pt2' t' q').
elim* => pt1' pt2' t' q'.
sp 3 3.
if => //.
inline SMCReal(KeyEx.KEIdeal).loop SMCRealKEIdealSimp.parties.
sp 3 2.
rcondt{1} 1; first auto.
case (mod{1} = Dir /\ addr1{1} = SMCReal.self{1} /\ n1{1} = 1).
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_smc_real_ke_ideal_simp_state_wait_adv2).
rcondf{2} 2; first auto.
if{1}.
inline{1} (1) SMCReal(KeyEx.KEIdeal).party1.
rcondf{1} 3; first auto; smt().
rcondt{1} 3; first auto; smt(is_smc_real_p1_state_wait_ke2).
sp 3 0.
if{1}.
rcondf{1} 2; first auto.
move => |> &hr.
smt(KeyEx.dest_good_ke_rsp2).
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
auto.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto.
exfalso; smt().
rcondf{1} 1; first auto.
move => |> &hr.
smt(not_le_ext_nonnil_l).
rcondf{1} 1; first auto.
move => |> &hr.
smt(not_le_ext_nonnil_l).
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_smc_real_ke_ideal_simp_state_wait_adv2).
case (addr1{1} = SMCReal.self{1} ++ [2] /\ n1{1} = 3).
rcondf{1} 1; first auto; progress.
rewrite (not_le_other_branch SMCReal.self{hr}
         (SMCReal.self{hr} ++ [2]) 2 1) // le_refl.
inline KeyEx.KEIdeal.invoke.
rcondt{1} 5; first auto; smt().
inline{1} (1) KeyEx.KEIdeal.parties.
rcondf{1} 7; first auto; smt().
rcondf{1} 7; first auto; smt().
rcondf{1} 7; first auto; smt().
rcondt{1} 7; first auto; smt(KeyEx.is_ke_ideal_state_wait_sim2).
sp 7 1.
if => //.
rcondt{2} 2; first auto; smt(KeyEx.dest_good_ke_sim_rsp).
swap{2} 2 -1.
rcondf{1} 5; first auto.
move => |> &hr _ dec_ke_ideal_wait_sim2 _ _ _ _ [] /= _ [#] _
        _ _ _ ->>.
rewrite /= oget_some in dec_ke_ideal_wait_sim2.
by elim dec_ke_ideal_wait_sim2.
rcondf{1} 5; first auto.
move => |> &hr _ dec_ke_ideal_wait_sim2 _ _ _ _ [] /= _ [#] _
        _ _ _ ->>.
rewrite /= oget_some in dec_ke_ideal_wait_sim2.
elim dec_ke_ideal_wait_sim2 => -> _ /= _.
move => _ _ _.
rewrite le_refl.
rcondt{1} 6; first auto.
rcondt{1} 6; first auto.
move => |> &hr _ dec_ke_ideal_wait_sim2 _ _ _ _ [] /= _ [#] _
        _ _ _ ->>.
rewrite /= oget_some in dec_ke_ideal_wait_sim2.
by elim dec_ke_ideal_wait_sim2 => -> _.
inline{1} (1) SMCReal(KeyEx.KEIdeal).party1.
rcondf{1} 8; first auto; smt().
rcondt{1} 8; first auto; smt(is_smc_real_p1_state_wait_ke2).
rcondt{1} 9; first auto.
move => |> &hr _ dec_ke_ideal_wait_sim2 _ _ _ _ [] /= _ [#] _
        _ _ _ ->>.
rewrite /= oget_some in dec_ke_ideal_wait_sim2.
elim dec_ke_ideal_wait_sim2 => -> _ /= _.
by rewrite oget_some KeyEx.is_ke_rsp2.
rcondt{1} 10; first auto.
move => |> &hr _ dec_ke_ideal_wait_sim2 _ _ _ _ [] /= _ [#] _
        _ _ _ ->>.
rewrite /= oget_some in dec_ke_ideal_wait_sim2.
elim dec_ke_ideal_wait_sim2 => -> _ /= _.
by rewrite oget_some KeyEx.enc_dec_ke_rsp2.
rcondf{1} 13; first auto; progress.
rewrite !oget_some /Fwd.fw_req /= le_ext_r.
rcondt{1} 14; first auto.
rcondf{1} 14; first auto.
move => |> &hr.
rewrite oget_some /Fwd.fw_req /=.
smt(ne_cat_nonnil_r).
rcondf{1} 14; first auto.
rcondt{1} 14; first auto.
move => |> &hr _ dec_ke_ideal_wait_sim2 _ _ _ _ [] /= _ [#] _
        _ _ _ ->> _ _ _.
rewrite /= oget_some in dec_ke_ideal_wait_sim2.
elim dec_ke_ideal_wait_sim2 => -> _ /= _.
rewrite !oget_some /fw_req /= le_refl.
inline Fwd.Forw.invoke.
rcondt{1} 16; first auto; smt().
rcondt{1} 16; first auto.
rcondt{1} 17; first auto.
move => |> &hr _ dec_ke_ideal_wait_sim2 _ _ _ _ [] /= _ [#] _
        _ _ _ ->> _ _ _.
rewrite /= oget_some in dec_ke_ideal_wait_sim2.
elim dec_ke_ideal_wait_sim2 => -> _ /= _.
rewrite !oget_some Fwd.enc_dec_fw_req !oget_some /=.
smt(not_le_ext_nonnil_l).
rcondt{1} 20; first auto.
move => |> &hr _ dec_ke_ideal_wait_sim2 _ _ _ _ [] /= _ [#] _
        _ _ _ ->> _ _ _.
rewrite /= oget_some in dec_ke_ideal_wait_sim2.
elim dec_ke_ideal_wait_sim2 => -> _ /= _.
by rewrite !oget_some Fwd.enc_dec_fw_req !oget_some /Fwd.fw_obs
           /= inc_nle_l.
rcondf{1} 21; first auto.
auto => |> &1 &2 dec_smc_real_ke_ideal_simp_wait_adv2
        dec_ke_ideal_wait_sim2 _ _ _ _ [] /= _
        [#] _ -> _ _ ->> ->> _ _.
rewrite /= oget_some in dec_ke_ideal_wait_sim2.
elim dec_ke_ideal_wait_sim2 => -> -> -> /=.
rewrite /= oget_some /= in dec_smc_real_ke_ideal_simp_wait_adv2.
elim dec_smc_real_ke_ideal_simp_wait_adv2 => -> [#] -> -> ->.
rewrite !oget_some Fwd.enc_dec_fw_req !oget_some
         /Fwd.fw_obs /= KeyEx.enc_dec_ke_rsp2 !oget_some /=.
rewrite (SMCRealKEIdealSimpRel3 _ pt1' pt2' t' q') /#.
rcondf{1} 3; first auto.
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
auto.
seq 0 3 :
  (smc_real_ke_ideal_simp_rel2
   {|smc_real_ke_ideal_simp_rel_st_func = func;
     smc_real_ke_ideal_simp_rel_st_r1s = SMCReal.st1{1};
     smc_real_ke_ideal_simp_rel_st_r2s = SMCReal.st2{1};
     smc_real_ke_ideal_simp_rel_st_fws = Fwd.Forw.st{1};
     smc_real_ke_ideal_simp_rel_st_keis = KeyEx.KEIdeal.st{1};
     smc_real_ke_ideal_simp_rel_st_riss = SMCRealKEIdealSimp.st{2};|}
     pt1' pt2' t' q' /\
   SMCReal.self{1} ++ [2] = KeyEx.KEIdeal.self{1} /\
   (mod{1} = Dir /\ addr1{1} = SMCReal.self{1} /\ n1{1} = 1 \/
    mod{1} = Adv /\
    (SMCReal.self{1} ++ [1] <= addr1{1} \/
     SMCReal.self{1} ++ [2] <= addr1{1})) /\
   ! (mod{1} = Dir /\ addr1{1} = SMCReal.self{1} /\ n1{1} = 1) /\
   ! (addr1{1} = SMCReal.self{1} ++ [2] /\ n1{1} = 3) /\
   r{2} = None /\
   m0{1} = (mod{1}, pt1{1}, pt2{1}, u{1}) /\
   (addr1{1}, n1{1}) = pt1{1}).
sp 0 1.
if{2}.
rcondf{2} 2; first auto.
move => |> &hr.
progress; smt(KeyEx.dest_good_ke_sim_rsp KeyEx.port_good_ke_sim_rsp).
auto.
auto.
if{1}.
inline{1} (1) Fwd.Forw.invoke.
rcondt{1} 3; first auto; smt().
rcondf{1} 3; first auto.
move => |> &hr.
rewrite /Fwd.is_fw_req /Fwd.dec_fw_req.
smt(not_dir).
rcondt{1} 4; first auto.
rcondf{1} 5; first auto.
auto; progress;
  rewrite (SMCRealKEIdealSimpRel2 _ pt1' pt2' t' q') /#.
inline{1} (1) KeyEx.KEIdeal.invoke.
rcondf{1} 5; first auto; smt().
rcondf{1} 6; first auto.
rcondt{1} 6; first auto.
rcondf{1} 7; first auto.
auto; progress;
  rewrite (SMCRealKEIdealSimpRel2 _ pt1' pt2' t' q') /#.
admit.
qed.

lemma Exper_SMCReal_KEIdeal_SMCRealKEIdealSimp
      (func' adv' : addr) (in_guard' : int fset) &m
      (Adv <: FUNC{MI, SMCReal, KeyEx.KEIdeal, SMCRealKEIdealSimp})
      (Env <: ENV{MI, SMCReal, KeyEx.KEIdeal, SMCRealKEIdealSimp, Adv}) :
  inc func' adv' =>
  Pr[Exper(MI(SMCReal(KeyEx.KEIdeal), Adv), Env).main
       (func', adv', in_guard') @ &m : res] =
  Pr[Exper(MI(SMCRealKEIdealSimp, Adv), Env).main
       (func', adv', in_guard') @ &m : res].
proof.
move => pre.
byequiv => //; proc; inline*.
seq 23 12 :
  (inc func' adv' /\ ={func, adv, in_guard, glob Adv, glob MI} /\
   func{1} = func' /\ adv{1} = adv' /\ in_guard{1} = in_guard' /\
   MI.func{1} = func' /\ MI.adv{1} = adv' /\ MI.in_guard{1} = in_guard' /\
   SMCReal.self{1} = func' /\ SMCReal.adv{1} = adv' /\
   Fwd.Forw.self{1} = func' ++ [1] /\ Fwd.Forw.adv{1} = adv' /\
   KeyEx.KEIdeal.self{1} = func' ++ [2] /\ KeyEx.KEIdeal.adv{1} = adv' /\
   SMCRealKEIdealSimp.self{2} = func' /\ SMCRealKEIdealSimp.adv{2} = adv' /\
   smc_real_ke_ideal_simp_rel
   {|smc_real_ke_ideal_simp_rel_st_func = func';
     smc_real_ke_ideal_simp_rel_st_r1s  = SMCReal.st1{1};
     smc_real_ke_ideal_simp_rel_st_r2s  = SMCReal.st2{1};
     smc_real_ke_ideal_simp_rel_st_fws  = Fwd.Forw.st{1};
     smc_real_ke_ideal_simp_rel_st_keis = KeyEx.KEIdeal.st{1};
     smc_real_ke_ideal_simp_rel_st_riss = SMCRealKEIdealSimp.st{2}|}).
call (_ : true).
auto; progress;
  by rewrite SMCRealKEIdealSimpRel0 /smc_real_ke_ideal_simp_rel0.
call
  (_ :
   inc func' adv' /\ ={glob Adv, glob MI} /\
   MI.func{1} = func' /\ MI.adv{1} = adv' /\ MI.in_guard{1} = in_guard' /\
   SMCReal.self{1} = func' /\ SMCReal.adv{1} = adv' /\
   Fwd.Forw.self{1} = func' ++ [1] /\ Fwd.Forw.adv{1} = adv' /\
   KeyEx.KEIdeal.self{1} = func' ++ [2] /\ KeyEx.KEIdeal.adv{1} = adv' /\
   SMCRealKEIdealSimp.self{2} = func' /\ SMCRealKEIdealSimp.adv{2} = adv' /\
   smc_real_ke_ideal_simp_rel
   {|smc_real_ke_ideal_simp_rel_st_func = func';
     smc_real_ke_ideal_simp_rel_st_r1s  = SMCReal.st1{1};
     smc_real_ke_ideal_simp_rel_st_r2s  = SMCReal.st2{1};
     smc_real_ke_ideal_simp_rel_st_fws  = Fwd.Forw.st{1};
     smc_real_ke_ideal_simp_rel_st_keis = KeyEx.KEIdeal.st{1};
     smc_real_ke_ideal_simp_rel_st_riss = SMCRealKEIdealSimp.st{2}|}).
proc.
sp 2 2.
if => //.
inline MI(SMCReal(KeyEx.KEIdeal), Adv).loop
       MI(SMCRealKEIdealSimp, Adv).loop.
wp; sp.
while
  (={not_done, m0, r0} /\ 
   inc func' adv' /\ ={glob Adv, glob MI} /\
   MI.func{1} = func' /\ MI.adv{1} = adv' /\ MI.in_guard{1} = in_guard' /\
   SMCReal.self{1} = func' /\ SMCReal.adv{1} = adv' /\
   Fwd.Forw.self{1} = func' ++ [1] /\ Fwd.Forw.adv{1} = adv' /\
   KeyEx.KEIdeal.self{1} = func' ++ [2] /\ KeyEx.KEIdeal.adv{1} = adv' /\
   SMCRealKEIdealSimp.self{2} = func' /\ SMCRealKEIdealSimp.adv{2} = adv' /\
   smc_real_ke_ideal_simp_rel
   {|smc_real_ke_ideal_simp_rel_st_func = func';
     smc_real_ke_ideal_simp_rel_st_r1s  = SMCReal.st1{1};
     smc_real_ke_ideal_simp_rel_st_r2s  = SMCReal.st2{1};
     smc_real_ke_ideal_simp_rel_st_fws  = Fwd.Forw.st{1};
     smc_real_ke_ideal_simp_rel_st_keis = KeyEx.KEIdeal.st{1};
     smc_real_ke_ideal_simp_rel_st_riss = SMCRealKEIdealSimp.st{2}|}).
sp 2 2.
if => //.
wp; call (SMCReal_KEIdeal_SMCRealKEIdealSimp_invoke func' adv'); auto.
wp; call (_ : true); auto.
auto.
auto.
auto.
qed.

end SMCRealKEIdealSimp.

(* make fresh version of MI *)

clone MakeInterface as MakeInt'
proof *.

module MI' = MakeInt'.MI.

module CompEnv (Env : ENV, Inter : INTER) = {
  var stub_st : msg option
  var func : addr
  var adv : addr

  module StubKE : FUNC = {
    proc init(func adv : addr) : unit = { }

    proc invoke(m : msg) : msg option = {
      var mod : mode; var pt1, pt2 : port; var u : univ;
      var addr1 : addr; var n1 : int;
      var r : msg option;
      if (stub_st <> None) {
        r <- stub_st; stub_st <- None;
      }
      else {
        r <@ Inter.invoke(m);
        if (r <> None) {
          m <- oget r; (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
          if (mod = Adv) {
            stub_st <- Some m;
            r <- Some (Adv, (adv, 1), (func ++ [2], 1), UnivUnit);
          }
        }
      }
      return r;
    }
  }

  module StubAdv : FUNC = {
    proc init(func adv : addr) : unit = { }

    proc invoke(m : msg) : msg option = {
      var mod : mode; var pt1, pt2 : port; var u : univ;
      var addr1 : addr; var n1 : int;
      var r : msg option;
      if (stub_st <> None) {
        r <- stub_st; stub_st <- None;
      }
      else {
        r <@ Inter.invoke(m);
        if (r <> None) {
          m <- oget r; (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
          if (mod = Dir) {
            stub_st <- Some m;
            (* only mode and destination address matter *)
            r <- Some (Adv, (func ++ [2], 1), (adv, 1), UnivUnit);
          }
        }
      }
      return r;
    }
  }

  (* func will end with 2 *)

  proc main(func_ adv_ : addr, in_guard : int fset) : bool = {
    var b : bool;
    stub_st <- None;
    func <- take (size func_ - 1) func_; adv <- adv_;
    b <@ Exper(MI'(SMCReal(StubKE), StubAdv), Env).main
           (func, adv, in_guard);
    return b;
  }
}.

section.

declare module Adv : FUNC{MI, SMCReal, KeyEx.KEReal, KeyEx.KEIdeal,
                          KeyEx.DDH_Adv, CompEnv}.
declare module Env : ENV{Adv, MI, SMCReal, KeyEx.KEReal, KeyEx.KEIdeal,
                         KeyEx.DDH_Adv, CompEnv}.

lemma smc_sec1_ke_real_bridge (func' adv' : addr) &m :
  exper_pre func' adv' (fset1 adv_fw_pi) =>
  Pr[Exper(MI(SMCReal(KeyEx.KEReal), Adv), Env).main
       (func', adv', fset1 adv_fw_pi) @ &m : res] =
  Pr[Exper(MI(KeyEx.KEReal, Adv), CompEnv(Env)).main
       (func' ++ [2], adv', fset1 adv_fw_pi) @ &m : res].
proof.
admit.
qed.

lemma smc_sec1_ke_ideal_bridge (func' adv' : addr) &m :
  exper_pre func' adv' (fset1 adv_fw_pi) =>
  Pr[Exper(MI(SMCReal(KeyEx.KEIdeal), Adv), Env).main
       (func', adv', fset1 adv_fw_pi) @ &m : res] =
  Pr[Exper(MI(KeyEx.KEIdeal, Adv), CompEnv(Env)).main
       (func' ++ [2], adv', fset1 adv_fw_pi) @ &m : res].
proof.
admit.
qed.

end section.

section.

declare module Adv : FUNC{MI, SMCReal, KeyEx.KEReal, KeyEx.KEIdeal,
                          KeyEx.KESim, KeyEx.DDH_Adv, CompEnv}.
declare module Env : ENV{Adv, MI, SMCReal, KeyEx.KEReal, KeyEx.KEIdeal,
                         KeyEx.KESim, KeyEx.DDH_Adv, CompEnv}.

lemma smc_sec1 (func adv : addr) &m :
  exper_pre func adv (fset1 adv_fw_pi) =>
  KeyEx.DDH_Adv.func{m} = func ++ [2] => KeyEx.DDH_Adv.adv{m} = adv =>
  `|Pr[Exper(MI(SMCReal(KeyEx.KEReal), Adv), Env).main
         (func, adv, fset1 adv_fw_pi) @ &m : res] -
    Pr[Exper(MI(SMCReal(KeyEx.KEIdeal), KeyEx.KESim(Adv)), Env).main
         (func, adv, fset1 adv_fw_pi) @ &m : res]| <=
  `|Pr[DDH1(KeyEx.DDH_Adv(CompEnv(Env), Adv)).main() @ &m : res] -
    Pr[DDH2(KeyEx.DDH_Adv(CompEnv(Env), Adv)).main() @ &m : res]|.
proof.
move => pre func_eq adv_eq.
by rewrite (smc_sec1_ke_real_bridge Adv Env func adv &m) //
           (smc_sec1_ke_ideal_bridge (KeyEx.KESim(Adv)) Env func adv &m) //
           (KeyEx.ke_security Adv (CompEnv(Env)) (func ++ [2]) adv &m) //
           exper_pre_ext1.
qed.

end section.

lemma smc_security1
      (Adv <: FUNC{MI, SMCReal, KeyEx.KEReal, KeyEx.KEIdeal,
                   KeyEx.KESim, KeyEx.DDH_Adv, CompEnv})
      (Env <: ENV{Adv, MI, SMCReal, KeyEx.KEReal, KeyEx.KEIdeal,
                  KeyEx.KESim, KeyEx.DDH_Adv, CompEnv})
      (func adv : addr) &m :
  exper_pre func adv (fset1 adv_fw_pi) =>
  KeyEx.DDH_Adv.func{m} = func ++ [2] => KeyEx.DDH_Adv.adv{m} = adv =>
  `|Pr[Exper(MI(SMCReal(KeyEx.KEReal), Adv), Env).main
         (func, adv, fset1 adv_fw_pi) @ &m : res] -
    Pr[Exper(MI(SMCReal(KeyEx.KEIdeal), KeyEx.KESim(Adv)), Env).main
         (func, adv, fset1 adv_fw_pi) @ &m : res]| <=
  `|Pr[DDH1(KeyEx.DDH_Adv(CompEnv(Env), Adv)).main() @ &m : res] -
    Pr[DDH2(KeyEx.DDH_Adv(CompEnv(Env), Adv)).main() @ &m : res]|.
proof.
move => pre func_eq adv_eq.
by apply (smc_sec1 Adv Env func adv &m).
qed.

(* padding isomorphism *)

op pad_iso_l (t : text, q : exp) : exp = log (inj t ^^ (g ^ q)).
op pad_iso_r (t : text, q : exp) : exp = log (kinv (inj t) ^^ (g ^ q)).

lemma pad_iso_lr (t : text) : cancel (pad_iso_l t) (pad_iso_r t).
proof.
rewrite /cancel /pad_iso_l /pad_iso_r => q.
by rewrite -2!/gen log_gen -kmulA kinv_l kid_l gen_log.
qed.

lemma pad_iso_rl (t : text) : cancel (pad_iso_r t) (pad_iso_l t).
proof.
rewrite /cancel /pad_iso_l /pad_iso_r => q.
by rewrite -2!/gen log_gen -kmulA kinv_r kid_l gen_log.
qed.

section.

declare module Adv : FUNC{MI, SMCReal, SMCIdeal, SMCSim, KeyEx.KEIdeal}.
declare module Env : ENV{Adv, MI, SMCReal, SMCIdeal, SMCSim, KeyEx.KEIdeal}.

local clone import SMCRealKEIdealSimp as SRKEIS.

lemma smc_sec2 (func adv : addr) &m :
  exper_pre func adv (fset1 adv_fw_pi) =>
  Pr[Exper(MI(SMCReal(KeyEx.KEIdeal), Adv), Env).main
       (func, adv, fset1 adv_fw_pi) @ &m : res] =
  Pr[Exper(MI(SMCIdeal, SMCSim(Adv)), Env).main
       (func, adv, fset1 adv_fw_pi) @ &m : res].
proof.
move => pre.
rewrite (Exper_SMCReal_KEIdeal_SMCRealKEIdealSimp func adv (fset1 adv_fw_pi)
         &m Adv Env) 1:/#.
admit.
qed.

end section.

lemma smc_security2
      (Adv <: FUNC{MI, SMCReal, SMCIdeal, SMCSim, KeyEx.KEIdeal})
      (Env <: ENV{Adv, MI, SMCReal, SMCIdeal, SMCSim, KeyEx.KEIdeal})
      (func adv : addr) &m :
  exper_pre func adv (fset1 adv_fw_pi) =>
  Pr[Exper(MI(SMCReal(KeyEx.KEIdeal), Adv), Env).main
       (func, adv, fset1 adv_fw_pi) @ &m : res] =
  Pr[Exper(MI(SMCIdeal, SMCSim(Adv)), Env).main
       (func, adv, fset1 adv_fw_pi) @ &m : res].
proof.
move => pre.
by apply (smc_sec2 Adv Env func adv &m).
qed.

lemma smc_security
      (Adv <: FUNC{MI, SMCReal, SMCIdeal, SMCSim, KeyEx.KEReal,
                   KeyEx.KEIdeal, KeyEx.KESim, KeyEx.DDH_Adv, CompEnv})
      (Env <: ENV{Adv, MI, SMCReal, SMCIdeal, SMCSim, KeyEx.KEReal,
                  KeyEx.KEIdeal, KeyEx.KESim, KeyEx.DDH_Adv, CompEnv})
      (func adv : addr) &m :
  exper_pre func adv (fset1 adv_fw_pi) =>
  KeyEx.DDH_Adv.func{m} = func ++ [2] => KeyEx.DDH_Adv.adv{m} = adv =>
  `|Pr[Exper(MI(SMCReal(KeyEx.KEReal), Adv), Env).main
         (func, adv, fset1 adv_fw_pi) @ &m : res] -
    Pr[Exper(MI(SMCIdeal, SMCSim(KeyEx.KESim(Adv))), Env).main
         (func, adv, fset1 adv_fw_pi) @ &m : res]| <=
  `|Pr[DDH1(KeyEx.DDH_Adv(CompEnv(Env), Adv)).main() @ &m : res] -
    Pr[DDH2(KeyEx.DDH_Adv(CompEnv(Env), Adv)).main() @ &m : res]|.
proof.
move => pre func_eq adv_eq.
by rewrite -(smc_security2 (KeyEx.KESim(Adv)) Env func adv &m) //
           (smc_security1 Adv Env func adv &m).
qed.
