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

(* request sent to port 1 of SMC functionality: pt1 wants to
   send x to pt2 *)

op smc_req (func : addr, pt1 pt2 : port, x : bits) : msg =
     (Dir, (func, 1), pt1,
      UnivPair (UnivPort pt2, UnivBase (BaseBits x))).

op dec_smc_req (m : msg) : (addr * port * port * bits) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Adv \/ pt1.`2 <> 1 \/ ! is_univ_pair v) ?
        None :
        let (v1, v2) = oget (dec_univ_pair v)
        in (! is_univ_port v1 \/ ! is_univ_base v2) ?
           None :
           let bse = oget (dec_univ_base v2)
           in (! is_base_bits bse) ?
              None :
              Some (pt1.`1, pt2, oget (dec_univ_port v1),
                    oget (dec_base_bits bse)).

lemma enc_dec_smc_req (func : addr, pt1 pt2 : port, x : bits) :
  dec_smc_req (smc_req func pt1 pt2 x) = Some (func, pt1, pt2, x).
proof.
by rewrite /smc_req /dec_smc_req /=
           (is_univ_pair (UnivPort pt2, UnivBase (BaseBits x))) /=
           oget_some /= (is_univ_port pt2) /= oget_some.
qed.

op is_smc_req (m : msg) : bool =
     dec_smc_req m <> None.

lemma is_smc_req (func : addr, pt1 pt2 : port, x : bits) :
  is_smc_req (smc_req func pt1 pt2 x).
proof.
by rewrite /is_smc_req enc_dec_smc_req.
qed.

(* response sent from port 2 of SMC functionality to pt2, completing
   the sending of x from pt1 *)

op smc_rsp (func : addr, pt1 pt2 : port, x : bits) : msg =
     (Dir, pt2, (func, 2), UnivPair (UnivPort pt1, UnivBase (BaseBits x))).

op dec_smc_rsp (m : msg) : (addr * port * port * bits) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Adv \/ pt2.`2 <> 2 \/ ! is_univ_pair v) ?
        None :
        let (v1, v2) = oget (dec_univ_pair v)
        in (! is_univ_port v1 \/ ! is_univ_base v2) ?
           None :
           let b = oget (dec_univ_base v2)
           in (! is_base_bits b) ?
              None :
              Some (pt2.`1, oget (dec_univ_port v1), pt1, oget (dec_base_bits b)).

lemma enc_dec_smc_rsp (func : addr, pt1 pt2 : port, x : bits) :
  dec_smc_rsp (smc_rsp func pt1 pt2 x) = Some (func, pt1, pt2, x).
proof.
by rewrite /smc_rsp /dec_smc_rsp /=
           (is_univ_pair (UnivPort pt1, UnivBase (BaseBits x))) /=
           oget_some /= (is_univ_port pt1) /= oget_some.
qed.

op is_smc_rsp (m : msg) : bool =
     dec_smc_rsp m <> None.

lemma is_smc_rsp (func : addr, pt1 pt2 : port, x : bits) :
  is_smc_rsp (smc_rsp func pt1 pt2 x).
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

type smc_real_state = [
    SMCRealStateWaitReq
  | SMCRealStateWaitKE1 of (port * port * bits)
  | SMCRealStateWaitKE2 of (port * port * bits * bits)
  | SMCRealStateWaitFwd of (port * port * bits * bits * bits)
  | SMCRealStateFinal   of (port * port * bits * bits * bits)
].

op dec_smc_real_state_wait_ke1 (st : smc_real_state) :
     (port * port * bits) option =
     with st = SMCRealStateWaitReq   => None
     with st = SMCRealStateWaitKE1 x => Some x
     with st = SMCRealStateWaitKE2 _ => None
     with st = SMCRealStateWaitFwd _ => None
     with st = SMCRealStateFinal _   => None.

lemma enc_dec_smc_real_state_wait_ke1 (x : port * port * bits) :
  dec_smc_real_state_wait_ke1 (SMCRealStateWaitKE1 x) = Some x.
proof. done. qed.

op is_smc_real_state_wait_ke1 (st : smc_real_state) : bool =
  dec_smc_real_state_wait_ke1 st <> None.

lemma is_smc_real_state_wait_ke1 (x : port * port * bits) :
  is_smc_real_state_wait_ke1 (SMCRealStateWaitKE1 x).
proof. done. qed.

op dec_smc_real_state_wait_ke2 (st : smc_real_state) :
     (port * port * bits * bits) option =
     with st = SMCRealStateWaitReq   => None
     with st = SMCRealStateWaitKE1 _ => None
     with st = SMCRealStateWaitKE2 x => Some x
     with st = SMCRealStateWaitFwd _ => None
     with st = SMCRealStateFinal _   => None.

lemma enc_dec_smc_real_state_wait_ke2 (x : port * port * bits * bits) :
  dec_smc_real_state_wait_ke2 (SMCRealStateWaitKE2 x) = Some x.
proof. done. qed.

op is_smc_real_state_wait_ke2 (st : smc_real_state) : bool =
  dec_smc_real_state_wait_ke2 st <> None.

lemma is_smc_real_state_wait_ke2 (x : port * port * bits * bits) :
  is_smc_real_state_wait_ke2 (SMCRealStateWaitKE2 x).
proof. done. qed.

op dec_smc_real_state_wait_fwd (st : smc_real_state) :
     (port * port * bits * bits * bits) option =
     with st = SMCRealStateWaitReq   => None
     with st = SMCRealStateWaitKE1 _ => None
     with st = SMCRealStateWaitKE2 _ => None
     with st = SMCRealStateWaitFwd x => Some x
     with st = SMCRealStateFinal _   => None.

lemma enc_dec_smc_real_state_wait_fwd (x : port * port * bits * bits * bits) :
  dec_smc_real_state_wait_fwd (SMCRealStateWaitFwd x) = Some x.
proof. done. qed.

op is_smc_real_state_wait_fwd (st : smc_real_state) : bool =
  dec_smc_real_state_wait_fwd st <> None.

lemma is_smc_real_state_wait_fwd (x : port * port * bits * bits * bits) :
  is_smc_real_state_wait_fwd (SMCRealStateWaitFwd x).
proof. done. qed.

op dec_smc_real_state_final (st : smc_real_state) :
     (port * port * bits * bits * bits) option =
     with st = SMCRealStateWaitReq   => None
     with st = SMCRealStateWaitKE1 _ => None
     with st = SMCRealStateWaitKE2 _ => None
     with st = SMCRealStateWaitFwd _ => None
     with st = SMCRealStateFinal x   => Some x.

lemma enc_dec_smc_real_state_final (x : port * port * bits * bits * bits) :
  dec_smc_real_state_final (SMCRealStateFinal x) = Some x.
proof. done. qed.

op is_smc_real_state_final (st : smc_real_state) : bool =
  dec_smc_real_state_final st <> None.

lemma is_smc_real_state_final (x : port * port * bits * bits * bits) :
  is_smc_real_state_final (SMCRealStateFinal x).
proof. done. qed.

module SMCReal (KE : FUNC) : FUNC = {
  var self, adv : addr
  var st : smc_real_state

  proc init(self_ adv_ : addr) : unit = {
    self <- self_; adv <- adv_;
    Fwd.Forw.init(self ++ [1], adv); KE.init(self ++ [2], adv);
    st <- SMCRealStateWaitReq;
  }

  proc parties(m : msg) : msg option = {
    var pt1, pt2, pt1', pt2' : port; var addr : addr;
    var u : univ; var x1, x2, k1, k2 : bits;
    var r : msg option <- None;
    if (st = SMCRealStateWaitReq) {  (* P1 *)
      if (is_smc_req m) {
        (* destination of m is (self, 1) *)
        (addr, pt1, pt2, x1) <- oget (dec_smc_req m);
        if (! self <= pt1.`1 /\ ! self <= pt2.`1) {
          r <-
            Some (KeyEx.ke_req1 (self ++ [2]) (self, 3) (self, 4));
          st <- SMCRealStateWaitKE1 (pt1, pt2, x1);
        }
      }
    }
    elif (is_smc_real_state_wait_ke1 st) {  (* P2 *)
      (pt1, pt2, x1) <- oget (dec_smc_real_state_wait_ke1 st);
      if (KeyEx.is_ke_rsp1 m) {
        (addr, pt1', pt2', k2) <- oget (KeyEx.dec_ke_rsp1 m);
        if (pt2' = (self, 4)) {
          (* destination of m is (self, 4) *)
          r <- Some (KeyEx.ke_req2 (self ++ [2]) (self, 4));
          st <- SMCRealStateWaitKE2 (pt1, pt2, x1, k2);
        }
      }
    }
    elif (is_smc_real_state_wait_ke2 st) {  (* P1 *)
      (pt1, pt2, x1, k2) <- oget (dec_smc_real_state_wait_ke2 st);
      if (KeyEx.is_ke_rsp2 m) {
        (addr, pt1', k1) <- oget (KeyEx.dec_ke_rsp2 m);
        if (pt1' = (self, 3)) {
          (* destination of m is (self, 3) *)
          r <-
            Some (Fwd.fw_req (self ++ [1]) (self, 3) (self, 4)
                  (UnivBase (BaseBits (x1 ^^ k1))));
          st <- SMCRealStateWaitFwd (pt1, pt2, x1, k2, k1);
        }
      }
    }
    elif (is_smc_real_state_wait_fwd st) {  (* P2 *)
      (pt1, pt2, x1, k2, k1) <- oget (dec_smc_real_state_wait_fwd st);
      if (Fwd.is_fw_rsp m) {
        (addr, pt1', pt2', u) <- oget (Fwd.dec_fw_rsp m);
        x2 <- oget (dec_base_bits (oget (dec_univ_base u))) ^^ k2;
        r <- Some (smc_rsp self pt1 pt2 x2);
        st <- SMCRealStateFinal (pt1, pt2, x1, k2, k1);
      }
    }
    return r;
  }

  proc loop(m : msg) : msg option = {
    var r : msg option <- None;
    var not_done : bool <- true;
    while (not_done) {
      if (m.`2.`1 = self) {
        r <- parties(m);
      }
      elif (self ++ [1] <= m.`2.`1) {
        r <- Fwd.Forw.invoke(m);
      }
      else {  (* self ++ [2] <= m.`2.`1 *)
        r <- KE.invoke(m);
        if (r <> None /\
            let (mod, pt1, pt2, u) = oget r in
            let (addr1, n1) = pt1
            in !((mod = Dir /\ addr1 = self /\ (n1 = 3 \/ n1 = 4)) \/
                 (mod = Adv /\ ! self <= addr1))) {
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
    (mod, pt1, pt2, u) <- m;
    (addr1, n1) <- pt1;
    if ((mod = Dir /\ addr1 = self /\ n1 = 1) \/
        (mod = Adv /\ (self ++ [1] <= addr1 \/ self ++ [2] <= addr1))) {
      r <- loop(m);
    }
    return r;
  }
}.

(* Ideal Functionality *)

(* request sent from port 3 of SMC ideal functionality to port
   smc_sim_adv_pi of SMC simulator *)

op smc_sim_req (ideal adv : addr) : msg =
     (Adv, (adv, smc_sim_adv_pi), (ideal, 3), UnivUnit).

op dec_smc_sim_req (m : msg) : (addr * addr) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Dir \/ pt1.`2 <> smc_sim_adv_pi \/ pt2.`2 <> 3 \/
         v <> UnivUnit) ?
        None :
        Some (pt2.`1, pt1.`1).

lemma enc_dec_smc_sim_req (ideal adv : addr) :
  dec_smc_sim_req (smc_sim_req ideal adv) = Some (ideal, adv).
proof. done. qed.

op is_smc_sim_req (m : msg) : bool =
     dec_smc_sim_req m <> None.

lemma is_smc_sim_req (ideal adv : addr) :
  is_smc_sim_req (smc_sim_req ideal adv).
proof. done. qed.

(* response sent from port smc_sim_adv_pi of SMC simulator to port 3
   of SMC ideal functionality *)

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
  | SMCIdealStateWaitSim of (port * port * bits)
  | SMCIdealStateFinal   of (port * port * bits)
].

op dec_smc_ideal_state_wait_sim (st : smc_ideal_state) :
     (port * port * bits) option =
     with st = SMCIdealStateWaitReq   => None
     with st = SMCIdealStateWaitSim x => Some x
     with st = SMCIdealStateFinal _   => None.

lemma enc_dec_smc_ideal_state_wait_sim (x : port * port * bits) :
  dec_smc_ideal_state_wait_sim (SMCIdealStateWaitSim x) = Some x.
proof. done. qed.

op is_smc_ideal_state_wait_sim (st : smc_ideal_state) : bool =
  dec_smc_ideal_state_wait_sim st <> None.

lemma is_smc_ideal_state_wait_sim (x : port * port * bits) :
  is_smc_ideal_state_wait_sim (SMCIdealStateWaitSim x).
proof. done. qed.

op dec_smc_ideal_state_final (st : smc_ideal_state) :
     (port * port * bits) option =
     with st = SMCIdealStateWaitReq   => None
     with st = SMCIdealStateWaitSim _ => None
     with st = SMCIdealStateFinal x   => Some x.

lemma enc_dec_smc_ideal_state_final (x : port * port * bits) :
  dec_smc_ideal_state_final (SMCIdealStateFinal x) = Some x.
proof. done. qed.

op is_smc_ideal_state_final (st : smc_ideal_state) : bool =
  dec_smc_ideal_state_final st <> None.

lemma is_smc_ideal_state_final (x : port * port * bits) :
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
    var x : bits;
    var r : msg option <- None;
    if (st = SMCIdealStateWaitReq) {  (* P1 *)
      if (is_smc_req m) {
        (* destination of m is (self, 1) *)
        (addr, pt1, pt2, x) <- oget (dec_smc_req m);
        if (! self <= pt1.`1 /\ ! self <= pt2.`1) {
          r <- Some (smc_sim_req self adv);
          st <- SMCIdealStateWaitSim (pt1, pt2, x);
        }
      }
    }
    elif (is_smc_ideal_state_wait_sim st) {  (* P2 *)
      (pt1, pt2, x) <- oget (dec_smc_ideal_state_wait_sim st);
      if (is_smc_sim_rsp m) {
        (* destination of m is (self, 3) *)
        (addr1, addr2) <- oget (dec_smc_sim_rsp m);
        r <- Some (smc_rsp self pt1 pt2 x);
        st <- SMCIdealStateFinal (pt1, pt2, x);
      }
    }
    return r;
  }

  proc invoke(m : msg) : msg option = {
    var mod : mode; var pt1, pt2 : port; var u : univ;
    var addr1 : addr; var n1 : int;
    var r : msg option <- None;
    (mod, pt1, pt2, u) <- m;
    (addr1, n1) <- pt1;
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
  | SMCSimStateWaitAdv1 of (addr * exp)
  | SMCSimStateWaitAdv2 of (addr * exp)
  | SMCSimStateWaitAdv3 of (addr * exp)
  | SMCSimStateFinal    of (addr * exp)
].

op dec_smc_sim_state_wait_adv1 (st : smc_sim_state) : (addr * exp) option =
     with st = SMCSimStateWaitReq    => None
     with st = SMCSimStateWaitAdv1 x => Some x
     with st = SMCSimStateWaitAdv2 _ => None
     with st = SMCSimStateWaitAdv3 _ => None
     with st = SMCSimStateFinal _    => None.

lemma enc_dec_smc_sim_state_wait_adv1 (x : addr * exp) :
  dec_smc_sim_state_wait_adv1 (SMCSimStateWaitAdv1 x) = Some x.
proof. done. qed.

op is_smc_sim_state_wait_adv1 (st : smc_sim_state) : bool =
  dec_smc_sim_state_wait_adv1 st <> None.

lemma is_smc_sim_state_wait_adv1 (x : addr * exp) :
  is_smc_sim_state_wait_adv1 (SMCSimStateWaitAdv1 x).
proof. done. qed.

op dec_smc_sim_state_wait_adv2 (st : smc_sim_state) : (addr * exp) option =
     with st = SMCSimStateWaitReq    => None
     with st = SMCSimStateWaitAdv1 _ => None
     with st = SMCSimStateWaitAdv2 x => Some x
     with st = SMCSimStateWaitAdv3 _ => None
     with st = SMCSimStateFinal _    => None.

lemma enc_dec_smc_sim_state_wait_adv2 (x : addr * exp) :
  dec_smc_sim_state_wait_adv2 (SMCSimStateWaitAdv2 x) = Some x.
proof. done. qed.

op is_smc_sim_state_wait_adv2 (st : smc_sim_state) : bool =
  dec_smc_sim_state_wait_adv2 st <> None.

lemma is_smc_sim_state_wait_adv2 (x : addr * exp) :
  is_smc_sim_state_wait_adv2 (SMCSimStateWaitAdv2 x).
proof. done. qed.

op dec_smc_sim_state_wait_adv3 (st : smc_sim_state) : (addr * exp) option =
     with st = SMCSimStateWaitReq    => None
     with st = SMCSimStateWaitAdv1 _ => None
     with st = SMCSimStateWaitAdv2 _ => None
     with st = SMCSimStateWaitAdv3 x => Some x
     with st = SMCSimStateFinal _    => None.

lemma enc_dec_smc_sim_state_wait_adv3 (x : addr * exp) :
  dec_smc_sim_state_wait_adv3 (SMCSimStateWaitAdv3 x) = Some x.
proof. done. qed.

op is_smc_sim_state_wait_adv3 (st : smc_sim_state) : bool =
  dec_smc_sim_state_wait_adv3 st <> None.

lemma is_smc_sim_state_wait_adv3 (x : addr * exp) :
  is_smc_sim_state_wait_adv3 (SMCSimStateWaitAdv3 x).
proof. done. qed.

op dec_smc_sim_state_final (st : smc_sim_state) : (addr * exp) option =
     with st = SMCSimStateWaitReq    => None
     with st = SMCSimStateWaitAdv1 _ => None
     with st = SMCSimStateWaitAdv2 _ => None
     with st = SMCSimStateWaitAdv3 _ => None
     with st = SMCSimStateFinal x    => Some x.

lemma enc_dec_smc_sim_state_final (x : addr * exp) :
  dec_smc_sim_state_final (SMCSimStateFinal x) = Some x.
proof. done. qed.

op is_smc_sim_state_final (st : smc_sim_state) : bool =
  dec_smc_sim_state_final st <> None.

lemma is_smc_sim_state_final (x : addr * exp) :
  is_smc_sim_state_final (SMCSimStateFinal x).
proof. done. qed.

TODO some of the following needs to be fixed...

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
            (addr1, addr2) <- oget (dec_smc_sim_req m);
            q <$ dexp;
            r <- Some (KeyEx.ke_sim_req1 (addr1 ++ [2]) self);
            st <- SMCSimStateWaitAdv1 (addr1, q);
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
            (addr, q) <- oget (dec_smc_sim_state_wait_adv1 st);
            r <- None;
            if (KeyEx.is_ke_sim_rsp1 m) {
              (addr1, addr2) <- oget (KeyEx.dec_ke_sim_rsp1 m);
              if (addr1 = addr ++ [2]) {
                r <- Some (KeyEx.ke_sim_req2 (addr ++ [2]) self);
                st <- SMCSimStateWaitAdv2 (addr, q);
              }
            }
          }
          elif (is_smc_sim_state_wait_adv2 st) {
            (addr, q) <- oget (dec_smc_sim_state_wait_adv2 st);
            r <- None;
            if (KeyEx.is_ke_sim_rsp2 m) {
              (addr1, addr2) <- oget (KeyEx.dec_ke_sim_rsp2 m);
              if (addr1 = addr ++ [2]) {
                r <-
                  Some (Fwd.fw_obs (addr ++ [1]) self (addr, 3) (addr, 4)
                        (UnivBase (BaseBits (g ^ q))));
                st <- SMCSimStateWaitAdv3 (addr, q);
              }
            }
          }
          elif (is_smc_sim_state_wait_adv3 st) {
            (addr, q) <- oget (dec_smc_sim_state_wait_adv3 st);
            r <- None;
            if (Fwd.is_fw_ok m) {
              (addr1, addr2) <- oget (Fwd.dec_fw_ok m);
              if (addr1 = addr ++ [1]) {
                r <- Some (smc_sim_rsp addr self);
                st <- SMCSimStateFinal (addr, q);
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

clone import MI_UOC.

module CompEnv (Env : ENV, Inter : INTER) = {
  module Stub : FUNC = {
    proc init(func adv : addr) : unit = { }

    proc invoke(m : msg) : msg option = {
      var r : msg option;
      r <@ Inter.invoke(m);
      return r;
    }
  }

  (* func will end with 2 *)

  proc main(func adv : addr, in_guard : int fset) : bool = {
    var b : bool;
    b <@ Exper(MI_UOC(SMCReal(Stub), Stub), Env).main
           (take (size func - 1) func, adv, in_guard);
    return b;
  }
}.

section.

declare module Adv : FUNC{MI, SMCReal, KeyEx.KEReal, KeyEx.KEIdeal,
                          KeyEx.DDH_Adv, CompEnv}.
declare module Env : ENV{Adv, MI, SMCReal, KeyEx.KEReal, KeyEx.KEIdeal,
                         KeyEx.DDH_Adv, CompEnv}.

(*
type smc_sec1_ke_real_bridge_st = {
  func  : addr;
  smcrs : smc_real_state;
  fws   : Fwd.fw_state;
  

}.

   SMCReal.st{1} = SMCRealStateWaitReq /\
   Fwd.Forw.st{1} = Fwd.FwStateInit /\
   KeyEx.Fwd1.Forw.st{1} = KeyEx.Fwd1.FwStateInit /\
   KeyEx.Fwd2.Forw.st{1} = KeyEx.Fwd2.FwStateInit ==>



pred smc_sec2_rel0 (st : smc_sec2_st) =
  (st.`smcrs = SMCRealStateWaitReq) /\
  (st.`fws   = Fwd.FwStateInit) /\
  (st.`keis  = KeyEx.KEIdealStateWaitReq1) /\
  (st.`smcis = SMCIdealStateWaitReq) /\
  (st.`smcss = SMCSimStateWaitReq).

inductive smc_sec2_rel (st : smc_sec2_st) =
    SMCSec2Rel0 of (smc_sec2_rel0 st)
  | SMCSec2Rel1 (pt1 pt2 : port, x : bits, q : exp) of
      (smc_sec2_rel1 st pt1 pt2 x q)
  | SMCSec2Rel2 (pt1 pt2 : port, x : bits, q : exp) of
      (smc_sec2_rel2 st pt1 pt2 x q)
  | SMCSec2Rel3 (pt1 pt2 : port, x : bits, q : exp) of
      (smc_sec2_rel3 st pt1 pt2 x q)
  | SMCSec2Rel4 (pt1 pt2 : port, x : bits, q : exp) of
      (smc_sec2_rel4 st pt1 pt2 x q).

*)

lemma smc_sec1_ke_real_bridge (func adv : addr) &m :
  exper_pre func adv (fset1 adv_fw_pi) =>
  Pr[Exper(MI(SMCReal(KeyEx.KEReal), Adv), Env).main
       (func, adv, fset1 adv_fw_pi) @ &m : res] =
  Pr[Exper(MI(KeyEx.KEReal, Adv), CompEnv(Env)).main
       (func ++ [2], adv, fset1 adv_fw_pi) @ &m : res].
proof.
move : func adv; move => func' adv' pre.
byequiv => //.
proc; inline*; wp; swap{2} 22 26; sp.
conseq
  (_ :
   exper_pre func' adv' (fset1 adv_fw_pi) /\
   ={SMCReal.self, SMCReal.adv, SMCReal.st,
     Fwd.Forw.self, Fwd.Forw.adv, Fwd.Forw.st,
     KeyEx.Fwd1.Forw.self, KeyEx.Fwd1.Forw.adv, KeyEx.Fwd1.Forw.st,
     KeyEx.Fwd2.Forw.self, KeyEx.Fwd2.Forw.adv, KeyEx.Fwd2.Forw.st} /\
   func{1} = func' /\ adv{1} = adv' /\ in_guard{1} = fset1 adv_fw_pi /\
   func1{2} = func' /\ adv1{2} = adv' /\ in_guard1{2} = fset1 adv_fw_pi /\
   MI.func{1} = func' /\ MI.adv{1} = adv' /\ MI.in_guard{1} = fset1 adv_fw_pi /\
   ={func, adv, in_guard}(MI, MI_UOC) /\
   MI.func{2} = func' ++ [2] /\ MI.adv{2} = adv' /\
   MI.in_guard{2} = fset1 adv_fw_pi /\
   Fwd.Forw.self{1} = func' ++ [1] /\ Fwd.Forw.adv{1} = adv' /\
   KeyEx.Fwd1.Forw.self{1} = func' ++ [2; 1] /\ KeyEx.Fwd1.Forw.adv{1} = adv' /\
   KeyEx.Fwd2.Forw.self{1} = func' ++ [2; 2] /\ KeyEx.Fwd2.Forw.adv{1} = adv' /\
   SMCReal.st{1} = SMCRealStateWaitReq /\
   Fwd.Forw.st{1} = Fwd.FwStateInit /\
   KeyEx.Fwd1.Forw.st{1} = KeyEx.Fwd1.FwStateInit /\
   KeyEx.Fwd2.Forw.st{1} = KeyEx.Fwd2.FwStateInit ==>
   _).
(progress;
   first 4 by rewrite size_cat /= -addzA /= (take_size_cat (size func{1})));
  by rewrite -catA.  
seq 1 1 :
  (exper_pre func' adv' (fset1 adv_fw_pi) /\
   ={glob Adv,
     SMCReal.self, SMCReal.adv, SMCReal.st,
     Fwd.Forw.self, Fwd.Forw.adv, Fwd.Forw.st,
     KeyEx.Fwd1.Forw.self, KeyEx.Fwd1.Forw.adv, KeyEx.Fwd1.Forw.st,
     KeyEx.Fwd2.Forw.self, KeyEx.Fwd2.Forw.adv, KeyEx.Fwd2.Forw.st} /\
   func{1} = func' /\ adv{1} = adv' /\ in_guard{1} = fset1 adv_fw_pi /\
   func1{2} = func' /\ adv1{2} = adv' /\ in_guard1{2} = fset1 adv_fw_pi /\
   MI.func{1} = func' /\ MI.adv{1} = adv' /\ MI.in_guard{1} = fset1 adv_fw_pi /\
   ={func, adv, in_guard}(MI, MI_UOC) /\
   MI.func{2} = func' ++ [2] /\ MI.adv{2} = adv' /\
   MI.in_guard{2} = fset1 adv_fw_pi /\
   Fwd.Forw.self{1} = func' ++ [1] /\ Fwd.Forw.adv{1} = adv' /\
   KeyEx.Fwd1.Forw.self{1} = func' ++ [2; 1] /\ KeyEx.Fwd1.Forw.adv{1} = adv' /\
   KeyEx.Fwd2.Forw.self{1} = func' ++ [2; 2] /\ KeyEx.Fwd2.Forw.adv{1} = adv' /\
   SMCReal.st{1} = SMCRealStateWaitReq /\
   Fwd.Forw.st{1} = Fwd.FwStateInit /\
   KeyEx.Fwd1.Forw.st{1} = KeyEx.Fwd1.FwStateInit /\
   KeyEx.Fwd2.Forw.st{1} = KeyEx.Fwd2.FwStateInit).
call (_ : true); first auto.
call
  (_ :
   ={glob Adv,
     SMCReal.self, SMCReal.adv, SMCReal.st,
     Fwd.Forw.self, Fwd.Forw.adv, Fwd.Forw.st,
     KeyEx.Fwd1.Forw.self, KeyEx.Fwd1.Forw.adv, KeyEx.Fwd1.Forw.st,
     KeyEx.Fwd2.Forw.self, KeyEx.Fwd2.Forw.adv, KeyEx.Fwd2.Forw.st} /\
   exper_pre MI.func{1} MI.adv{1} MI.in_guard{1} /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   ={func, adv, in_guard}(MI, MI_UOC) /\
   MI.func{2} = MI.func{1} ++ [2] /\ MI.adv{2} = MI.adv{1} /\
   MI.in_guard{2} = fset1 adv_fw_pi /\
   Fwd.Forw.self{1} = MI.func{1} ++ [1] /\ Fwd.Forw.adv{1} = MI.adv{1} /\
   KeyEx.Fwd1.Forw.self{1} = MI.func{1} ++ [2; 1] /\
   KeyEx.Fwd2.Forw.adv{1} = MI.adv{1} /\
   KeyEx.Fwd2.Forw.self{1} = MI.func{1} ++ [2; 2] /\
   KeyEx.Fwd1.Forw.adv{1} = MI.adv{1} /\
   SMCReal.st{1} = SMCRealStateWaitReq /\
   Fwd.Forw.st{1} = Fwd.FwStateInit /\
   KeyEx.Fwd1.Forw.st{1} = KeyEx.Fwd1.FwStateInit /\
   KeyEx.Fwd2.Forw.st{1} = KeyEx.Fwd2.FwStateInit).
proc.
admit.
auto.
qed.

lemma smc_sec1_ke_ideal_bridge (func adv : addr) &m :
  exper_pre func adv (fset1 adv_fw_pi) =>
  Pr[Exper(MI(SMCReal(KeyEx.KEIdeal), Adv), Env).main
       (func, adv, fset1 adv_fw_pi) @ &m : res] =
  Pr[Exper(MI(KeyEx.KEIdeal, Adv), CompEnv(Env)).main
       (func ++ [2], adv, fset1 adv_fw_pi) @ &m : res].
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
rewrite (smc_sec1_ke_real_bridge Adv Env func adv &m) //.
rewrite (smc_sec1_ke_ideal_bridge (KeyEx.KESim(Adv)) Env func adv &m) //.
apply (KeyEx.ke_security Adv (CompEnv(Env)) (func ++ [2]) adv &m) => //.
by apply exper_pre_ext1.
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

op pad_iso (x : bits, q : exp) : exp = log (gen q ^^ x).
  
lemma pad_isoK (x : bits) : involutive (pad_iso x).
proof.
rewrite /involutive /cancel /pad_iso => q.
by rewrite gen_logK xorA xorK xor_0 log_genK.
qed.

type smc_sec2_st = {
  smc_sec2_st_func  : addr;
  smc_sec2_st_smcrs : smc_real_state;
  smc_sec2_st_fws   : Fwd.fw_state;
  smc_sec2_st_keis  : KeyEx.ke_ideal_state;
  smc_sec2_st_smcis : smc_ideal_state;
  smc_sec2_st_smcss : smc_sim_state
}.

pred smc_sec2_rel0 (st : smc_sec2_st) =
  (st.`smc_sec2_st_smcrs = SMCRealStateWaitReq) /\
  (st.`smc_sec2_st_fws   = Fwd.FwStateInit) /\
  (st.`smc_sec2_st_keis  = KeyEx.KEIdealStateWaitReq1) /\
  (st.`smc_sec2_st_smcis = SMCIdealStateWaitReq) /\
  (st.`smc_sec2_st_smcss = SMCSimStateWaitReq).

pred smc_sec2_rel1 (st : smc_sec2_st, pt1 pt2 : port, x : bits, q : exp) =
  ! st.`smc_sec2_st_func <= pt1.`1 /\ ! st.`smc_sec2_st_func <= pt2.`1 /\ 
  (st.`smc_sec2_st_smcrs = SMCRealStateWaitKE1 (pt1, pt2, x)) /\
  (st.`smc_sec2_st_fws   = Fwd.FwStateInit) /\
  (st.`smc_sec2_st_keis  = KeyEx.KEIdealStateWaitSim1 ((st.`smc_sec2_st_func, 1), (st.`smc_sec2_st_func, 2), q)) /\
  (st.`smc_sec2_st_smcis = SMCIdealStateWaitSim (pt1, pt2, x)) /\
  (st.`smc_sec2_st_smcss = SMCSimStateWaitAdv1 (st.`smc_sec2_st_func, pad_iso x q)).

pred smc_sec2_rel2 (st : smc_sec2_st, pt1 pt2 : port, x : bits, q : exp) =
  ! st.`smc_sec2_st_func <= pt1.`1 /\ ! st.`smc_sec2_st_func <= pt2.`1 /\ 
  (st.`smc_sec2_st_smcrs = SMCRealStateWaitKE2 (pt1, pt2, x, g ^ q)) /\
  (st.`smc_sec2_st_fws   = Fwd.FwStateInit) /\
  (st.`smc_sec2_st_keis  = KeyEx.KEIdealStateWaitSim2 ((st.`smc_sec2_st_func, 1), (st.`smc_sec2_st_func, 2), q)) /\
  (st.`smc_sec2_st_smcis = SMCIdealStateWaitSim (pt1, pt2, x)) /\
  (st.`smc_sec2_st_smcss = SMCSimStateWaitAdv2 (st.`smc_sec2_st_func, pad_iso x q)).

pred smc_sec2_rel3 (st : smc_sec2_st, pt1 pt2 : port, x : bits, q : exp) =
  ! st.`smc_sec2_st_func <= pt1.`1 /\ ! st.`smc_sec2_st_func <= pt2.`1 /\ 
  (st.`smc_sec2_st_smcrs =
     SMCRealStateWaitFwd (pt1, pt2, x, g ^ q, g ^ q)) /\
  (st.`smc_sec2_st_fws   =
     Fwd.FwStateWait
     ((st.`smc_sec2_st_func, 1), (st.`smc_sec2_st_func, 2), UnivBase (BaseBits (x ^^ g ^ q)))) /\
  (st.`smc_sec2_st_keis  = KeyEx.KEIdealStateFinal ((st.`smc_sec2_st_func, 1), (st.`smc_sec2_st_func, 2), q)) /\
  (st.`smc_sec2_st_smcis = SMCIdealStateWaitSim (pt1, pt2, x)) /\
  (st.`smc_sec2_st_smcss = SMCSimStateWaitAdv3 (st.`smc_sec2_st_func, pad_iso x q)).

pred smc_sec2_rel4 (st : smc_sec2_st, pt1, pt2 : port, x : bits, q : exp) =
  (st.`smc_sec2_st_smcrs = SMCRealStateFinal (pt1, pt2, x, g ^ q, g ^ q)) /\
  (st.`smc_sec2_st_fws   =
     Fwd.FwStateFinal
     ((st.`smc_sec2_st_func, 1), (st.`smc_sec2_st_func, 2), UnivBase (BaseBits (x ^^ g ^ q)))) /\
  (st.`smc_sec2_st_keis  = KeyEx.KEIdealStateFinal ((st.`smc_sec2_st_func, 1), (st.`smc_sec2_st_func, 2), q)) /\
  (st.`smc_sec2_st_smcis = SMCIdealStateFinal (pt1, pt2, x)) /\
  (st.`smc_sec2_st_smcss = SMCSimStateFinal (st.`smc_sec2_st_func, pad_iso x q)).

inductive smc_sec2_rel (st : smc_sec2_st) =
    SMCSec2Rel0 of (smc_sec2_rel0 st)
  | SMCSec2Rel1 (pt1 pt2 : port, x : bits, q : exp) of
      (smc_sec2_rel1 st pt1 pt2 x q)
  | SMCSec2Rel2 (pt1 pt2 : port, x : bits, q : exp) of
      (smc_sec2_rel2 st pt1 pt2 x q)
  | SMCSec2Rel3 (pt1 pt2 : port, x : bits, q : exp) of
      (smc_sec2_rel3 st pt1 pt2 x q)
  | SMCSec2Rel4 (pt1 pt2 : port, x : bits, q : exp) of
      (smc_sec2_rel4 st pt1 pt2 x q).

inductive smc_sec2_rel_1_4 (st : smc_sec2_st) =
    SMCSec2Rel1_1_4 (pt1 pt2 : port, x : bits, q : exp) of
      (smc_sec2_rel1 st pt1 pt2 x q)
  | SMCSec2Rel2_1_4 (pt1 pt2 : port, x : bits, q : exp) of
      (smc_sec2_rel2 st pt1 pt2 x q)
  | SMCSec2Rel3_1_4 (pt1 pt2 : port, x : bits, q : exp) of
      (smc_sec2_rel3 st pt1 pt2 x q)
  | SMCSec2Rel4_1_4 (pt1 pt2 : port, x : bits, q : exp) of
      (smc_sec2_rel4 st pt1 pt2 x q).

inductive smc_sec2_rel_2_4 (st : smc_sec2_st) =
    SMCSec2Rel2_2_4 (pt1 pt2 : port, x : bits, q : exp) of
      (smc_sec2_rel2 st pt1 pt2 x q)
  | SMCSec2Rel3_2_4 (pt1 pt2 : port, x : bits, q : exp) of
      (smc_sec2_rel3 st pt1 pt2 x q)
  | SMCSec2Rel4_2_4 (pt1 pt2 : port, x : bits, q : exp) of
      (smc_sec2_rel4 st pt1 pt2 x q).

inductive smc_sec2_rel_3_4 (st : smc_sec2_st) =
    SMCSec2Rel3_3_4 (pt1 pt2 : port, x : bits, q : exp) of
      (smc_sec2_rel3 st pt1 pt2 x q)
  | SMCSec2Rel4_3_4 (pt1 pt2 : port, x : bits, q : exp) of
      (smc_sec2_rel4 st pt1 pt2 x q).

inductive smc_sec2_rel_4_4 (st : smc_sec2_st) =
    SMCSec2Rel4_4_4 (pt1 pt2 : port, x : bits, q : exp) of
      (smc_sec2_rel4 st pt1 pt2 x q).

lemma smc_sec2_rel_1_4_imp_full (st : smc_sec2_st) :
  smc_sec2_rel_1_4 st => smc_sec2_rel st.
proof.
case;
  [apply SMCSec2Rel1 | apply SMCSec2Rel2 | apply SMCSec2Rel3 |
   apply SMCSec2Rel4].
qed.

lemma smc_sec2_rel_2_4_imp_full (st : smc_sec2_st) :
  smc_sec2_rel_2_4 st => smc_sec2_rel st.
proof.
case; [apply SMCSec2Rel2 | apply SMCSec2Rel3 | apply SMCSec2Rel4].
qed.

lemma smc_sec2_rel_3_4_imp_full (st : smc_sec2_st) :
  smc_sec2_rel_3_4 st => smc_sec2_rel st.
proof.
case; [apply SMCSec2Rel3 | apply SMCSec2Rel4].
qed.

lemma smc_sec2_rel_4_imp_full (st : smc_sec2_st) :
  smc_sec2_rel_4_4 st => smc_sec2_rel st.
proof.
case; apply SMCSec2Rel4.
qed.

section.

declare module Adv : FUNC{MI, SMCReal, KeyEx.KEIdeal, SMCIdeal, SMCSim}.
declare module Env : ENV{Adv, MI, SMCReal, KeyEx.KEIdeal, SMCIdeal, SMCSim}.

lemma MI_SMCReal_KEIdeal_Adv_SMCIdeal_SMCSim_Adv_invoke_4 :
  equiv
  [MI(SMCReal(KeyEx.KEIdeal), Adv).invoke ~
   MI(SMCIdeal, SMCSim(Adv)).invoke :
   ={m, MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   Fwd.Forw.self{1} = MI.func{1} ++ [1] /\
   Fwd.Forw.adv{1} = MI.adv{1} /\
   KeyEx.KEIdeal.self{1} = MI.func{1} ++ [2] /\
   KeyEx.KEIdeal.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   ={glob Adv} /\
   (exists (pt1 pt2 : port, x : bits, q : exp),
    smc_sec2_rel4
    {|smc_sec2_st_func = MI.func{1}; smc_sec2_st_smcrs = SMCReal.st{1};
      smc_sec2_st_fws = Fwd.Forw.st{1}; smc_sec2_st_keis = KeyEx.KEIdeal.st{1};
      smc_sec2_st_smcis = SMCIdeal.st{2}; smc_sec2_st_smcss = SMCSim.st{2}|}
    pt1 pt2 x q) ==>
   ={res, MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   Fwd.Forw.self{1} = MI.func{1} ++ [1] /\
   Fwd.Forw.adv{1} = MI.adv{1} /\
   KeyEx.KEIdeal.self{1} = MI.func{1} ++ [2] /\
   KeyEx.KEIdeal.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   ={glob Adv} /\
   smc_sec2_rel_4_4
   {|smc_sec2_st_func = MI.func{1}; smc_sec2_st_smcrs = SMCReal.st{1};
     smc_sec2_st_fws = Fwd.Forw.st{1}; smc_sec2_st_keis = KeyEx.KEIdeal.st{1};
     smc_sec2_st_smcis = SMCIdeal.st{2}; smc_sec2_st_smcss = SMCSim.st{2}|}].
proof.
admit.
qed.

lemma MI_SMCReal_KEIdeal_Adv_SMCIdeal_SMCSim_Adv_invoke_3 :
  equiv
  [MI(SMCReal(KeyEx.KEIdeal), Adv).invoke ~
   MI(SMCIdeal, SMCSim(Adv)).invoke :
   ={m, MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   Fwd.Forw.self{1} = MI.func{1} ++ [1] /\
   Fwd.Forw.adv{1} = MI.adv{1} /\
   KeyEx.KEIdeal.self{1} = MI.func{1} ++ [2] /\
   KeyEx.KEIdeal.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   ={glob Adv} /\
   (exists (pt1 pt2 : port, x : bits, q : exp),
    smc_sec2_rel3
    {|smc_sec2_st_func = MI.func{1}; smc_sec2_st_smcrs = SMCReal.st{1};
      smc_sec2_st_fws = Fwd.Forw.st{1}; smc_sec2_st_keis = KeyEx.KEIdeal.st{1};
      smc_sec2_st_smcis = SMCIdeal.st{2}; smc_sec2_st_smcss = SMCSim.st{2}|}
    pt1 pt2 x q) ==>
   ={res, MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   Fwd.Forw.self{1} = MI.func{1} ++ [1] /\
   Fwd.Forw.adv{1} = MI.adv{1} /\
   KeyEx.KEIdeal.self{1} = MI.func{1} ++ [2] /\
   KeyEx.KEIdeal.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   ={glob Adv} /\
   smc_sec2_rel_3_4
   {|smc_sec2_st_func = MI.func{1}; smc_sec2_st_smcrs = SMCReal.st{1};
     smc_sec2_st_fws = Fwd.Forw.st{1}; smc_sec2_st_keis = KeyEx.KEIdeal.st{1};
     smc_sec2_st_smcis = SMCIdeal.st{2}; smc_sec2_st_smcss = SMCSim.st{2}|}].
proof.
admit.
qed.

lemma MI_SMCReal_KEIdeal_Adv_SMCIdeal_SMCSim_Adv_invoke_2 :
  equiv
  [MI(SMCReal(KeyEx.KEIdeal), Adv).invoke ~
   MI(SMCIdeal, SMCSim(Adv)).invoke :
   ={m, MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   Fwd.Forw.self{1} = MI.func{1} ++ [1] /\
   Fwd.Forw.adv{1} = MI.adv{1} /\
   KeyEx.KEIdeal.self{1} = MI.func{1} ++ [2] /\
   KeyEx.KEIdeal.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   ={glob Adv} /\
   (exists (pt1 pt2 : port, x : bits, q : exp),
    smc_sec2_rel2
    {|smc_sec2_st_func = MI.func{1}; smc_sec2_st_smcrs = SMCReal.st{1};
      smc_sec2_st_fws = Fwd.Forw.st{1}; smc_sec2_st_keis = KeyEx.KEIdeal.st{1};
      smc_sec2_st_smcis = SMCIdeal.st{2}; smc_sec2_st_smcss = SMCSim.st{2}|}
    pt1 pt2 x q) ==>
   ={res, MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   Fwd.Forw.self{1} = MI.func{1} ++ [1] /\
   Fwd.Forw.adv{1} = MI.adv{1} /\
   KeyEx.KEIdeal.self{1} = MI.func{1} ++ [2] /\
   KeyEx.KEIdeal.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   ={glob Adv} /\
   smc_sec2_rel_2_4
   {|smc_sec2_st_func = MI.func{1}; smc_sec2_st_smcrs = SMCReal.st{1};
     smc_sec2_st_fws = Fwd.Forw.st{1}; smc_sec2_st_keis = KeyEx.KEIdeal.st{1};
     smc_sec2_st_smcis = SMCIdeal.st{2}; smc_sec2_st_smcss = SMCSim.st{2}|}].
proof.
admit.
qed.

lemma MI_SMCReal_KEIdeal_Adv_SMCIdeal_SMCSim_Adv_invoke_1 :
  equiv
  [MI(SMCReal(KeyEx.KEIdeal), Adv).invoke ~
   MI(SMCIdeal, SMCSim(Adv)).invoke :
   ={m, MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   Fwd.Forw.self{1} = MI.func{1} ++ [1] /\
   Fwd.Forw.adv{1} = MI.adv{1} /\
   KeyEx.KEIdeal.self{1} = MI.func{1} ++ [2] /\
   KeyEx.KEIdeal.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   ={glob Adv} /\
   (exists (pt1 pt2 : port, x : bits, q : exp),
    smc_sec2_rel1
    {|smc_sec2_st_func = MI.func{1}; smc_sec2_st_smcrs = SMCReal.st{1};
      smc_sec2_st_fws = Fwd.Forw.st{1}; smc_sec2_st_keis = KeyEx.KEIdeal.st{1};
      smc_sec2_st_smcis = SMCIdeal.st{2}; smc_sec2_st_smcss = SMCSim.st{2}|}
    pt1 pt2 x q) ==>
   ={res, MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   Fwd.Forw.self{1} = MI.func{1} ++ [1] /\
   Fwd.Forw.adv{1} = MI.adv{1} /\
   KeyEx.KEIdeal.self{1} = MI.func{1} ++ [2] /\
   KeyEx.KEIdeal.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   ={glob Adv} /\
   smc_sec2_rel_1_4
   {|smc_sec2_st_func = MI.func{1}; smc_sec2_st_smcrs = SMCReal.st{1};
     smc_sec2_st_fws = Fwd.Forw.st{1}; smc_sec2_st_keis = KeyEx.KEIdeal.st{1};
     smc_sec2_st_smcis = SMCIdeal.st{2}; smc_sec2_st_smcss = SMCSim.st{2}|}].
proof.
admit.
qed.

lemma MI_SMCReal_KEIdeal_Adv_SMCIdeal_SMCSim_Adv_invoke_0 :
  equiv
  [MI(SMCReal(KeyEx.KEIdeal), Adv).invoke ~
   MI(SMCIdeal, SMCSim(Adv)).invoke :
   ={m, MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   Fwd.Forw.self{1} = MI.func{1} ++ [1] /\
   Fwd.Forw.adv{1} = MI.adv{1} /\
   KeyEx.KEIdeal.self{1} = MI.func{1} ++ [2] /\
   KeyEx.KEIdeal.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   ={glob Adv} /\
   smc_sec2_rel0
   {|smc_sec2_st_func = MI.func{1}; smc_sec2_st_smcrs = SMCReal.st{1};
     smc_sec2_st_fws = Fwd.Forw.st{1}; smc_sec2_st_keis = KeyEx.KEIdeal.st{1};
     smc_sec2_st_smcis = SMCIdeal.st{2}; smc_sec2_st_smcss = SMCSim.st{2}|} ==>
   ={res, MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   Fwd.Forw.self{1} = MI.func{1} ++ [1] /\
   Fwd.Forw.adv{1} = MI.adv{1} /\
   KeyEx.KEIdeal.self{1} = MI.func{1} ++ [2] /\
   KeyEx.KEIdeal.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   ={glob Adv} /\
   smc_sec2_rel
   {|smc_sec2_st_func = MI.func{1}; smc_sec2_st_smcrs = SMCReal.st{1};
     smc_sec2_st_fws = Fwd.Forw.st{1}; smc_sec2_st_keis = KeyEx.KEIdeal.st{1};
     smc_sec2_st_smcis = SMCIdeal.st{2}; smc_sec2_st_smcss = SMCSim.st{2}|}].
proof.
proc.
sp 2 2.
if => //; last first.
auto; progress; by apply SMCSec2Rel0.
inline MI(SMCReal(KeyEx.KEIdeal), Adv).loop
       MI(SMCIdeal, SMCSim(Adv)).loop.
sp 3 3.
rcondt{1} 1; first progress. rcondt{2} 1; first progress.
sp 2 2.
if => //.
inline{1} (1) SMCReal(KeyEx.KEIdeal).invoke.
inline{2} (1) SMCIdeal.invoke.
sp 4 4.
if => //.
progress; smt(inc_ext2).
admit.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto; progress; by apply SMCSec2Rel0.
inline{2} (1) SMCSim(Adv).invoke.
sp 0 3.
rcondt{2} 1.
progress; auto; progress; smt().
inline{2} (1) SMCSim(Adv).loop.
rcondt{2} 4; progress; auto.
sp 0 4.
rcondf{2} 1; progress; auto; progress.
have smc_pi_uniq := smc_pi_uniq.
rewrite cons_uniq 3!in_cons in_nil 2!negb_or /= in smc_pi_uniq.
smt(in_fset1).
seq 1 1 :
   (r0{1} = r2{2} /\ not_done{1} /\ not_done{2} /\
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   Fwd.Forw.self{1} = MI.func{1} ++ [1] /\
   Fwd.Forw.adv{1} = MI.adv{1} /\
   KeyEx.KEIdeal.self{1} = MI.func{1} ++ [2] /\
   KeyEx.KEIdeal.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\  SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   ={glob Adv} /\
   smc_sec2_rel0
   {|smc_sec2_st_func = MI.func{1}; smc_sec2_st_smcrs = SMCReal.st{1};
     smc_sec2_st_fws = Fwd.Forw.st{1}; smc_sec2_st_keis = KeyEx.KEIdeal.st{1};
     smc_sec2_st_smcis = SMCIdeal.st{2}; smc_sec2_st_smcss = SMCSim.st{2};|}).
call (_ : true).
auto.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondt{2} 4; first auto.
rcondf{2} 5; first auto.
auto; progress; by apply SMCSec2Rel0.
sp 3 2.
rcondf{2} 1; first auto; progress; smt().
rcondf{2} 1; first auto; progress; smt().
rcondf{2} 1; first auto; progress; smt().
rcondf{2} 2; first auto.
rcondf{2} 4; first auto.
sp 0 6.
if => //.
move => |> &1 &2 <- //.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto; progress; by apply SMCSec2Rel0.
if => //.
move => |> &1 &2 <- //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto; progress; by apply SMCSec2Rel0.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sp 2 2.
elim* => addr10_R n10_R mod0_R pt10_R pt20_R u0_R addr10_L n10_L mod0_L
         pt10_L pt20_L u0_L.
rcondt{1} 1; first auto.
rcondt{2} 1; first progress; auto => |> &hr <- //.
inline{1} (1) SMCReal(KeyEx.KEIdeal).invoke.
inline{2} (1) SMCIdeal.invoke.
sp 4 4.
conseq
  (_ :
   _ ==>
   r0{1} = None /\ r0{2} = None /\
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   SMCReal.self{1} = MI.func{1} /\
   SMCReal.adv{1} = MI.adv{1} /\
   Fwd.Forw.self{1} = MI.func{1} ++ [1] /\
   Fwd.Forw.adv{1} = MI.adv{1} /\
   KeyEx.KEIdeal.self{1} = MI.func{1} ++ [2] /\
   KeyEx.KEIdeal.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\
   SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\
   SMCSim.adv{2} = [] /\
   ={glob Adv} /\
   smc_sec2_rel
    {|smc_sec2_st_func = MI.func{1}; smc_sec2_st_smcrs = SMCReal.st{1};
      smc_sec2_st_fws = Fwd.Forw.st{1}; smc_sec2_st_keis = KeyEx.KEIdeal.st{1};
      smc_sec2_st_smcis = SMCIdeal.st{2}; smc_sec2_st_smcss = SMCSim.st{2};|}) => //.
rcondf{2} 1.
auto => |> &hr <-; progress; smt().
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
if{1}.
inline{1} (1) SMCReal(KeyEx.KEIdeal).loop.
rcondt{1} 4; first auto.
sp 3 0.
if{1}.
inline{1} (1) SMCReal(KeyEx.KEIdeal).parties.
sp 2 0.
rcondt{1} 1.
progress; auto; progress; smt().
rcondf{1} 1.
progress; auto; progress.
rewrite /is_smc_req /dec_smc_req /#.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{1} 5.
progress; auto; progress.
rcondf{1} 6; first auto.
auto; progress; by apply SMCSec2Rel0.
if{1}.
inline{1} (1) Fwd.Forw.invoke.
rcondt{1} 3.
progress; auto; smt().
rcondf{1} 3.
progress; auto; progress.
rewrite /is_fw_req /dec_fw_req /#.
rcondt{1} 4; first auto.
rcondf{1} 5; first auto.
rcondt{1} 7; first auto.
rcondf{1} 8; first auto.
auto; progress; by apply SMCSec2Rel0.
inline{1} (1) KeyEx.KEIdeal.invoke.
rcondf{1} 5.
progress; auto; progress; smt().
rcondf{1} 6; first auto.
rcondt{1} 6; first auto.
rcondf{1} 7; first auto.
rcondt{1} 9; first auto.
rcondf{1} 10; first auto.
auto; progress; by apply SMCSec2Rel0.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto; progress; by apply SMCSec2Rel0.
qed.

lemma MI_SMCReal_KEIdeal_Adv_SMCIdeal_SMCSim_Adv_invoke :
  equiv
  [MI(SMCReal(KeyEx.KEIdeal), Adv).invoke ~
   MI(SMCIdeal, SMCSim(Adv)).invoke :
   ={m, MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   Fwd.Forw.self{1} = MI.func{1} ++ [1] /\
   Fwd.Forw.adv{1} = MI.adv{1} /\
   KeyEx.KEIdeal.self{1} = MI.func{1} ++ [2] /\
   KeyEx.KEIdeal.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   ={glob Adv} /\
   smc_sec2_rel
   {|smc_sec2_st_func = MI.func{1}; smc_sec2_st_smcrs = SMCReal.st{1};
     smc_sec2_st_fws = Fwd.Forw.st{1}; smc_sec2_st_keis = KeyEx.KEIdeal.st{1};
     smc_sec2_st_smcis = SMCIdeal.st{2}; smc_sec2_st_smcss = SMCSim.st{2}|} ==>
   ={res, MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} (fset1 adv_fw_pi) /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   Fwd.Forw.self{1} = MI.func{1} ++ [1] /\
   Fwd.Forw.adv{1} = MI.adv{1} /\
   KeyEx.KEIdeal.self{1} = MI.func{1} ++ [2] /\
   KeyEx.KEIdeal.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   ={glob Adv} /\
   smc_sec2_rel
   {|smc_sec2_st_func = MI.func{1}; smc_sec2_st_smcrs = SMCReal.st{1};
     smc_sec2_st_fws = Fwd.Forw.st{1}; smc_sec2_st_keis = KeyEx.KEIdeal.st{1};
     smc_sec2_st_smcis = SMCIdeal.st{2}; smc_sec2_st_smcss = SMCSim.st{2}|}].
proof.
proc*.
case
  (smc_sec2_rel0
   {|smc_sec2_st_func = MI.func{1}; smc_sec2_st_smcrs = SMCReal.st{1};
     smc_sec2_st_fws = Fwd.Forw.st{1}; smc_sec2_st_keis = KeyEx.KEIdeal.st{1};
     smc_sec2_st_smcis = SMCIdeal.st{2}; smc_sec2_st_smcss = SMCSim.st{2};|}).
call MI_SMCReal_KEIdeal_Adv_SMCIdeal_SMCSim_Adv_invoke_0.
auto.
case
  (exists (pt1 pt2 : port, x : bits, q : exp),
   smc_sec2_rel1
   {|smc_sec2_st_func = MI.func{1}; smc_sec2_st_smcrs = SMCReal.st{1};
     smc_sec2_st_fws = Fwd.Forw.st{1}; smc_sec2_st_keis = KeyEx.KEIdeal.st{1};
     smc_sec2_st_smcis = SMCIdeal.st{2}; smc_sec2_st_smcss = SMCSim.st{2};|}
   pt1 pt2 x q).
call MI_SMCReal_KEIdeal_Adv_SMCIdeal_SMCSim_Adv_invoke_1.
auto; progress.
by exists pt1 pt2 x q.
by apply smc_sec2_rel_1_4_imp_full.
case
  (exists (pt1 pt2 : port, x : bits, q : exp),
   smc_sec2_rel2
   {|smc_sec2_st_func = MI.func{1}; smc_sec2_st_smcrs = SMCReal.st{1};
     smc_sec2_st_fws = Fwd.Forw.st{1}; smc_sec2_st_keis = KeyEx.KEIdeal.st{1};
     smc_sec2_st_smcis = SMCIdeal.st{2}; smc_sec2_st_smcss = SMCSim.st{2};|}
   pt1 pt2 x q).
call MI_SMCReal_KEIdeal_Adv_SMCIdeal_SMCSim_Adv_invoke_2.
auto; progress.
by exists pt1 pt2 x q.
by apply smc_sec2_rel_2_4_imp_full.
case
  (exists (pt1 pt2 : port, x : bits, q : exp),
   smc_sec2_rel3
   {|smc_sec2_st_func = MI.func{1}; smc_sec2_st_smcrs = SMCReal.st{1};
     smc_sec2_st_fws = Fwd.Forw.st{1}; smc_sec2_st_keis = KeyEx.KEIdeal.st{1};
     smc_sec2_st_smcis = SMCIdeal.st{2}; smc_sec2_st_smcss = SMCSim.st{2};|}
   pt1 pt2 x q).
call MI_SMCReal_KEIdeal_Adv_SMCIdeal_SMCSim_Adv_invoke_3.
auto; progress.
by exists pt1 pt2 x q.
by apply smc_sec2_rel_3_4_imp_full.
case
  (exists (pt1 pt2 : port, x : bits, q : exp),
   smc_sec2_rel4
   {|smc_sec2_st_func = MI.func{1}; smc_sec2_st_smcrs = SMCReal.st{1};
     smc_sec2_st_fws = Fwd.Forw.st{1}; smc_sec2_st_keis = KeyEx.KEIdeal.st{1};
     smc_sec2_st_smcis = SMCIdeal.st{2}; smc_sec2_st_smcss = SMCSim.st{2};|}
   pt1 pt2 x q).
call MI_SMCReal_KEIdeal_Adv_SMCIdeal_SMCSim_Adv_invoke_4.
auto; progress.
by exists pt1 pt2 x q.
by apply smc_sec2_rel_4_imp_full.
exfalso => &1 &2 [# _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
case => //.
move => pt1 pt2 x q true1 _ false1.
have true1_ex // : 
  exists (pt1 pt2 : port, x : bits, q : exp),
  smc_sec2_rel1
   {|smc_sec2_st_func = MI.func{1}; smc_sec2_st_smcrs = SMCReal.st{1};
     smc_sec2_st_fws = Fwd.Forw.st{1}; smc_sec2_st_keis = KeyEx.KEIdeal.st{1};
     smc_sec2_st_smcis = SMCIdeal.st{2}; smc_sec2_st_smcss = SMCSim.st{2};|}
  pt1 pt2 x q.
  by exists pt1 pt2 x q.
move => pt1 pt2 x q true2 _ _.
have true2_ex // : 
  exists (pt1 pt2 : port, x : bits, q : exp),
  smc_sec2_rel2
   {|smc_sec2_st_func = MI.func{1}; smc_sec2_st_smcrs = SMCReal.st{1};
     smc_sec2_st_fws = Fwd.Forw.st{1}; smc_sec2_st_keis = KeyEx.KEIdeal.st{1};
     smc_sec2_st_smcis = SMCIdeal.st{2}; smc_sec2_st_smcss = SMCSim.st{2};|}
  pt1 pt2 x q.
  by exists pt1 pt2 x q.
move => pt1 pt2 x q true3 _ _ _.
have true3_ex // : 
  exists (pt1 pt2 : port, x : bits, q : exp),
  smc_sec2_rel3
   {|smc_sec2_st_func = MI.func{1}; smc_sec2_st_smcrs = SMCReal.st{1};
     smc_sec2_st_fws = Fwd.Forw.st{1}; smc_sec2_st_keis = KeyEx.KEIdeal.st{1};
     smc_sec2_st_smcis = SMCIdeal.st{2}; smc_sec2_st_smcss = SMCSim.st{2};|}
  pt1 pt2 x q.
  by exists pt1 pt2 x q.
move => pt1 pt2 x q true4 _ _ _.
have true4_ex // : 
  exists (pt1 pt2 : port, x : bits, q : exp),
  smc_sec2_rel4
   {|smc_sec2_st_func = MI.func{1}; smc_sec2_st_smcrs = SMCReal.st{1};
     smc_sec2_st_fws = Fwd.Forw.st{1}; smc_sec2_st_keis = KeyEx.KEIdeal.st{1};
     smc_sec2_st_smcis = SMCIdeal.st{2}; smc_sec2_st_smcss = SMCSim.st{2};|}
  pt1 pt2 x q.
  by exists pt1 pt2 x q.
qed.

lemma smc_sec2 (func adv : addr) &m :
  exper_pre func adv (fset1 adv_fw_pi) =>
  Pr[Exper(MI(SMCReal(KeyEx.KEIdeal), Adv), Env).main
       (func, adv, fset1 adv_fw_pi) @ &m : res] =
  Pr[Exper(MI(SMCIdeal, SMCSim(Adv)), Env).main
       (func, adv, fset1 adv_fw_pi) @ &m : res].
proof.
move => pre; byequiv => //; proc.
seq 1 1 :
  (={func, adv, in_guard, MI.func, MI.adv, MI.in_guard} /\
   exper_pre func{1} adv{1} (fset1 adv_fw_pi) /\
   MI.func{1} = func{1} /\ MI.adv{1} = adv{1} /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   SMCReal.self{1} = func{1} /\ SMCReal.adv{1} = adv{1} /\
   SMCReal.st{1} = SMCRealStateWaitReq /\
   Fwd.Forw.self{1} = func{1} ++ [1] /\ Fwd.Forw.adv{1} = adv{1} /\
   Fwd.Forw.st{1} = Fwd.FwStateInit /\
   KeyEx.KEIdeal.self{1} = func{1} ++ [2] /\ KeyEx.KEIdeal.adv{1} = adv{1} /\
   KeyEx.KEIdeal.st{1} = KeyEx.KEIdealStateWaitReq1 /\
   SMCIdeal.self{2} = func{1} /\ SMCIdeal.adv{2} = adv{1} /\
   SMCIdeal.st{2} = SMCIdealStateWaitReq /\
   SMCSim.self{2} = adv{1} /\ SMCSim.adv{2} = [] /\
   SMCSim.st{2} = SMCSimStateWaitReq /\
   ={glob Adv}).
inline*.
swap{2} 16 1; call (_ : true).
auto.
auto.
call
  (_ : 
   ={func, adv, in_guard, MI.func, MI.adv, MI.in_guard} /\
   exper_pre func{1} adv{1} (fset1 adv_fw_pi) /\
   MI.func{1} = func{1} /\ MI.adv{1} = adv{1} /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   SMCReal.self{1} = func{1} /\ SMCReal.adv{1} = adv{1} /\
   Fwd.Forw.self{1} = func{1} ++ [1] /\ Fwd.Forw.adv{1} = adv{1} /\
   KeyEx.KEIdeal.self{1} = func{1} ++ [2] /\ KeyEx.KEIdeal.adv{1} = adv{1} /\
   SMCIdeal.self{2} = func{1} /\ SMCIdeal.adv{2} = adv{1} /\
   SMCSim.self{2} = adv{1} /\ SMCSim.adv{2} = [] /\
   ={glob Adv} /\
   smc_sec2_rel
   {|smc_sec2_st_func = func{1}; smc_sec2_st_smcrs = SMCReal.st{1};
     smc_sec2_st_fws = Fwd.Forw.st{1}; smc_sec2_st_keis = KeyEx.KEIdeal.st{1};
     smc_sec2_st_smcis = SMCIdeal.st{2}; smc_sec2_st_smcss = SMCSim.st{2}|} ==>
   ={res}).
proc
  (={MI.func, MI.adv, MI.in_guard} /\
   exper_pre func{1} adv{1} (fset1 adv_fw_pi) /\
   MI.func{1} = func{1} /\ MI.adv{1} = adv{1} /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   SMCReal.self{1} = func{1} /\ SMCReal.adv{1} = adv{1} /\
   Fwd.Forw.self{1} = func{1} ++ [1] /\ Fwd.Forw.adv{1} = adv{1} /\
   KeyEx.KEIdeal.self{1} = func{1} ++ [2] /\ KeyEx.KEIdeal.adv{1} = adv{1} /\
   SMCIdeal.self{2} = func{1} /\ SMCIdeal.adv{2} = adv{1} /\
   SMCSim.self{2} = adv{1} /\ SMCSim.adv{2} = [] /\
   ={glob Adv} /\
   smc_sec2_rel
   {|smc_sec2_st_func = func{1}; smc_sec2_st_smcrs = SMCReal.st{1};
     smc_sec2_st_fws = Fwd.Forw.st{1}; smc_sec2_st_keis = KeyEx.KEIdeal.st{1};
     smc_sec2_st_smcis = SMCIdeal.st{2}; smc_sec2_st_smcss = SMCSim.st{2}|}) => //.
by conseq MI_SMCReal_KEIdeal_Adv_SMCIdeal_SMCSim_Adv_invoke.
auto; progress; by apply SMCSec2Rel0.
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