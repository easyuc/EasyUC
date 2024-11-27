(* SMC.ec *)

(* Secure Message Communication *)

prover quorum=2 ["Alt-Ergo" "Z3"].

require import AllCore List FSet SmtMap Distr ListAux ListPO.
require import UCCoreDiffieHellman FSetAux.
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
           (is_univ_pair (UnivPort pt2, UnivBase (BaseText t))).
qed.

lemma dec_enc_smc_req (m : msg, func : addr, pt1 pt2 : port, t : text) :
  dec_smc_req m = Some (func, pt1, pt2, t) =>
  smc_req func pt1 pt2 t = m.
proof.
case m => mod pt1' pt2' u'.
rewrite /dec_smc_req /smc_req /=.
case (mod = Adv \/ pt1'.`2 <> 1 \/ ! is_univ_pair u') => //.
rewrite !negb_or /= not_adv.
move => [#] -> pt1'_2 iup_u'.
have [] p : exists (p : univ * univ), dec_univ_pair u' = Some p.
  exists (oget (dec_univ_pair u')); by rewrite -some_oget.
case p => v1 v2 /dec_enc_univ_pair -> /=.
case (! is_univ_port v1 \/ ! is_univ_base v2) => //.
rewrite !negb_or /=.
move => [#] iupt_v1 iubse_v2.
have [] pt2'' : exists (pt2'' : port), dec_univ_port v1 = Some pt2''.
  exists (oget (dec_univ_port v1)); by rewrite -some_oget.
move => /dec_enc_univ_port -> /=.
have [] bse : exists (bse : base), dec_univ_base v2 = Some bse.
  exists (oget (dec_univ_base v2)); by rewrite -some_oget.
move => /dec_enc_univ_base -> /=.
case (! is_base_text bse) => //= ibt_bse.
have [] t' : exists (t' : text), dec_base_text bse = Some t'.
  exists (oget (dec_base_text bse)); by rewrite -some_oget.
move => /dec_enc_base_text -> /=.
smt().
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
           (is_univ_pair (UnivPort pt1, UnivBase (BaseText t))).
qed.

lemma dec_enc_smc_rsp (m : msg, func : addr, pt1 pt2 : port, t : text) :
  dec_smc_rsp m = Some (func, pt1, pt2, t) =>
  smc_rsp func pt1 pt2 t = m.
proof.
case m => mod pt1' pt2' u'.
rewrite /dec_smc_rsp /smc_rsp /=.
case (mod = Adv \/ pt2'.`2 <> 2 \/ ! is_univ_pair u') => //.
rewrite !negb_or /= not_adv.
move => [#] -> pt2'_2 iup_u'.
have [] p : exists (p : univ * univ), dec_univ_pair u' = Some p.
  exists (oget (dec_univ_pair u')); by rewrite -some_oget.
case p => v1 v2 /dec_enc_univ_pair -> /=.
case (! is_univ_port v1 \/ ! is_univ_base v2) => //.
rewrite !negb_or /=.
move => [#] iupt_v1 iupt_v2.
have [] pt1'' : exists (pt1'' : port), dec_univ_port v1 = Some pt1''.
  exists (oget (dec_univ_port v1)); by rewrite -some_oget.
move => /dec_enc_univ_port -> /=.
have [] bse : exists (bse : base), dec_univ_base v2 = Some bse.
  exists (oget (dec_univ_base v2)); by rewrite -some_oget.
move => /dec_enc_univ_base -> /=.
case (! is_base_text bse) => //= ibsetxt_bse.
have [] t' : exists (t' : text), dec_base_text bse = Some t'.
  exists (oget (dec_base_text bse)); by rewrite -some_oget.
move => /dec_enc_base_text -> /= /#.
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

         not_done =>
         m.`1 = Dir /\ m.`2.`1 = self /\
         (m.`2.`2 = 1 \/ m.`2.`2 = 2 \/ m.`2.`2 = 3 \/ m.`2.`2 = 4) \/
         self ++ [1] <= m.`2.`1 \/
         self ++ [2] <= m.`2.`1

       to facilitate proofs of composition bridging lemmas, calls to
       party1, party2, Fwd.Forw.invoke and KE.invoke are explicitly
       guarded, in particular making clear that invariant holds *)

    while (not_done) {
      if (m.`2.`1 = self /\ (m.`2.`2 = 1 \/ m.`2.`2 = 3)) {
        r <@ party1(m);
        if (r <> None /\
            let (mod, pt1, pt2, u) = oget r in
            let (addr1, n1) = pt1
            in !(mod = Dir /\ (self ++ [2] <= addr1 \/ self ++ [1] <= addr1))) {
          r <- None;
        }
      }
      elif (m.`2.`1 = self /\ (m.`2.`2 = 2 \/ m.`2.`2 = 4)) {
        r <@ party2(m);
        if (r <> None /\
            let (mod, pt1, pt2, u) = oget r in
            let (addr1, n1) = pt1
            in !(mod = Dir /\ (self ++ [2] <= addr1 \/ ! self <= addr1))) {
          r <- None;
        }
      }
      elif (self ++ [1] <= m.`2.`1) {
        r <@ Fwd.Forw.invoke(m);
        if (r <> None /\
            let (mod, pt1, pt2, u) = oget r in
            let (addr1, n1) = pt1
            in !(mod = Dir /\ addr1 = self /\ n1 = 4) /\
               !(mod = Adv /\ ! self <= addr1 /\ n1 = adv_fw_pi)) {
          r <- None;
        }
      }
      else {  (* self ++ [2] <= m.`2.`1 *)
        r <@ KE.invoke(m);
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
      r <@ loop(m);
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

lemma dec_enc_smc_sim_req (m : msg, ideal adv : addr, pt1 pt2 : port) :
  dec_smc_sim_req m = Some (ideal, adv, pt1, pt2) =>
  smc_sim_req ideal adv pt1 pt2 = m.
proof.
case m => mod pt1' pt2' u'.
rewrite /dec_smc_sim_req /smc_sim_req /=.
case (mod = Dir \/ pt1'.`2 <> smc_sim_adv_pi \/
      pt2'.`2 <> 3 \/ ! is_univ_pair u') => //.
rewrite !negb_or /= not_dir.
move => [#] -> pt1'_2 pt2'_2 iup_u'.
have [] p : exists (p : univ * univ), dec_univ_pair u' = Some p.
  exists (oget (dec_univ_pair u')); by rewrite -some_oget.
case p => v1 v2 /dec_enc_univ_pair -> /=.
case (! is_univ_port v1 \/ ! is_univ_port v2) => //.
rewrite !negb_or /= => [#] iupt_v1 iupt_v2.
have [] pt1'' : exists (pt1'' : port), dec_univ_port v1 = Some pt1''.
  exists (oget (dec_univ_port v1)); by rewrite -some_oget.
move => /dec_enc_univ_port ->.
have [] pt2'' : exists (pt2'' : port), dec_univ_port v2 = Some pt2''.
  exists (oget (dec_univ_port v2)); by rewrite -some_oget.
move => /dec_enc_univ_port -> /=.
smt().
qed.

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

lemma dec_enc_smc_sim_rsp (m : msg, ideal adv : addr) :
  dec_smc_sim_rsp m = Some (ideal, adv) =>
  smc_sim_rsp ideal adv = m.
proof.
case m => mod pt1' pt2' u'.
rewrite /dec_smc_sim_rsp /smc_sim_rsp /=.
case (mod = Dir \/ pt1'.`2 <> 3 \/
      pt2'.`2 <> smc_sim_adv_pi \/ u' <> UnivUnit) => //.
rewrite !negb_or /= not_dir.
move => [#] -> pt1'_2 pt2'_2 -> /#.
qed.

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
    else {  (* is_smc_ideal_state_final st *)
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
      r <@ parties(m);
    }
    return r;
  }
}.

(* Simulator *)

type smc_sim_state = [
    SMCSimStateWaitReq
  | SMCSimStateWaitAdv1 of (port * port * addr)
  | SMCSimStateWaitAdv2 of (port * port * addr * exp)
  | SMCSimStateWaitAdv3 of (port * port * addr * exp)
  | SMCSimStateFinal    of (port * port * addr * exp)
].

op dec_smc_sim_state_wait_adv1 (st : smc_sim_state) :
     (port * port * addr) option =
     with st = SMCSimStateWaitReq    => None
     with st = SMCSimStateWaitAdv1 x => Some x
     with st = SMCSimStateWaitAdv2 _ => None
     with st = SMCSimStateWaitAdv3 _ => None
     with st = SMCSimStateFinal _    => None.

lemma enc_dec_smc_sim_state_wait_adv1 (x : port * port * addr) :
  dec_smc_sim_state_wait_adv1 (SMCSimStateWaitAdv1 x) = Some x.
proof. done. qed.

op is_smc_sim_state_wait_adv1 (st : smc_sim_state) : bool =
  dec_smc_sim_state_wait_adv1 st <> None.

lemma is_smc_sim_state_wait_adv1 (x : port * port * addr) :
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
    var addr, addr1, addr2 : addr; var n1 : int; var q : exp;
    var r : msg option <- None;
    var not_done : bool <- true;
    while (not_done) {
      (* mod = Adv /\ pt1.`1 = self *)
      (mod, pt1, pt2, u) <- m;
      if (pt1.`2 = smc_sim_adv_pi) {  (* simulator *)
        r <- None; not_done <- false;
        if (st = SMCSimStateWaitReq) {
          if (is_smc_sim_req m) {
            (addr1, addr2, pt1, pt2) <- oget (dec_smc_sim_req m);
            m <-
              KeyEx.ke_sim_req1 (addr1 ++ [2]) self
              (addr1, 3) (addr1, 4);
            not_done <- true;
            st <- SMCSimStateWaitAdv1 (pt1, pt2, addr1);
          }
        }
      }
      else {  (* adversary *)
        r <@ Adv.invoke(m);
        if (r = None) {
          not_done <- false;
        }
        else {
          m <- oget r; (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
          if (mod = Dir \/ self <= addr1) {
            r <- None; not_done <- false;
          }
          elif (is_smc_sim_state_wait_adv1 st) {
            (pt1, pt2, addr) <- oget (dec_smc_sim_state_wait_adv1 st);
            not_done <- false;
            if (addr <= addr1) {
              r <- None;
              if (KeyEx.is_ke_sim_rsp m) {
                (addr1, addr2) <- oget (KeyEx.dec_ke_sim_rsp m);
                if (addr1 = addr ++ [2]) {
                  q <$ dexp;
                  m <- KeyEx.ke_sim_req2 (addr ++ [2]) self;
                  not_done <- true;
                  st <- SMCSimStateWaitAdv2 (pt1, pt2, addr, q);
                }
              }
            }
          }
          elif (is_smc_sim_state_wait_adv2 st) {
            (pt1, pt2, addr, q) <- oget (dec_smc_sim_state_wait_adv2 st);
            not_done <- false;
            if (addr <= addr1) {
              r <- None;
              if (KeyEx.is_ke_sim_rsp m) {
                (addr1, addr2) <- oget (KeyEx.dec_ke_sim_rsp m);
                if (addr1 = addr ++ [2]) {
                  m <-
                    Fwd.fw_obs (addr ++ [1]) self (addr, 3) (addr, 4)
                    (univ_triple (UnivPort pt1) (UnivPort pt2)
                     (UnivBase (BaseKey (g ^ q))));
                  not_done <- true;
                  st <- SMCSimStateWaitAdv3 (pt1, pt2, addr, q);
                }
              }
            }
          }
          elif (is_smc_sim_state_wait_adv3 st) {
            (pt1, pt2, addr, q) <- oget (dec_smc_sim_state_wait_adv3 st);
            not_done <- false;
            if (addr <= addr1) {
              r <- None;
              if (Fwd.is_fw_ok m) {
                (addr1, addr2) <- oget (Fwd.dec_fw_ok m);
                if (addr1 = addr ++ [1]) {
                  r <- Some (smc_sim_rsp addr self);
                  (* not_done = false *)
                  st <- SMCSimStateFinal (pt1, pt2, addr, q);
                }
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
        r <@ loop(m);
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
      r <@ parties(m);
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
if; first smt().
rcondf{1} 4; first auto.
move => /> &hr <-; smt(le_refl).
rcondf{1} 4; first auto.
move => /> &1 &2.
rewrite /KeyEx.ke_req1 /=; smt(le_ext_r).
rcondt{1} 5; first auto.
rcondf{1} 5; first auto.
move => /> &hr <-.
rewrite /KeyEx.ke_req1 /=; smt(ne_cat_nonnil_r).
rcondf{1} 5; first auto.
rcondf{1} 5; first auto.
move => /> &hr.
by rewrite /KeyEx.ke_req1 /= le_ext_comm.
inline{1} (1) KeyEx.KEIdeal.invoke.
rcondt{1} 9; first auto.
inline{1} (1) KeyEx.KEIdeal.parties.
rcondt{1} 11; first auto; smt().
rcondt{1} 11; first auto.
rcondt{1} 12; first auto.
move => /> &hr <-.
rewrite KeyEx.enc_dec_ke_req1 /=.
progress.
by rewrite not_le_ext_nonnil_l.
by rewrite not_le_ext_nonnil_l.
by rewrite inc_nle_r.
by rewrite inc_nle_r.
rcondf{1} 16; first auto; progress.
by rewrite inc_nle_l.
rcondt{1} 16; first auto.
move => /> &hr.
rewrite KeyEx.enc_dec_ke_req1 /= /ke_sim_req1 /=.
progress; by rewrite inc_nle_l.
rcondf{1} 17; first auto.
auto => |> &1 &2.
rewrite KeyEx.enc_dec_ke_req1 /=.
move => <- [#] _ -> -> ->.
progress; rewrite (SMCRealKEIdealSimpRel1 _ pt10{2} pt20{2} t{2}) /#.
rcondf{1} 2; first auto.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto.
rcondf{1} 2; first auto.
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
rcondf{1} 4; first auto.
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
rcondf{1} 3; first auto.
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
auto.
rcondf{1} 2; first auto.
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
by elim dec_ke_ideal_wait_sim1 => -> ->.
rcondf{1} 6; first auto.
move => |> &hr _ dec_ke_ideal_wait_sim1 _ _ _ [] /= _ [#] _
        _ _ _ ->> _ _ _ q _.
rewrite /= in dec_ke_ideal_wait_sim1.
elim dec_ke_ideal_wait_sim1 => -> -> /=.
rewrite le_refl.
rcondt{1} 7; first auto.
rcondf{1} 7; first auto.
move => |> &hr _ dec_ke_ideal_wait_sim1 _ _ _ [] /= _ [#] _
        _ _ _ ->> _ _ _ q _.
by elim dec_ke_ideal_wait_sim1 => -> ->.
rcondt{1} 7; first auto.
move => |> &hr _ dec_ke_ideal_wait_sim1 _ _ _ [] /= _ [#] _
        _ _ _ ->> _ _ _ q _.
by elim dec_ke_ideal_wait_sim1 => -> ->.
inline{1} (1) SMCReal(KeyEx.KEIdeal).party2.
rcondt{1} 9; first auto; smt().
rcondt{1} 9; first auto.
move => |> &hr _ dec_ke_ideal_wait_sim1 _ _ _ [] /= _ [#] _
        _ _ _ ->> _ _ _ q _.
elim dec_ke_ideal_wait_sim1 => -> ->.
rewrite KeyEx.is_ke_rsp1.
rcondt{1} 10; first auto.
move => |> &hr _ dec_ke_ideal_wait_sim1 _ _ _ [] /= _ [#] _
        _ _ _ ->> _ _ _ q _.
elim dec_ke_ideal_wait_sim1 => -> ->.
by rewrite KeyEx.enc_dec_ke_rsp1.
rcondf{1} 13; first auto.
move => /> &hr; smt(le_refl).
rcondf{1} 13; first auto; progress.
by rewrite /KeyEx.ke_req2 /= le_ext_r.
rcondt{1} 14; first auto.
rcondf{1} 14; first auto.
rcondf{1} 14; first auto.
move => |> &hr.
rewrite /KeyEx.ke_req2 /=.
smt(ne_cat_nonnil_r).
rcondf{1} 14; first auto.
progress.
rewrite /KeyEx.ke_req2 /=.
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
elim dec_ke_ideal_wait_sim1.
by rewrite KeyEx.enc_dec_ke_req2.
rcondf{1} 26; first auto; progress; smt(inc_le1_not_lr).
rcondt{1} 26; first auto; progress.
rewrite /KeyEx.ke_sim_req2 /=.
smt(inc_le1_not_lr).
rcondf{1} 27; first auto.
auto => |> &1 &2 _ dec_ke_ideal_wait_sim1 _ _ _ [] /= _ [#] _
        _ _ _ ->> _ _ _ q _.
elim dec_ke_ideal_wait_sim1 => -> ->.
rewrite /= KeyEx.enc_dec_ke_rsp1 /=.
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
rcondf{1} 3; first auto; smt(Fwd.not_is_fw_req_suff).
rcondf{1} 4; first auto.
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
rcondf{1} 3; first auto.
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
auto.
rcondf{1} 2; first auto.
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
by elim dec_ke_ideal_wait_sim2.
rcondf{1} 5; first auto.
move => |> &hr _ dec_ke_ideal_wait_sim2 _ _ _ _ [] /= _ [#] _
        _ _ _ ->>.
elim dec_ke_ideal_wait_sim2 => -> _ /= _.
move => _ _ _.
rewrite le_refl.
rcondt{1} 6; first auto.
rcondt{1} 6; first auto.
move => |> &hr _ dec_ke_ideal_wait_sim2 _ _ _ _ [] /= _ [#] _
        _ _ _ ->>.
by elim dec_ke_ideal_wait_sim2 => -> _.
inline{1} (1) SMCReal(KeyEx.KEIdeal).party1.
rcondf{1} 8; first auto; smt().
rcondt{1} 8; first auto; smt(is_smc_real_p1_state_wait_ke2).
rcondt{1} 9; first auto.
move => |> &hr _ dec_ke_ideal_wait_sim2 _ _ _ _ [] /= _ [#] _
        _ _ _ ->>.
elim dec_ke_ideal_wait_sim2 => -> _ /= _.
by rewrite KeyEx.is_ke_rsp2.
rcondt{1} 10; first auto.
move => |> &hr _ dec_ke_ideal_wait_sim2 _ _ _ _ [] /= _ [#] _
        _ _ _ ->>.
elim dec_ke_ideal_wait_sim2 => -> _ /= _.
by rewrite KeyEx.enc_dec_ke_rsp2.
rcondf{1} 13; first auto.
move => /> &hr; smt(le_refl).
rcondf{1} 13; first auto; progress.
rewrite /Fwd.fw_req /= le_ext_r.
rcondt{1} 14; first auto.
rcondf{1} 14; first auto.
move => |> &hr.
rewrite /Fwd.fw_req /=.
smt(ne_cat_nonnil_r).
rcondf{1} 14; first auto.
rcondt{1} 14; first auto.
move => |> &hr _ dec_ke_ideal_wait_sim2 _ _ _ _ [] /= _ [#] _
        _ _ _ ->> _ _ _.
elim dec_ke_ideal_wait_sim2 => -> _ /= _.
rewrite /Fwd.fw_req /= le_refl.
inline Fwd.Forw.invoke.
rcondt{1} 16; first auto; smt().
rcondt{1} 16; first auto.
rcondt{1} 17; first auto.
move => |> &hr _ dec_ke_ideal_wait_sim2 _ _ _ _ [] /= _ [#] _
        _ _ _ ->> _ _ _.
elim dec_ke_ideal_wait_sim2 => -> _ /= _.
rewrite Fwd.enc_dec_fw_req /=.
smt(not_le_ext_nonnil_l inc_nle_r).
rcondf{1} 20; first auto.
move => /> &hr; smt(incP).
rcondt{1} 20; first auto.
move => |> &hr _ dec_ke_ideal_wait_sim2 _ _ _ _ [] /= _ [#] _
        _ _ _ ->> _ _ _.
elim dec_ke_ideal_wait_sim2 => -> _ /= _.
by rewrite Fwd.enc_dec_fw_req /Fwd.fw_obs
           /= inc_nle_l.
rcondf{1} 21; first auto.
auto => |> &1 &2 dec_smc_real_ke_ideal_simp_wait_adv2
        dec_ke_ideal_wait_sim2 _ _ _ _ [] /= _
        [#] _ -> _ _ ->> ->> _ _.
elim dec_ke_ideal_wait_sim2 => -> -> -> /=.
elim dec_smc_real_ke_ideal_simp_wait_adv2 => -> [#] -> -> ->.
rewrite Fwd.enc_dec_fw_req /Fwd.fw_obs /= KeyEx.enc_dec_ke_rsp2 /=.
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
rcondf{1} 3; first auto; smt(Fwd.not_is_fw_req_suff).
rcondf{1} 4; first auto.
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
case
  (exists pt1' pt2' t' q',
   smc_real_ke_ideal_simp_rel3
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
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_smc_real_ke_ideal_simp_state_wait_adv3).
rcondf{2} 2; first auto.
if{1}.
inline{1} (1) SMCReal(KeyEx.KEIdeal).party1.
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondf{1} 4; first auto.
rcondt{1} 4; first auto.
rcondf{1} 5; first auto.
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
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_smc_real_ke_ideal_simp_state_wait_adv3).
case (addr1{1} = SMCReal.self{1} ++ [1] /\ n1{1} = 1).
rcondt{1} 1; first auto; smt(le_refl).
inline{1} (1) Fwd.Forw.invoke.
rcondf{1} 3; first auto; smt().
rcondt{1} 3; first auto; smt(Fwd.is_fw_state_wait).
sp 3 1.
if => //.
rcondt{1} 2; first auto; smt(Fwd.dest_good_fw_ok).
rcondt{2} 2; first auto; smt(Fwd.dest_good_fw_ok).
rcondf{1} 5; first auto.
move => /> &hr //.
rcondf{1} 5; first auto.
move => |> &hr dec_smc_real_ke_ideal_simp_wait_adv3_eq dec_fw_wait_eq
        _ _ _ _ _ [] /= _ [#] _ _ _ ->> _ ->>.
elim dec_fw_wait_eq => -> [#] -> _ /=.
smt(le_refl).
rcondt{1} 6; first auto.
rcondf{1} 6; first auto.
move => |> &hr dec_smc_real_ke_ideal_simp_wait_adv3_eq dec_fw_wait_eq
        _ _ _ _ _ [] /= _ [#] _ _ _ ->> _ ->>.
by elim dec_fw_wait_eq.
rcondt{1} 6; first auto.
move => |> &hr dec_smc_real_ke_ideal_simp_wait_adv3_eq dec_fw_wait_eq
        _ _ _ _ _ [] /= _ [#] _ _ _ ->> _ ->>.
by elim dec_fw_wait_eq.
inline SMCReal(KeyEx.KEIdeal).party2.
rcondf{1} 8; first auto; smt().
rcondt{1} 8; first auto; smt(is_smc_real_p2_state_wait_fwd).
rcondt{1} 9; first auto; smt().
rcondt{1} 10; first auto.
move => |> &hr dec_smc_real_ke_ideal_simp_wait_adv3_eq dec_fw_wait_eq
        _ _ _ _ _ [] /= _ [#] _ _ _ ->> _ ->>.
elim dec_fw_wait_eq => -> [#] -> _ /=.
by rewrite Fwd.enc_dec_fw_rsp.
rcondf{1} 17; first auto.
move => |> &hr _ dec_fw_wait_eq _ _ _ _ _ [] /= _ [#] pt2'_out _ _ ->> _ ->>.
elim dec_fw_wait_eq => -> [#] -> -> /=.
rewrite !Fwd.enc_dec_fw_rsp /= !enc_dec_univ_triple /= /smc_rsp /=.
smt(not_le_ext).
rcondt{1} 17; first auto.
move => |> &hr dec_smc_real_ke_ideal_simp_wait_adv3_eq dec_fw_wait_eq
        _ _ _ _ _ [] /= _ [#] pt2'_out _ _ ->> _ ->>.
elim dec_fw_wait_eq => -> [#] -> -> /=.
by rewrite !Fwd.enc_dec_fw_rsp /= !enc_dec_univ_triple /=.
rcondf{1} 18; first auto.
auto.
move => |> &1 &2 dec_smc_real_ke_ideal_simp_wait_adv3_eq dec_fw_wait_eq
        _ _ _ _ _ [] /= _ [#] pt2'_out -> -> ->> _ ->> _ _ _.
elim dec_fw_wait_eq => -> [#] -> -> /=.
elim dec_smc_real_ke_ideal_simp_wait_adv3_eq => -> [#] -> -> ->.
rewrite /= !Fwd.enc_dec_fw_rsp /= !enc_dec_univ_triple /=
        kmulA kinv_r kid_r proj_injK /=.
by rewrite (SMCRealKEIdealSimpRel4 _ pt1' pt2' t' q').
rcondf{1} 2; first auto.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto.
seq 0 3 :
  (smc_real_ke_ideal_simp_rel3
   {|smc_real_ke_ideal_simp_rel_st_func = func;
     smc_real_ke_ideal_simp_rel_st_r1s = SMCReal.st1{1};
     smc_real_ke_ideal_simp_rel_st_r2s = SMCReal.st2{1};
     smc_real_ke_ideal_simp_rel_st_fws = Fwd.Forw.st{1};
     smc_real_ke_ideal_simp_rel_st_keis = KeyEx.KEIdeal.st{1};
     smc_real_ke_ideal_simp_rel_st_riss = SMCRealKEIdealSimp.st{2};|}
     pt1' pt2' t' q' /\
   SMCReal.self{1} ++ [1] = Fwd.Forw.self{1} /\
   (mod{1} = Dir /\ addr1{1} = SMCReal.self{1} /\ n1{1} = 1 \/
    mod{1} = Adv /\
    (SMCReal.self{1} ++ [1] <= addr1{1} \/
     SMCReal.self{1} ++ [2] <= addr1{1})) /\
   ! (mod{1} = Dir /\ addr1{1} = SMCReal.self{1} /\ n1{1} = 1) /\
   ! (addr1{1} = SMCReal.self{1} ++ [1] /\ n1{1} = 1) /\
   r{2} = None /\
   m0{1} = (mod{1}, pt1{1}, pt2{1}, u{1}) /\
   (addr1{1}, n1{1}) = pt1{1}).
sp 0 1.
if{2}.
rcondf{2} 2; first auto; smt(Fwd.dest_good_fw_ok).
auto.
auto.
if{1}.
inline{1} (1) Fwd.Forw.invoke.
rcondf{1} 3; first auto; smt().
rcondt{1} 3; first auto; smt(Fwd.is_fw_state_wait).
sp 3 0.
if{1}.
rcondf{1} 2; first auto; smt(Fwd.dest_good_fw_ok).
rcondf{1} 3; first auto.
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
auto; progress; by rewrite (SMCRealKEIdealSimpRel3 _ pt1' pt2' t' q').
rcondf{1} 2; first auto.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto; progress; by rewrite (SMCRealKEIdealSimpRel3 _ pt1' pt2' t' q').
inline{1} (1) KeyEx.KEIdeal.invoke.
sp 4 0.
if{1}.
inline{1} (1) KeyEx.KEIdeal.parties.
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt(KeyEx.is_ke_ideal_state_wait_sim1).
rcondf{1} 3; first auto; smt(KeyEx.is_ke_ideal_state_wait_req2).
rcondf{1} 3; first auto; smt(KeyEx.is_ke_ideal_state_wait_sim2).
rcondf{1} 5; first auto.
rcondt{1} 5; first auto.
rcondf{1} 6; first auto.
auto; progress; by rewrite (SMCRealKEIdealSimpRel3 _ pt1' pt2' t' q').
rcondf{1} 2; first auto.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto; progress; by rewrite (SMCRealKEIdealSimpRel3 _ pt1' pt2' t' q').
case
  (exists pt1' pt2' t' q',
   smc_real_ke_ideal_simp_rel4
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
rcondf{2} 3; first auto; smt().
rcondf{2} 3; first auto; smt().
rcondf{2} 3; first auto; smt().
rcondf{2} 3; first auto; smt().
rcondt{1} 4; first auto.
wp; sp.
if{1}.
inline{1} (1) SMCReal(KeyEx.KEIdeal).party1.
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondf{1} 4; first auto.
rcondt{1} 4; first auto.
rcondf{1} 5; first auto.
auto.
if{1}.
inline{1} (1) SMCReal(KeyEx.KEIdeal).party2.
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondf{1} 4; first auto.
rcondt{1} 4; first auto.
rcondf{1} 5; first auto.
auto.
if{1}.
inline{1} (1) Fwd.Forw.invoke.
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondf{1} 4; first auto.
rcondt{1} 4; first auto.
rcondf{1} 5; first auto.
auto.
inline KeyEx.KEIdeal.invoke.
sp 4 0.
if{1}.
inline KeyEx.KEIdeal.parties.
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondf{1} 5; first auto.
rcondt{1} 5; first auto.
rcondf{1} 6; first auto.
auto.
rcondf{1} 2; first auto.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto.
exfalso => &1 &2 [#] _ _ _ _ _ _ _ _ _ _ []; smt().
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
  (inc func' adv' /\ ={func, adv, in_guard, glob Env, glob Adv, glob MI} /\
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
  var in_guard_low : int fset

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
            (* only mode and destination port matter (destination port id
               must not be 0) *)
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

  (* func_ will end with 2 *)

  proc main(func_ adv_ : addr, in_guard : int fset) : bool = {
    var b : bool;
    stub_st <- None;
    func <- take (size func_ - 1) func_; adv <- adv_;
    b <@ Exper(MI'(SMCReal(StubKE), StubAdv), Env).main
           (func, adv, in_guard_low);
    return b;
  }
}.

section.

(* working up to composition theorem bridging lemmas *)

declare module Adv : FUNC{MI, SMCReal, KeyEx.KEReal, KeyEx.KEIdeal,
                          CompEnv}.
declare module Env : ENV{Adv, MI, SMCReal, KeyEx.KEReal, KeyEx.KEIdeal,
                         CompEnv}.

op real_p1_term_metric_max : int = 2.

op real_p1_term_metric (st : smc_real_p1_state) : int =
     with st = SMCRealP1StateWaitReq   => 2
     with st = SMCRealP1StateWaitKE2 _ => 1
     with st = SMCRealP1StateFinal _   => 0.

lemma ge0_real_p1_term_metric (st : smc_real_p1_state) :
  0 <= real_p1_term_metric st.
proof. by case st. qed.

lemma real_p1_term_metric_is_smc_real_p1_state_wait_ke2
      (st : smc_real_p1_state) :
  is_smc_real_p1_state_wait_ke2 st => real_p1_term_metric st = 1.
proof. by case st. qed.

op real_p2_term_metric_max : int = 2.

op real_p2_term_metric (st : smc_real_p2_state) : int =
     with st = SMCRealP2StateWaitKE1   => 2
     with st = SMCRealP2StateWaitFwd _ => 1
     with st = SMCRealP2StateFinal _   => 0.

lemma ge0_real_p2_term_metric (st : smc_real_p2_state) :
  0 <= real_p2_term_metric st.
proof. by case st. qed.

lemma real_p2_term_metric_is_smc_real_p2_state_wait_fwd
      (st : smc_real_p2_state) :
  is_smc_real_p2_state_wait_fwd st => real_p2_term_metric st = 1.
proof. by case st. qed.

lemma smc_party1_met (KE1 <: FUNC) (KE2 <: FUNC) (n : int) :
  equiv
  [SMCReal(KE1).party1 ~ SMCReal(KE2).party1 :
   ={m, SMCReal.self, SMCReal.adv, SMCReal.st1} /\
   real_p1_term_metric SMCReal.st1{1} = n ==>
   ={res, SMCReal.st1} /\
   (res{1} = None \/ real_p1_term_metric SMCReal.st1{1} = n - 1)].
proof.
proc.
sp 1 1.
if => //.
if => //.
sp 1 1.
if; first smt().
auto => |> &1 &2 <- //.
auto.
if => //.
sp 1 1.
if => //.
sp 1 1.
if; first smt().
auto => |> &1 &2 <- [#] _ -> -> <- [#] -> -> -> />.
case (SMCReal.st1{2}); smt().
auto.
qed.

lemma smc_party2_met (KE1 <: FUNC) (KE2 <: FUNC) (n : int) :
  equiv
  [SMCReal(KE1).party2 ~ SMCReal(KE2).party2 :
   ={m, SMCReal.self, SMCReal.adv, SMCReal.st2} /\
   real_p2_term_metric SMCReal.st2{1} = n ==>
   ={res, SMCReal.st2} /\
   (res{1} = None \/ real_p2_term_metric SMCReal.st2{1} = n - 1)].
proof.
proc.
sp 1 1.
if => //.
if => //.
sp 1 1.
if; first smt().
auto; smt().
auto.
if => //.
sp 1 1.
if => //.
sp 1 1.
if; first smt().
auto => |> &1 &2 <- [#] _ _ _ -> /=.
case (SMCReal.st2{2}); smt().
auto.
qed.

local module SMCSec1Bridge_Left (KE : FUNC) = {
  proc rest(m : msg, r : msg option) : msg option = {
    var not_done : bool <- true;
    var not_done0 : bool <- true;
    var mod : mode; var pt1, pt2 : port; var u : univ;
    var addr1 : addr; var n1 : int;

    while (not_done0) {
      if (m.`2.`1 = SMCReal.self /\ (m.`2.`2 = 1 \/ m.`2.`2 = 3)) {
        r <@ SMCReal(KE).party1(m);
        if (r <> None /\
            let (mod, pt1, pt2, u) = oget r in
            let (addr1, n1) = pt1
            in !(mod = Dir /\
                 (SMCReal.self ++ [2] <= addr1 \/
                  SMCReal.self ++ [1] <= addr1))) {
          r <- None;
        }
      }
      elif (m.`2.`1 = SMCReal.self /\ (m.`2.`2 = 2 \/ m.`2.`2 = 4)) {
        r <@ SMCReal(KE).party2(m);
        if (r <> None /\
            let (mod, pt1, pt2, u) = oget r in
            let (addr1, n1) = pt1
            in !(mod = Dir /\
                 (SMCReal.self ++ [2] <= addr1 \/
                  ! SMCReal.self <= addr1))) {
          r <- None;
        }
      }
      elif (SMCReal.self ++ [1] <= m.`2.`1) {
        r <@ Fwd.Forw.invoke(m);
        if (r <> None /\
            let (mod, pt1, pt2, u) = oget r in
            let (addr1, n1) = pt1
            in !(mod = Dir /\ addr1 = SMCReal.self /\ n1 = 4) /\
               !(mod = Adv /\ ! SMCReal.self <= addr1 /\ n1 = adv_fw_pi)) {
          r <- None;
        }
      }
      else {
        r <@ KE.invoke(m);
        if (r <> None /\
            let (mod, pt1, pt2, u) = oget r in
            let (addr1, n1) = pt1
            in !(mod = Dir /\ addr1 = SMCReal.self /\
                 (n1 = 3 \/ n1 = 4)) /\
               !(mod = Adv /\ ! SMCReal.self <= addr1)) {
          r <- None;
        }
      }
      if (r = None \/ ! SMCReal.self <= (oget r).`2.`1) {
        not_done0 <- false;
      }
      else {
        m <- oget r;
      }
    }
    if (r = None) {
      not_done <- false;
    }
    else {
      m <- oget r;
      (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
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
    while (not_done) {
      (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
      if (MI.func <= addr1) {
        r <@ SMCReal(KE).invoke(m);
        if (r = None) {
          not_done <- false;
        }
        else {
          m <- oget r;
          (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
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
        }
        else {
          m <- oget r;
          (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
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

local module SMCSec1Bridge_TopRight (KE : FUNC) = {
  proc rest(m : msg, r : msg option) : msg option = {
    var not_done : bool <- true;
    var not_done0 : bool <- true;
    var mod : mode; var pt1, pt2 : port; var u : univ;
    var addr1 : addr; var n1 : int;

    while (not_done0) {
      if (m.`2.`1 = SMCReal.self /\ (m.`2.`2 = 1 \/ m.`2.`2 = 3)) {
        r <@ SMCReal(CompEnv(Env, MI(KE, Adv)).StubKE).party1(m);
        if (r <> None /\
            let (mod, pt1, pt2, u) = oget r in
            let (addr1, n1) = pt1
            in !(mod = Dir /\
                 (SMCReal.self ++ [2] <= addr1 \/
                  SMCReal.self ++ [1] <= addr1))) {
          r <- None;
        }
      }
      elif (m.`2.`1 = SMCReal.self /\ (m.`2.`2 = 2 \/ m.`2.`2 = 4)) {
        r <@ SMCReal(CompEnv(Env, MI(KE, Adv)).StubKE).party2(m);
        if (r <> None /\
            let (mod, pt1, pt2, u) = oget r in
            let (addr1, n1) = pt1
            in !(mod = Dir /\
                 (SMCReal.self ++ [2] <= addr1 \/
                  ! SMCReal.self <= addr1))) {
          r <- None;
        }
      }
      elif (SMCReal.self ++ [1] <= m.`2.`1) {
        r <@ Fwd.Forw.invoke(m);
        if (r <> None /\
            let (mod, pt1, pt2, u) = oget r in
            let (addr1, n1) = pt1
            in !(mod = Dir /\ addr1 = SMCReal.self /\ n1 = 4) /\
               !(mod = Adv /\ ! SMCReal.self <= addr1 /\ n1 = adv_fw_pi)) {
          r <- None;
        }
      }
      else {
        r <@ CompEnv(Env, MI(KE, Adv)).StubKE.invoke(m);
        if (r <> None /\
            let (mod, pt1, pt2, u) = oget r in
            let (addr1, n1) = pt1
            in !(mod = Dir /\ addr1 = SMCReal.self /\
                 (n1 = 3 \/ n1 = 4)) /\
               !(mod = Adv /\ ! SMCReal.self <= addr1)) {
          r <- None;
        }
      }
      if (r = None \/ ! SMCReal.self <= (oget r).`2.`1) {
        not_done0 <- false;
      }
      else {
        m <- oget r;
      }
    }
    if (r = None) {
      not_done <- false;
    }
    else {
      m <- oget r;
      (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
      if (MakeInt'.MI.func <= addr1) {
        r <- None; not_done <- false;
      }
      elif (mod = Dir) {
        not_done <- false;
        if (MakeInt'.MI.adv <= addr1) {
          r <- None;
        }
      }
      elif (addr1 <> MakeInt'.MI.adv \/ n1 = 0) {
        r <- None; not_done <- false;
      }
    }          
    while (not_done) {
      (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
      if (MakeInt'.MI.func <= addr1) {
        r <@ SMCReal(CompEnv(Env, MI(KE, Adv)).StubKE).invoke(m);
        if (r = None) {
          not_done <- false;
        }
        else {
          m <- oget r;
          (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
          if (MakeInt'.MI.func <= addr1) {
            r <- None; not_done <- false;
          }
          elif (mod = Dir) {
            not_done <- false;
            if (MakeInt'.MI.adv <= addr1) {
              r <- None;
            }
          }
          elif (addr1 <> MakeInt'.MI.adv \/ n1 = 0) {
            r <- None; not_done <- false;
          }
        }          
      }
      else {
        r <@ CompEnv(Env, MI(KE, Adv)).StubAdv.invoke(m);
        if (r = None) {
          not_done <- false;
        }
        else {
          m <- oget r;
          (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
          if (MakeInt'.MI.adv <= addr1 \/ mod = Dir) {
            r <- None; not_done <- false;
          }
          elif (! MakeInt'.MI.func <= addr1) {
            not_done <- false;
          }
        }
      }      
    }
    return r;
  }
}.

local module SMCSec1Bridge_BotRightKE (KE : FUNC) = {
  proc rest(m : msg, r : msg option) : msg option = {
    var not_done : bool <- true;
    var not_done0 : bool <- true;
    var not_done1 : bool <- true;
    var mod : mode; var pt1, pt2 : port; var u : univ;
    var addr1 : addr; var n1 : int;

    while (not_done0) {
      (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
      if (MI.func <= addr1) {
        r <@ KE.invoke(m);
        if (r = None) {
          not_done0 <- false;
        }
        else {
          m <- oget r;
          (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
          if (MI.func <= addr1) {
            r <- None; not_done0 <- false;
          }
          elif (mod = Dir) {
            not_done0 <- false;
            if (MI.adv <= addr1) {
              r <- None;
            }
          }
          elif (addr1 <> MI.adv \/ n1 = 0) {
            r <- None; not_done0 <- false;
          }
        }          
      }
      else {
        r <@ Adv.invoke(m);
        if (r = None) {
          not_done0 <- false;
        }
        else {
          m <- oget r;
          (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
          if (MI.adv <= addr1 \/ mod = Dir) {
            r <- None; not_done0 <- false;
          }
          elif (! MI.func <= addr1) {
            not_done0 <- false;
          }
        }
      }      
    }
    if (r <> None) {
      m <- oget r; (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
      if (mod = Adv) {
        CompEnv.stub_st <- Some m;
        r <- Some (Adv, (CompEnv.adv, 1), (CompEnv.func ++ [2], 1), UnivUnit);
      }
    }
    if (r <> None /\
        let (mod, pt1, pt2, u) = oget r in
        let (addr1, n1) = pt1
        in !(mod = Dir /\ addr1 = SMCReal.self /\ (n1 = 3 \/ n1 = 4)) /\
           !(mod = Adv /\ ! SMCReal.self <= addr1)) {
      r <- None;
    }
    if (r = None \/ ! SMCReal.self <= (oget r).`2.`1) {
      not_done1 <- false;
    }
    else {
      m <- oget r;
    }
    while (not_done1) {
      if (m.`2.`1 = SMCReal.self /\ (m.`2.`2 = 1 \/ m.`2.`2 = 3)) {
        r <@ SMCReal(CompEnv(Env, MI(KE, Adv)).StubKE).party1(m);
        if (r <> None /\
            let (mod, pt1, pt2, u) = oget r in
            let (addr1, n1) = pt1
            in !(mod = Dir /\
                 (SMCReal.self ++ [2] <= addr1 \/
                  SMCReal.self ++ [1] <= addr1))) {
          r <- None;
        }
      }
      elif (m.`2.`1 = SMCReal.self /\ (m.`2.`2 = 2 \/ m.`2.`2 = 4)) {
        r <@ SMCReal(CompEnv(Env, MI(KE, Adv)).StubKE).party2(m);
        if (r <> None /\
            let (mod, pt1, pt2, u) = oget r in
            let (addr1, n1) = pt1
            in !(mod = Dir /\
                 (SMCReal.self ++ [2] <= addr1 \/
                  ! SMCReal.self <= addr1))) {
          r <- None;
        }
      }
      elif (SMCReal.self ++ [1] <= m.`2.`1) {
        r <@ Fwd.Forw.invoke(m);
        if (r <> None /\
            let (mod, pt1, pt2, u) = oget r in
            let (addr1, n1) = pt1
            in !(mod = Dir /\ addr1 = SMCReal.self /\ n1 = 4) /\
               !(mod = Adv /\ ! SMCReal.self <= addr1 /\ n1 = adv_fw_pi)) {
          r <- None;
        }
      }
      else {
        r <@ CompEnv(Env, MI(KE, Adv)).StubKE.invoke(m);
        if (r <> None /\
            let (mod, pt1, pt2, u) = oget r in
            let (addr1, n1) = pt1
            in !(mod = Dir /\ addr1 = SMCReal.self /\ (n1 = 3 \/ n1 = 4)) /\
               !(mod = Adv /\ ! SMCReal.self <= addr1)) {
          r <- None;
        }
      }
      if (r = None \/ ! SMCReal.self <= (oget r).`2.`1) {
        not_done1 <- false;
      }
      else {
        m <- oget r;
      }
    }
    if (r = None) {
      not_done <- false;
    }
    else {
      m <- oget r;
      (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
      if (MakeInt'.MI.func <= addr1) {
        r <- None; not_done <- false;
      }
      elif (mod = Dir) {
        not_done <- false;
        if (MakeInt'.MI.adv <= addr1) {
          r <- None;
        }
      }
      elif (addr1 <> MakeInt'.MI.adv \/ n1 = 0) {
        r <- None; not_done <- false;
      }
    }          
    while (not_done) {
      (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
      if (MakeInt'.MI.func <= addr1) {
        r <@ SMCReal(CompEnv(Env, MI(KE, Adv)).StubKE).invoke(m);
        if (r = None) {
          not_done <- false;
        }
        else {
          m <- oget r;
          (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
          if (MakeInt'.MI.func <= addr1) {
            r <- None; not_done <- false;
          }
          elif (mod = Dir) {
            not_done <- false;
            if (MakeInt'.MI.adv <= addr1) {
              r <- None;
            }
          }
          elif (addr1 <> MakeInt'.MI.adv \/ n1 = 0) {
            r <- None; not_done <- false;
          }
        }          
      }
      else {
        r <@ CompEnv(Env, MI(KE, Adv)).StubAdv.invoke(m);
        if (r = None) {
          not_done <- false;
        }
        else {
          m <- oget r;
          (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
          if (MakeInt'.MI.adv <= addr1 \/ mod = Dir) {
            r <- None; not_done <- false;
          }
          elif (! MakeInt'.MI.func <= addr1) {
            not_done <- false;
          }
        }
      }      
    }
    return r;
  }
}.

local module SMCSec1Bridge_BotRightAdv (KE : FUNC) = {
  proc rest(m : msg, r : msg option) : msg option = {
    var not_done : bool <- true;
    var not_done0 : bool <- true;
    var mod : mode; var pt1, pt2 : port; var u : univ;
    var addr1 : addr; var n1 : int;

    while (not_done0) {
      (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
      if (MI.func <= addr1) {
        r <@ KE.invoke(m);
        if (r = None) {
          not_done0 <- false;
        }
        else {
          m <- oget r;
          (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
          if (MI.func <= addr1) {
            r <- None; not_done0 <- false;
          }
          elif (mod = Dir) {
            not_done0 <- false;
            if (MI.adv <= addr1) {
              r <- None;
            }
          }
          elif (addr1 <> MI.adv \/ n1 = 0) {
            r <- None; not_done0 <- false;
          }
        }          
      }
      else {
        r <@ Adv.invoke(m);
        if (r = None) {
          not_done0 <- false;
        }
        else {
          m <- oget r;
          (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
          if (MI.adv <= addr1 \/ mod = Dir) {
            r <- None; not_done0 <- false;
          }
          elif (! MI.func <= addr1) {
            not_done0 <- false;
          }
        }
      }      
    }
    if (r <> None) {
      m <- oget r; (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
      if (mod = Dir) {
        CompEnv.stub_st <- Some m;
        r <- Some (Adv, (CompEnv.func ++ [2], 1), (CompEnv.adv, 1), UnivUnit);
      }
    }
    if (r = None) {
      not_done <- false;
    }
    else {
      m <- oget r;
      (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
      if (MakeInt'.MI.adv <= addr1 \/ mod = Dir) {
        r <- None; not_done <- false;
      }
      elif (! MakeInt'.MI.func <= addr1) {
        not_done <- false;
      }
    }
    while (not_done) {
      (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
      if (MakeInt'.MI.func <= addr1) {
        r <@ SMCReal(CompEnv(Env, MI(KE, Adv)).StubKE).invoke(m);
        if (r = None) {
          not_done <- false;
        }
        else {
          m <- oget r;
          (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
          if (MakeInt'.MI.func <= addr1) {
            r <- None; not_done <- false;
          }
          elif (mod = Dir) {
            not_done <- false;
            if (MakeInt'.MI.adv <= addr1) {
              r <- None;
            }
          }
          elif (addr1 <> MakeInt'.MI.adv \/ n1 = 0) {
            r <- None; not_done <- false;
          }
        }          
      }
      else {
        r <@ CompEnv(Env, MI(KE, Adv)).StubAdv.invoke(m);
        if (r = None) {
          not_done <- false;
        }
        else {
          m <- oget r;
          (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
          if (MakeInt'.MI.adv <= addr1 \/ mod = Dir) {
            r <- None; not_done <- false;
          }
          elif (! MakeInt'.MI.func <= addr1) {
            not_done <- false;
          }
        }
      }      
    }
    return r;
  }
}.

(* working up to KEReal bridging lemma

   first we enable core proof to be done using KERealSimp *)

local clone KeyEx.RealSimp as KERS
proof *.

local lemma smc_real_ke_real_simp
            (func' adv' : addr, in_guard' : int fset) &m :
  exper_pre func' adv' =>
  Pr[Exper(MI(SMCReal(KeyEx.KEReal), Adv), Env).main
       (func', adv', in_guard') @ &m : res] =
  Pr[Exper(MI(SMCReal(KERS.KERealSimp), Adv), Env).main
       (func', adv', in_guard') @ &m : res].
proof.
move => ep.
byequiv => //.
proc.
seq 1 1 :
  (={func, adv, in_guard, glob MI, glob Adv, glob Env, glob SMCReal} /\
   MI.func{1} = func' /\ MI.adv{1} = adv' /\
   SMCReal.self{1} = func' /\ SMCReal.adv{1} = adv' /\
   Fwd.Forw.self{1} = func' ++ [1] /\ Fwd.Forw.adv{1} = adv' /\
   KeyEx.KEReal.self{1} = func' ++ [2] /\
   KeyEx.KEReal.adv{1} = adv' /\
   KeyEx.Fwd1.Forw.self{1} = func' ++ [2] ++ [1] /\
   KeyEx.Fwd1.Forw.adv{1} = adv' /\
   KeyEx.Fwd2.Forw.self{1} = func' ++ [2] ++ [2] /\
   KeyEx.Fwd2.Forw.adv{1} = adv' /\
   KERS.KERealSimp.self{2} = func' ++ [2] /\ KERS.KERealSimp.adv{2} = adv' /\
   KERS.real_simp_rel
   {|KERS.real_simp_rel_st_func = func' ++ [2];
     KERS.real_simp_rel_st_r1s  = KeyEx.KEReal.st1{1};
     KERS.real_simp_rel_st_r2s  = KeyEx.KEReal.st2{1};
     KERS.real_simp_rel_st_fws1 = KeyEx.Fwd1.Forw.st{1};
     KERS.real_simp_rel_st_fws2 = KeyEx.Fwd2.Forw.st{1};
     KERS.real_simp_rel_st_rss  = KERS.KERealSimp.st{2}|}).
inline MI(SMCReal(KeyEx.KEReal), Adv).init
       MI(SMCReal(KERS.KERealSimp), Adv).init
       SMCReal(KeyEx.KEReal).init
       SMCReal(KERS.KERealSimp).init.
swap 12 2.
call (_ : true).
call (KERS.KEReal_KERealSimp_init (func' ++ [2]) adv').
inline*; auto.
call
  (_ :
   ={glob MI, glob Adv, glob SMCReal} /\
   MI.func{1} = func' /\ MI.adv{1} = adv' /\
   exper_pre func' adv' /\
   SMCReal.self{1} = func' /\ SMCReal.adv{1} = adv' /\
   Fwd.Forw.self{1} = func' ++ [1] /\ Fwd.Forw.adv{1} = adv' /\
   KeyEx.KEReal.self{1} = func' ++ [2] /\
   KeyEx.KEReal.adv{1} = adv' /\
   KeyEx.Fwd1.Forw.self{1} = func' ++ [2] ++ [1] /\
   KeyEx.Fwd1.Forw.adv{1} = adv' /\
   KeyEx.Fwd2.Forw.self{1} = func' ++ [2] ++ [2] /\
   KeyEx.Fwd2.Forw.adv{1} = adv' /\
   KERS.KERealSimp.self{2} = func' ++ [2] /\ KERS.KERealSimp.adv{2} = adv' /\
   KERS.real_simp_rel
   {|KERS.real_simp_rel_st_func = func' ++ [2];
     KERS.real_simp_rel_st_r1s  = KeyEx.KEReal.st1{1};
     KERS.real_simp_rel_st_r2s  = KeyEx.KEReal.st2{1};
     KERS.real_simp_rel_st_fws1 = KeyEx.Fwd1.Forw.st{1};
     KERS.real_simp_rel_st_fws2 = KeyEx.Fwd2.Forw.st{1};
     KERS.real_simp_rel_st_rss  = KERS.KERealSimp.st{2}|}).
proc.
sp 2 2.
if => //.
inline MI(SMCReal(KeyEx.KEReal), Adv).loop
       MI(SMCReal(KERS.KERealSimp), Adv).loop.
sp 3 3; wp.
while
  (={not_done, m0, r0, glob MI, glob Adv, glob SMCReal} /\
   MI.func{1} = func' /\ MI.adv{1} = adv' /\
   exper_pre func' adv' /\
   SMCReal.self{1} = func' /\ SMCReal.adv{1} = adv' /\
   Fwd.Forw.self{1} = func' ++ [1] /\ Fwd.Forw.adv{1} = adv' /\
   KeyEx.KEReal.self{1} = func' ++ [2] /\
   KeyEx.KEReal.adv{1} = adv' /\
   KeyEx.Fwd1.Forw.self{1} = func' ++ [2] ++ [1] /\
   KeyEx.Fwd1.Forw.adv{1} = adv' /\
   KeyEx.Fwd2.Forw.self{1} = func' ++ [2] ++ [2] /\
   KeyEx.Fwd2.Forw.adv{1} = adv' /\
   KERS.KERealSimp.self{2} = func' ++ [2] /\ KERS.KERealSimp.adv{2} = adv' /\
   KERS.real_simp_rel
   {|KERS.real_simp_rel_st_func = func' ++ [2];
     KERS.real_simp_rel_st_r1s  = KeyEx.KEReal.st1{1};
     KERS.real_simp_rel_st_r2s  = KeyEx.KEReal.st2{1};
     KERS.real_simp_rel_st_fws1 = KeyEx.Fwd1.Forw.st{1};
     KERS.real_simp_rel_st_fws2 = KeyEx.Fwd2.Forw.st{1};
     KERS.real_simp_rel_st_rss  = KERS.KERealSimp.st{2}|}).
sp 2 2.
if => //.
wp.
call
  (_ :
   ={glob SMCReal} /\
   exper_pre func' adv' /\
   SMCReal.self{1} = func' /\ SMCReal.adv{1} = adv' /\
   Fwd.Forw.self{1} = func' ++ [1] /\ Fwd.Forw.adv{1} = adv' /\
   KeyEx.KEReal.self{1} = func' ++ [2] /\
   KeyEx.KEReal.adv{1} = adv' /\
   KeyEx.Fwd1.Forw.self{1} = func' ++ [2] ++ [1] /\
   KeyEx.Fwd1.Forw.adv{1} = adv' /\
   KeyEx.Fwd2.Forw.self{1} = func' ++ [2] ++ [2] /\
   KeyEx.Fwd2.Forw.adv{1} = adv' /\
   KERS.KERealSimp.self{2} = func' ++ [2] /\ KERS.KERealSimp.adv{2} = adv' /\
   KERS.real_simp_rel
   {|KERS.real_simp_rel_st_func = func' ++ [2];
     KERS.real_simp_rel_st_r1s  = KeyEx.KEReal.st1{1};
     KERS.real_simp_rel_st_r2s  = KeyEx.KEReal.st2{1};
     KERS.real_simp_rel_st_fws1 = KeyEx.Fwd1.Forw.st{1};
     KERS.real_simp_rel_st_fws2 = KeyEx.Fwd2.Forw.st{1};
     KERS.real_simp_rel_st_rss  = KERS.KERealSimp.st{2}|}).
sp 3 3.
if => //.
inline SMCReal(KeyEx.KEReal).loop SMCReal(KERS.KERealSimp).loop.
sp 3 3; wp.
while
  (={not_done, m0, r0} /\
   ={glob SMCReal} /\
   exper_pre func' adv' /\
   SMCReal.self{1} = func' /\ SMCReal.adv{1} = adv' /\
   Fwd.Forw.self{1} = func' ++ [1] /\ Fwd.Forw.adv{1} = adv' /\
   KeyEx.KEReal.self{1} = func' ++ [2] /\
   KeyEx.KEReal.adv{1} = adv' /\
   KeyEx.Fwd1.Forw.self{1} = func' ++ [2] ++ [1] /\
   KeyEx.Fwd1.Forw.adv{1} = adv' /\
   KeyEx.Fwd2.Forw.self{1} = func' ++ [2] ++ [2] /\
   KeyEx.Fwd2.Forw.adv{1} = adv' /\
   KERS.KERealSimp.self{2} = func' ++ [2] /\ KERS.KERealSimp.adv{2} = adv' /\
   KERS.real_simp_rel
   {|KERS.real_simp_rel_st_func = func' ++ [2];
     KERS.real_simp_rel_st_r1s  = KeyEx.KEReal.st1{1};
     KERS.real_simp_rel_st_r2s  = KeyEx.KEReal.st2{1};
     KERS.real_simp_rel_st_fws1 = KeyEx.Fwd1.Forw.st{1};
     KERS.real_simp_rel_st_fws2 = KeyEx.Fwd2.Forw.st{1};
     KERS.real_simp_rel_st_rss  = KERS.KERealSimp.st{2}|}).
if => //.
wp; call (_ : ={glob SMCReal}); first sim.
auto.
if => //.
wp; call (_ : ={glob SMCReal}); first sim.
auto.
if => //.
wp; call (_ : ={glob SMCReal}); first sim.
auto.
wp; call (KERS.KEReal_KERealSimp_invoke (func' ++ [2]) adv').
auto; progress; by rewrite inc_ext1.
auto.
auto.
wp; call (_ : true).
auto.
auto.
auto.
auto.
qed.

(* start of core of KERealSimp bridging lemma proof

   will be replicated via textual substitutions for KEIdeal (need to
   have way of doing this proof once, and instantiating twice) *)

local module StubKE_KERealSimp = CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubKE.

type real_ke_real_simp_term_met_st = {
  real_ke_real_simp_term_met_st_p1s : smc_real_p1_state;
  real_ke_real_simp_term_met_st_p2s : smc_real_p2_state;
  real_ke_real_simp_term_met_st_fws : Fwd.fw_state;
  real_ke_real_simp_term_met_st_kes  : KERS.ke_real_simp_state
}.

op real_ke_real_term_metric_max : int =
     real_p1_term_metric_max +
     real_p2_term_metric_max +
     Fwd.term_metric_max +
     KERS.ke_real_simp_term_metric_max.

op real_ke_real_term_metric (rtms : real_ke_real_simp_term_met_st) : int =
     real_p1_term_metric rtms.`real_ke_real_simp_term_met_st_p1s +
     real_p2_term_metric rtms.`real_ke_real_simp_term_met_st_p2s +
     Fwd.term_metric rtms.`real_ke_real_simp_term_met_st_fws +
     KERS.ke_real_simp_term_metric rtms.`real_ke_real_simp_term_met_st_kes.

lemma ge0_real_ke_real_term_metric (rtms : real_ke_real_simp_term_met_st) :
  0 <= real_ke_real_term_metric rtms.
proof.
smt(ge0_real_p1_term_metric ge0_real_p2_term_metric
    Fwd.ge0_term_metric KERS.ge0_ke_real_simp_term_metric).
qed.

lemma real_ke_real_term_metric0 (rtms : real_ke_real_simp_term_met_st) :
  real_ke_real_term_metric rtms = 0 =>
  real_p1_term_metric rtms.`real_ke_real_simp_term_met_st_p1s = 0 /\
  real_p2_term_metric rtms.`real_ke_real_simp_term_met_st_p2s = 0 /\
  Fwd.term_metric rtms.`real_ke_real_simp_term_met_st_fws = 0 /\
  KERS.ke_real_simp_term_metric rtms.`real_ke_real_simp_term_met_st_kes = 0.
proof.
smt(ge0_real_p1_term_metric ge0_real_p2_term_metric
    Fwd.ge0_term_metric KERS.ge0_ke_real_simp_term_metric).
qed.

local lemma smc_sec1_ke_real_simp_bridge_induction (n : int) :
  equiv
  [SMCSec1Bridge_Left(KERS.KERealSimp).rest ~
   SMCSec1Bridge_TopRight(KERS.KERealSimp).rest :
   ={m, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
    (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
    MI.func{1} ++ [1] <= m{1}.`2.`1 \/
    (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
   real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   ={res, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   CompEnv.stub_st{2} = None] /\
  equiv
  [SMCSec1Bridge_Left(KERS.KERealSimp).rest ~
   SMCSec1Bridge_BotRightKE(KERS.KERealSimp).rest :
   ={m, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   m{1}.`1 = Adv /\ MI.func{1} ++ [2] <= m{1}.`2.`1 /\
   real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   ={res, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   CompEnv.stub_st{2} = None] /\
  equiv
  [SMCSec1Bridge_Left(KERS.KERealSimp).rest ~
   SMCSec1Bridge_BotRightAdv(KERS.KERealSimp).rest :
   ={m, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   m{1}.`1 = Adv /\ MI.func{1} ++ [2] <= m{1}.`2.`1 /\
   real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   ={res, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   CompEnv.stub_st{2} = None].
proof.
case (n < 0).
move => lt0_n.
(split; last split); proc; exfalso; smt(ge0_real_ke_real_term_metric).
rewrite -lezNgt.
elim n => [| n ge0_n IH].
(* basis step *)
split; last split.
(* SMCSec1Bridge_Left(KERS.KERealSimp).rest ~
   SMCSec1Bridge_TopRight(KERS.KERealSimp).rest *)
proc.
rcondt{1} 3; first auto.
rcondt{2} 3; first auto.
sp 2 2.
if => //.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\ r{1} = None).
exlim (real_p1_term_metric SMCReal.st1{1}) => p1_met.
call (smc_party1_met KERS.KERealSimp StubKE_KERealSimp p1_met).
auto; smt(real_ke_real_term_metric0 ge0_real_p1_term_metric).
rcondf{1} 1; first auto.
rcondf{2} 1; first auto.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
if => //.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\ r{1} = None).
exlim (real_p2_term_metric SMCReal.st2{1}) => p2_met.
call (smc_party2_met KERS.KERealSimp StubKE_KERealSimp p2_met).
auto; smt(real_ke_real_term_metric0 ge0_real_p2_term_metric).
rcondf{1} 1; first auto.
rcondf{2} 1; first auto.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
if => //.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\ r{1} = None).
exlim (Fwd.term_metric Fwd.Forw.st{1}) => fwd_met.
call (Fwd.term_invoke fwd_met).
auto; smt(real_ke_real_term_metric0 Fwd.ge0_term_metric).
rcondf{1} 1; first auto.
rcondf{2} 1; first auto.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
inline{2} (1) CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubKE.invoke.
rcondf{2} 2; first auto.
inline{2} (1) MI(KERS.KERealSimp, Adv).invoke.
rcondt{2} 5; first auto; smt().
inline{2} (1) MI(KERS.KERealSimp, Adv).loop.
rcondt{2} 8; first auto.
rcondt{2} 10; first auto; smt().
sp 0 9.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done0{2}
   /\ r{1} = r2{2} /\
   ={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\ r{1} = None).
exlim (KERS.ke_real_simp_term_metric KERS.KERealSimp.st{1}) => ke_met.
call (KERS.ke_real_simp_term_invoke ke_met).
auto; smt(real_ke_real_term_metric0 KERS.ge0_ke_real_simp_term_metric).
rcondt{2} 1; first auto.
rcondf{2} 2; first auto.
sp 0 5.
rcondf{1} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondt{1} 1; first auto; smt().
rcondt{2} 1; first auto; smt().
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondt{1} 2; first auto; smt().
rcondt{2} 2; first auto; smt().
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto; smt().
(* SMCSec1Bridge_Left(KERS.KERealSimp).rest ~
   SMCSec1Bridge_BotRightKE(KERS.KERealSimp).rest *)
proc.
rcondt{1} 3; first auto.
rcondt{2} 4; first auto.
rcondt{2} 6; first auto.
rcondf{1} 3; first auto; smt(not_le_ext_nonnil_l).
rcondf{1} 3; first auto; smt(not_le_ext_nonnil_l).
rcondf{1} 3; first auto; smt(not_le_other_branch).
sp 2 5.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done1{2} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\ r{1} = None).
exlim (KERS.ke_real_simp_term_metric KERS.KERealSimp.st{1}) => ke_met.
call (KERS.ke_real_simp_term_invoke ke_met).
auto; smt(real_ke_real_term_metric0 KERS.ge0_ke_real_simp_term_metric).
rcondf{1} 1; first auto.
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{2} 1; first auto.
rcondf{2} 2; first auto.
rcondf{2} 2; first auto.
rcondf{2} 2; first auto.
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
rcondt{2} 3; first auto.
rcondf{2} 4; first auto.
auto.
(* SMCSec1Bridge_Left(KERS.KERealSimp).rest ~
   SMCSec1Bridge_BotRightAdv(KERS.KERealSimp).rest *)
proc.
rcondt{1} 3; first auto.
rcondt{2} 3; first auto.
rcondt{2} 5; first auto.
rcondf{1} 3; first auto; smt(not_le_ext_nonnil_l).
rcondf{1} 3; first auto; smt(not_le_ext_nonnil_l).
rcondf{1} 3; first auto; smt(not_le_other_branch).
sp 2 4.
seq 1 1 :
  (not_done{1} /\ not_done0{1} /\ not_done{2} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\ r{1} = None).
exlim (KERS.ke_real_simp_term_metric KERS.KERealSimp.st{1}) => ke_met.
call (KERS.ke_real_simp_term_invoke ke_met).
auto; smt(real_ke_real_term_metric0 KERS.ge0_ke_real_simp_term_metric).
rcondf{1} 1; first auto.
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{2} 1; first auto.
rcondf{2} 2; first auto.
rcondf{2} 2; first auto.
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
auto.
(* inductive step *)
split; last split.
(* SMCSec1Bridge_Left(KERS.KERealSimp).rest ~
   SMCSec1Bridge_TopRight(KERS.KERealSimp).rest *)
proc; sp 2 2.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
if => //.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\
   (r{1} = None \/
    real_ke_real_term_metric
    {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
      real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
      real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
      real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n)).
exlim (real_p1_term_metric SMCReal.st1{1}) => p1_met.
call (smc_party1_met KERS.KERealSimp StubKE_KERealSimp p1_met).
auto; progress; smt().
if => //.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondt{1} 3; first auto.
rcondt{2} 3; first auto.
rcondf{1} 4; first auto.
rcondf{2} 4; first auto.
auto.
case (r{1} = None).
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
conseq
  (_ :
   not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\
   real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
   r{1} <> None /\
   (oget r{1}).`1 = Dir /\
   (SMCReal.self{1} ++ [2] <= (oget r{1}).`2.`1 \/
    SMCReal.self{1} ++ [1] <= (oget r{1}).`2.`1) ==>
   _); first smt(le_trans le_ext_r).
rcondf{1} 1; first auto.
progress; smt(le_trans le_ext_r).
rcondf{2} 1; first auto.
progress; smt(le_trans le_ext_r).
sp 1 1.
conseq
  (_ :
   not_done{1} /\ not_done0{1} /\ not_done{2} /\ not_done0{2} /\
   ={m, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
    (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
    MI.func{1} ++ [1] <= m{1}.`2.`1 \/
    (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
   real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _); first smt().
(* use part 1 of induction *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KERS.KERealSimp).rest(m, r);}
(={m, r, glob MI, glob SMCReal, glob KERS.KERealSimp,
   glob Adv} /\
 not_done{1} /\ not_done0{1} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob Adv})
(={m, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
  (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m{1}.`2.`1 \/
  (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
 real_ke_real_term_metric
 {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
   real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
   real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 not_done{2} /\ not_done0{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} m{2} r{1}.
inline SMCSec1Bridge_Left(KERS.KERealSimp).rest.
sp 0 4.
sim; smt().
transitivity{2}
{r <@ SMCSec1Bridge_TopRight(KERS.KERealSimp).rest(m, r);}
(={m, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
  (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m{1}.`2.`1 \/
  (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
  real_ke_real_term_metric
  {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
    real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
    real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
    real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m, r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done0{2} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          MI.adv{2} (MI.func{1} ++ [2]) MI.in_guard{2} m{2} r{2}.
exlim
  (real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|}) => met.
have [IH_first _] := IH.
call IH_first.
auto.
inline SMCSec1Bridge_TopRight(KERS.KERealSimp).rest.
sp 4 0.
sim; smt().
(* end of use of part 1 of induction *)
if => //.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\
   (r{1} = None \/
    real_ke_real_term_metric
    {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
      real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
      real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
      real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n)).
exlim (real_p2_term_metric SMCReal.st2{1}) => p2_met.
call (smc_party2_met KERS.KERealSimp StubKE_KERealSimp p2_met).
auto; progress; smt().
if => //.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondt{1} 3; first auto.
rcondt{2} 3; first auto.
rcondf{1} 4; first auto.
rcondf{2} 4; first auto.
auto.
case (r{1} = None).
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
conseq
  (_ :
   not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\
   real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
   r{1} <> None /\
   (oget r{1}).`1 = Dir /\
   (SMCReal.self{1} ++ [2] <= (oget r{1}).`2.`1 \/
    ! SMCReal.self{1} <= (oget r{1}).`2.`1) ==>
   _); first smt(le_trans le_ext_r).
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondf{1} 5; first auto; smt().
rcondf{2} 5; first auto; smt().
rcondt{1} 5; first auto.
rcondt{2} 5; first auto.
sp 5 5.
if; first smt().
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
rcondf{1} 1; first auto.
rcondf{2} 1; first auto.
auto.
sp 1 1.
conseq
  (_ :
   not_done{1} /\ not_done0{1} /\ not_done{2} /\ not_done0{2} /\
   ={m, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
    (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
    MI.func{1} ++ [1] <= m{1}.`2.`1 \/
    (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
   real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _); first smt().
(* use part 1 of induction *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KERS.KERealSimp).rest(m, r);}
(={m, r, glob MI, glob SMCReal, glob KERS.KERealSimp,
   glob Adv} /\
 not_done{1} /\ not_done0{1} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob Adv})
(={m, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
  (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m{1}.`2.`1 \/
  (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
 real_ke_real_term_metric
 {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
   real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
   real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 not_done{2} /\ not_done0{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} m{2} r{1}.
inline SMCSec1Bridge_Left(KERS.KERealSimp).rest.
sp 0 4.
sim; smt().
transitivity{2}
{r <@ SMCSec1Bridge_TopRight(KERS.KERealSimp).rest(m, r);}
(={m, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
  (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m{1}.`2.`1 \/
  (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
  real_ke_real_term_metric
  {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
    real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
    real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
    real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m, r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done0{2} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} MI.adv{2} (MI.func{1} ++ [2])
          MI.in_guard{2}  m{2} r{2}.
exlim
  (real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|}) => met.
have [IH_first _] := IH.
call IH_first.
auto.
inline SMCSec1Bridge_TopRight(KERS.KERealSimp).rest.
sp 4 0.
sim; smt().
(* end of use of part 1 of induction *)
if => //.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\
   (r{1} = None \/
    real_ke_real_term_metric
    {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
      real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
      real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
      real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n)).
exlim (Fwd.term_metric Fwd.Forw.st{1}) => fwd_met.
call (Fwd.term_invoke fwd_met).
auto; progress; smt().
if => //.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondt{1} 3; first auto.
rcondt{2} 3; first auto.
rcondf{1} 4; first auto.
rcondf{2} 4; first auto.
auto.
case (r{1} = None).
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
conseq
  (_ :
   not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\
   real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
   r{1} <> None /\
   ((oget r{1}).`1 = Dir /\ (oget r{1}).`2.`1 = MI.func{1} /\
    (oget r{1}).`2.`2 = 4 \/
    (oget r{1}).`1 = Adv /\ ! MI.func{1} <= (oget r{1}).`2.`1 /\
    (oget r{1}).`2.`2 = adv_fw_pi) ==>
   _); first smt(le_trans le_ext_r).
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondf{1} 5; first auto; smt().
rcondf{2} 5; first auto; smt().
rcondf{1} 5; first auto; smt(le_refl).
rcondf{2} 5; first auto; smt(le_refl).
sp 4 4.
if; first smt().
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
rcondf{1} 3; first auto; smt().
rcondf{2} 3; first auto; smt().
sp 2 2.
inline{2} (1) CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubAdv.invoke.
rcondf{2} 2; first auto.
inline{2} (1) MI(KERS.KERealSimp, Adv).invoke.
rcondt{2} 5; first auto; smt(in_fset1 le_refl incP).
inline MI(KERS.KERealSimp, Adv).loop.
rcondt{2} 8; first auto.
rcondf{2} 10; first auto; smt(inc_le1_not_lr le_ext_r).
sp 0 9.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ !not_done0{1} /\ !not_done0{2} /\
   not_done1{2} /\ r{1} = r2{2} /\
   ={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\
   real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n).
call (_ : true).
auto; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondf{2} 4; first auto.
rcondt{2} 5; first auto.
rcondf{2} 6; first auto.
auto.
sp 3 3.
if; first smt().
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondf{2} 5; first auto.
rcondt{2} 6; first auto.
rcondf{2} 7; first auto.
auto.
case (MI.func{1} ++ [2] <= addr1{1}).
rcondf{1} 1; first auto; smt(le_trans le_ext_r).
rcondf{2} 1; first auto; smt().
rcondt{1} 1; first auto.
rcondt{1} 3; first auto; smt(le_ext_r le_trans).
inline{1} (1) SMCReal(KERS.KERealSimp).invoke.
rcondt{1} 7; first auto; progress.
right; rewrite negb_or not_dir in H10.
smt(le_ext_r le_trans).
inline{1} (1) SMCReal(KERS.KERealSimp).loop.
sp 9 0.
conseq
  (_ :
   not_done{1} /\ not_done1{1} /\ not_done{2} /\ not_done1{2} /\
   ={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   m1{1} = m2{2} /\
   m1{1}.`1 = Adv /\ MI.func{1} ++ [2] <= m1{1}.`2.`1 /\
   real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _).
move => &1 &2 />. rewrite negb_or not_dir /#.
(* use part 3 of induction: *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KERS.KERealSimp).rest(m1, r1);}
(={m1, r1, glob MI, glob SMCReal, glob KERS.KERealSimp,
   glob Adv} /\
 not_done{1} /\ not_done1{1} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob Adv})
(={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 m1{1} = m2{2} /\
 m1{1}.`1 = Adv /\ MI.func{1} ++ [2] <= m1{1}.`2.`1 /\
 real_ke_real_term_metric
 {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
   real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
   real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 not_done{2} /\ not_done1{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} m2{2} r1{1}.
inline SMCSec1Bridge_Left(KERS.KERealSimp).rest.
sp 0 4.
seq 3 1 :
  (={glob MI, glob SMCReal, glob KERS.KERealSimp,
     glob Adv} /\
   r{1} = r2{2} /\ not_done{1} = not_done2{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
transitivity{2}
{r <@ SMCSec1Bridge_BotRightAdv(KERS.KERealSimp).rest(m2, r2);}
(={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 m1{1} = m2{2} /\
 m1{1}.`1 = UCCore'.Adv /\ MI.func{1} ++ [2] <= m1{1}.`2.`1 /\
 real_ke_real_term_metric
 {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
   real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
   real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m2, r2, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done1{2} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} MI.adv{2} (MI.func{1} ++ [2])
          MI.in_guard{2} m2{2} r2{2}.
exlim
  (real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|}) => met.
have [_ [_ IH_third]] := IH.
call IH_third.
auto.
inline SMCSec1Bridge_BotRightAdv(KERS.KERealSimp).rest.
sp 4 0.
seq 1 3 :
  (={glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv,
     glob Adv} /\
   r3{1} = r0{2} /\ not_done00{1} = not_done1{2} /\ not_done2{1} = not_done{2}).
sim; smt().
seq 1 2 :
  (={glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv,
     glob Adv} /\
   r3{1} = r{2} /\ not_done00{1} = not_done1{2} /\ not_done2{1} = not_done{2}).
sim.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
(* end of use of part 3 of induction *)
rcondt{2} 1; first auto; smt().
rcondf{2} 2; first auto.
rcondt{2} 4; first auto; smt().
rcondf{2} 7; first auto; smt().
rcondf{2} 8; first auto.
rcondf{2} 11; first auto; smt().
sp 0 10.
if; first smt().
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
rcondt{1} 3; first auto; smt().
rcondt{2} 3; first auto; smt().
inline{1} (1) SMCReal(KERS.KERealSimp).invoke.
inline{2} (1) SMCReal(CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubKE).invoke.
sp 6 6.
if; first smt().
inline{1} (1) SMCReal(KERS.KERealSimp).loop.
inline{2} (1) SMCReal(CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubKE).loop.
sp 3 3.
conseq
  (_ :
   not_done{1} /\ not_done1{1} /\ not_done{2} /\ not_done2{2} /\
   ={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   m1{1} = m4{2} /\
   (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = MI.func{1} /\
    (m1{1}.`2.`2 = 1 \/ m1{1}.`2.`2 = 2 \/ m1{1}.`2.`2 = 3 \/ m1{1}.`2.`2 = 4) \/
    MI.func{1} ++ [1] <= m1{1}.`2.`1 \/
    (m1{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m1{1}.`2.`1)) /\
   real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _).
move => &1 &2 /> _ <- [#] -> -> -> -> -> /#.
(* use part 1 of induction *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KERS.KERealSimp).rest(m1, r1);}
(={m1, r1, glob MI, glob SMCReal, glob KERS.KERealSimp,
   glob Adv} /\
 not_done{1} /\ not_done1{1} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob Adv})
(={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 m1{1} = m4{2} /\
 (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = MI.func{1} /\
  (m1{1}.`2.`2 = 1 \/ m1{1}.`2.`2 = 2 \/ m1{1}.`2.`2 = 3 \/ m1{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m1{1}.`2.`1 \/
  (m1{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m1{1}.`2.`1)) /\
 real_ke_real_term_metric
 {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
   real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
   real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 not_done{2} /\ not_done2{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} m4{2} r1{1}.
inline SMCSec1Bridge_Left(KERS.KERealSimp).rest.
sp 0 4.
seq 3 1 :
  (={glob MI, glob SMCReal, glob KERS.KERealSimp,
     glob Adv} /\
   r{1} = r2{2} /\ not_done{1} = not_done2{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim; smt().
transitivity{2}
{r <@ SMCSec1Bridge_TopRight(KERS.KERealSimp).rest(m4, r4);}
(={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 m1{1} = m4{2} /\
 (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = MI.func{1} /\
  (m1{1}.`2.`2 = 1 \/ m1{1}.`2.`2 = 2 \/ m1{1}.`2.`2 = 3 \/ m1{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m1{1}.`2.`1 \/
  (m1{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m1{1}.`2.`1)) /\
  real_ke_real_term_metric
  {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
    real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
    real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
    real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m4, r4, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done2{2} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} MI.adv{2} (MI.func{1} ++ [2])
          MI.in_guard{2} m4{2} r4{2}.
exlim
  (real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|}) => met.
have [IH_first _] := IH.
call IH_first.
auto.
inline SMCSec1Bridge_TopRight(KERS.KERealSimp).rest.
sp 4 0.
seq 1 3 :
  (={glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv,
     glob Adv} /\
   r5{1} = r{2} /\ not_done3{1} = not_done{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
(* end of use of part 1 of induction *)
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
sp 1 1.
conseq
  (_ :
   not_done{1} /\ not_done0{1} /\ not_done{2} /\ not_done0{2} /\
   ={m, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
    (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
    MI.func{1} ++ [1] <= m{1}.`2.`1 \/
    (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
   real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _); first smt().
(* use part 1 of induction *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KERS.KERealSimp).rest(m, r);}
(={m, r, glob MI, glob SMCReal, glob KERS.KERealSimp,
   glob Adv} /\
 not_done{1} /\ not_done0{1} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob Adv})
(={m, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
  (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m{1}.`2.`1 \/
  (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
 real_ke_real_term_metric
 {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
   real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
   real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 not_done{2} /\ not_done0{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          m{2} r{1}.
inline SMCSec1Bridge_Left(KERS.KERealSimp).rest.
sp 0 4.
sim; smt().
transitivity{2}
{r <@ SMCSec1Bridge_TopRight(KERS.KERealSimp).rest(m, r);}
(={m, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
  (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m{1}.`2.`1 \/
  (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
  real_ke_real_term_metric
  {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
    real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
    real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
    real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m, r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done0{2} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          MI.adv{2} (MI.func{1} ++ [2]) MI.in_guard{2} m{2} r{2}.
exlim
  (real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|}) => met.
have [IH_first _] := IH.
call IH_first.
auto.
inline SMCSec1Bridge_TopRight(KERS.KERealSimp).rest.
sp 4 0.
sim; smt().
(* end of use of part 1 of induction *)
inline{2} (1) CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubKE.invoke.
rcondf{2} 2; first auto.
inline{2} (1) MI(KERS.KERealSimp, Adv).invoke.
rcondt{2} 5; first auto; smt().
inline{2} (1) MI(KERS.KERealSimp, Adv).loop.
rcondt{2} 8; first auto.
rcondt{2} 10; first auto; smt().
sp 0 9.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done0{2} /\
   not_done1{2} /\ r{1} = r2{2} /\
   ={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\
   (r{1} = None \/
   real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n)).
exlim (KERS.ke_real_simp_term_metric KERS.KERealSimp.st{1}) => ke_met.
call (KERS.ke_real_simp_term_invoke ke_met).
auto; progress; smt().
case (r{1} = None).
rcondt{2} 1; first auto.
rcondf{2} 2; first auto.
rcondf{2} 4; first auto.
rcondf{1} 1; first auto.
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 5; first auto.
rcondt{2} 5; first auto.
rcondf{2} 6; first auto.
rcondt{2} 6; first auto.
rcondf{2} 7; first auto.
auto.
rcondf{2} 1; first auto.
case (MI.func{1} ++ [2] <= (oget r{1}).`2.`1).
rcondt{1} 1; first auto; smt(not_le_ext_nonnil_l le_trans le_ext_r).
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
rcondt{2} 4; first auto. 
rcondf{2} 6; first auto.
rcondf{2} 8; first auto.
rcondf{2} 9; first auto.
rcondt{2} 9; first auto.
rcondf{2} 10; first auto.
rcondt{2} 10; first auto.
rcondf{2} 11; first auto.
auto.
rcondf{2} 4; first auto.
case ((oget r{1}).`1 = Dir).
rcondt{2} 4; first auto.
case (MI.adv{1} <= (oget r{1}).`2.`1).
rcondt{2} 5; first auto.
rcondf{2} 6; first auto.
rcondf{2} 8; first auto.
sp 0 8.
rcondt{1} 1; first auto; smt(incP le_refl).
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
rcondf{2} 1; first auto.
rcondt{2} 1; first auto.
rcondf{2} 2; first auto.
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
auto.
rcondf{2} 5; first auto.
rcondf{2} 5; first auto.
rcondt{2} 7; first auto.
rcondf{2} 10; first auto; smt().
sp 0 10.
if => //.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondt{1} 3; first auto.
rcondt{2} 3; first auto.
rcondf{1} 4; first auto.
rcondf{2} 4; first auto.
auto.
rcondf{1} 1; first auto; smt(le_refl).
rcondf{2} 1; first auto; smt(le_refl).
sp 1 1.
conseq
  (_ :
   not_done{1} /\ not_done0{1} /\ not_done{2} /\ not_done0{2} /\
   ={m, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
    (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
    MI.func{1} ++ [1] <= m{1}.`2.`1 \/
    (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
   real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _); first smt().
(* use part 1 of induction *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KERS.KERealSimp).rest(m, r);}
(={m, r, glob MI, glob SMCReal, glob KERS.KERealSimp,
   glob Adv} /\
 not_done{1} /\ not_done0{1} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob Adv})
(={m, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
  (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m{1}.`2.`1 \/
  (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
 real_ke_real_term_metric
 {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
   real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
   real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 not_done{2} /\ not_done0{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          m{2} r{1}.
inline SMCSec1Bridge_Left(KERS.KERealSimp).rest.
sp 0 4.
sim; smt().
transitivity{2}
{r <@ SMCSec1Bridge_TopRight(KERS.KERealSimp).rest(m, r);}
(={m, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
  (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m{1}.`2.`1 \/
  (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
  real_ke_real_term_metric
  {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
    real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
    real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
    real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m, r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done0{2} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          MI.adv{2} (MI.func{1} ++ [2]) MI.in_guard{2} m{2} r{2}.
exlim
  (real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|}) => met.
have [IH_first _] := IH.
call IH_first.
auto.
inline SMCSec1Bridge_TopRight(KERS.KERealSimp).rest.
sp 4 0.
sim; smt().
(* end of use of part 1 of induction *)
rcondf{2} 4; first auto.
case ((oget r{1}).`2.`1 <> MI.adv{1} \/ (oget r{1}).`2.`2 = 0).
rcondt{2} 4; first auto.
rcondf{2} 6; first auto.
rcondf{2} 8; first auto.
rcondf{2} 9; first auto.
rcondt{2} 9; first auto.
rcondf{2} 10; first auto.
rcondt{2} 10; first auto.
rcondf{2} 11; first auto.
wp.
if{1}.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
auto.
rcondt{1} 1; first auto; smt().
rcondf{1} 2; first auto.
rcondf{1} 2; first auto.
rcondf{1} 5; first auto; smt().
rcondf{1} 5; first auto.
rcondt{1} 5; first auto.
rcondf{1} 7; first auto.
auto.
rcondf{1} 1; first auto.
move => |> &hr _ _ _ _ _ ep _.
case (r2{m}) => // msg.
case msg => mod pt1 pt2 u.
case pt1 => addr1 n1 /= _.
rewrite not_dir negb_or /=.
smt(inc_nle_l).
rcondf{2} 4; first auto.
rcondt{1} 1; first auto; smt().
rcondf{1} 2; first auto.
rcondf{1} 2; first auto.
rcondf{1} 5; first auto; smt().
rcondf{1} 5; first auto.
rcondf{1} 5; first auto.
sp 4 3.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
rcondf{1} 3; first auto; smt().
rcondf{2} 3; first auto; smt().
sp 2 2.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ not_done0{2} /\ not_done1{2} /\
   r{1} = r2{2} /\
   ={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\
   (r{1} = None \/
    real_ke_real_term_metric
    {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
      real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
      real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
      real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n)).
call (_ : true).
auto; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondf{2} 4; first auto.
rcondf{2} 5; first auto.
rcondt{2} 5; first auto.
rcondf{2} 6; first auto.
rcondt{2} 6; first auto.
rcondf{2} 7; first auto.
auto.
sp 3 3.
if; first smt().
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondf{2} 5; first auto.
rcondf{2} 6; first auto.
rcondt{2} 6; first auto.
rcondf{2} 7; first auto.
rcondt{2} 7; first auto.
rcondf{2} 8; first auto.
auto.
case (MI.func{1} ++ [2] <= (oget r{1}).`2.`1).
rcondf{1} 1; first auto; smt(le_trans le_ext_r).
rcondf{2} 1; first auto; smt().
rcondt{1} 1; first auto.
rcondt{1} 3; first auto; smt(le_trans le_ext_r).
inline{1} (1) SMCReal(KERS.KERealSimp).invoke.
rcondt{1} 7; first auto.
move => |> &hr <-; by rewrite negb_or not_dir.
inline{1} (1) SMCReal(KERS.KERealSimp).loop.
sp 9 0.
conseq
  (_ :
   not_done{1} /\ not_done1{1} /\ not_done{2} /\ not_done0{2} /\ not_done1{2} /\
   ={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   m1{1} = m2{2} /\
   m1{1}.`1 = Adv /\ MI.func{1} ++ [2] <= m1{1}.`2.`1 /\
   real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _).
move => &1 &2 />. rewrite negb_or not_dir /#.
(* use part 2 of induction: *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KERS.KERealSimp).rest(m1, r1);}
(={m1, r1, glob MI, glob SMCReal, glob KERS.KERealSimp,
   glob Adv} /\
 not_done{1} /\ not_done1{1} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob Adv})
(={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 m1{1} = m2{2} /\
 m1{1}.`1 = Adv /\ MI.func{1} ++ [2] <= m1{1}.`2.`1 /\
 real_ke_real_term_metric
 {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
   real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
   real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 not_done{2} /\ not_done0{2} /\ not_done1{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          m2{2} r1{1}.
inline SMCSec1Bridge_Left(KERS.KERealSimp).rest.
sp 0 4.
seq 3 1 :
  (={glob MI, glob SMCReal, glob KERS.KERealSimp,
     glob Adv} /\
   r{1} = r2{2} /\ not_done{1} = not_done2{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
transitivity{2}
{r <@ SMCSec1Bridge_BotRightKE(KERS.KERealSimp).rest(m2, r2);}
(={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 m1{1} = m2{2} /\
 m1{1}.`1 = UCCore'.Adv /\ MI.func{1} ++ [2] <= m1{1}.`2.`1 /\
 real_ke_real_term_metric
 {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
   real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
   real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m2, r2, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done0{2} /\ not_done1{2} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} MI.adv{2} (MI.func{1} ++ [2])
          MI.in_guard{2} m2{2} r2{2}.
exlim
  (real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|}) => met.
have [_ [IH_second _]] := IH.
call IH_second.
auto.
inline SMCSec1Bridge_BotRightKE(KERS.KERealSimp).rest.
sp 5 0.
seq 1 3 :
  (={glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv,
     glob Adv} /\
   r3{1} = r0{2} /\ not_done00{1} = not_done1{2} /\
   not_done10{1} = not_done0{2} /\ not_done2{1} = not_done{2}).
sim; smt().
seq 1 2 :
  (={glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv,
     glob Adv} /\
   r3{1} = r{2} /\ not_done00{1} = not_done1{2} /\
   not_done10{1} = not_done0{2} /\ not_done2{1} = not_done{2}).
sim.
if => //.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondt{1} 3; first auto.
rcondt{2} 3; first auto.
rcondf{1} 4; first auto.
rcondf{2} 4; first auto.
auto.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
sp 1 1.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
sim.
(* end of use of part 2 of induction *)
rcondt{2} 1; first auto; smt().
rcondf{2} 2; first auto.
rcondt{2} 4; first auto.
rcondt{2} 7; first auto.
move => |> &hr <-; by rewrite negb_or not_dir.
rcondf{2} 10; first auto => |> &hr <-; progress; smt(incP).
rcondt{2} 10; first auto => |> &hr <-; rewrite /=; smt(incP).
rcondf{2} 11; first auto.
rcondf{2} 11; first auto.
rcondf{2} 14; first auto => |> &hr <-; rewrite /=; smt(incP).
rcondf{2} 14; first auto.
rcondf{2} 14; first auto.
rcondt{2} 14; first auto.
rcondf{2} 16; first auto => |> &hr <-; rewrite /=; smt(incP).
inline{2} (1) CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubAdv.invoke.
rcondt{2} 17; first auto.
rcondf{2} 20; first auto.
rcondf{2} 23; first auto => |> &hr <- /#.
sp 0 22.
if; first auto => |> &1 &2 _ _ <- //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto; progress; by rewrite some_oget.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
sp 2 2.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto => |> &hr _ _ <- //.
inline{1} (1) SMCReal(KERS.KERealSimp).invoke.
inline{2} (1) SMCReal(CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubKE).invoke.
sp 4 4.
if.
auto => |> &1 &2 _ _ <- //.
inline{1} (1) SMCReal(KERS.KERealSimp).loop.
inline{2} (1) SMCReal(CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubKE).loop.
sp 3 3.
conseq
  (_ :
   not_done{1} /\ not_done1{1} /\ not_done{2} /\ not_done2{2} /\
   ={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   m1{1} = m5{2} /\
   (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = MI.func{1} /\
    (m1{1}.`2.`2 = 1 \/ m1{1}.`2.`2 = 2 \/ m1{1}.`2.`2 = 3 \/ m1{1}.`2.`2 = 4) \/
    MI.func{1} ++ [1] <= m1{1}.`2.`1 \/
    (m1{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m1{1}.`2.`1)) /\
   real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _).
move => &1 &2 /> _ _ <- [#] -> -> -> -> -> /#.
(* use part 1 of induction *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KERS.KERealSimp).rest(m1, r1);}
(={m1, r1, glob MI, glob SMCReal, glob KERS.KERealSimp,
   glob Adv} /\
 not_done{1} /\ not_done1{1} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob Adv})
(={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 m1{1} = m5{2} /\
 (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = MI.func{1} /\
  (m1{1}.`2.`2 = 1 \/ m1{1}.`2.`2 = 2 \/ m1{1}.`2.`2 = 3 \/ m1{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m1{1}.`2.`1 \/
  (m1{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m1{1}.`2.`1)) /\
 real_ke_real_term_metric
 {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
   real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
   real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 not_done{2} /\ not_done2{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} m5{2} r1{1}.
inline SMCSec1Bridge_Left(KERS.KERealSimp).rest.
sp 0 4.
seq 3 1 :
  (={glob MI, glob SMCReal, glob KERS.KERealSimp,
     glob Adv} /\
   r{1} = r2{2} /\ not_done{1} = not_done2{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim; smt().
transitivity{2}
{r <@ SMCSec1Bridge_TopRight(KERS.KERealSimp).rest(m5, r5);}
(={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 m1{1} = m5{2} /\
 (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = MI.func{1} /\
  (m1{1}.`2.`2 = 1 \/ m1{1}.`2.`2 = 2 \/ m1{1}.`2.`2 = 3 \/ m1{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m1{1}.`2.`1 \/
  (m1{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m1{1}.`2.`1)) /\
  real_ke_real_term_metric
  {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
    real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
    real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
    real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m5, r5, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done2{2} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} MI.adv{2} (MI.func{1} ++ [2])
          MI.in_guard{2} m5{2} r5{2}.
exlim
  (real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|}) => met.
have [IH_first _] := IH.
call IH_first.
auto.
inline SMCSec1Bridge_TopRight(KERS.KERealSimp).rest.
sp 4 0.
seq 1 3 :
  (={glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv,
     glob Adv} /\
   r6{1} = r{2} /\ not_done3{1} = not_done{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
(* end of use of part 1 of induction *)
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
(* SMCSec1Bridge_Left(KERS.KERealSimp).rest ~
   SMCSec1Bridge_BotRightKE(KERS.KERealSimp).rest *)
proc.
rcondt{1} 3; first auto.
rcondt{2} 4; first auto.
rcondt{2} 6; first auto.
rcondf{1} 3; first auto; smt(not_le_ext_nonnil_l).
rcondf{1} 3; first auto; smt(not_le_ext_nonnil_l).
rcondf{1} 3; first auto; smt(not_le_other_branch).
sp 2 5.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done1{2} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\
   (r{1} = None \/
    real_ke_real_term_metric
    {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
      real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
      real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
      real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n)).
exlim (KERS.ke_real_simp_term_metric KERS.KERealSimp.st{1}) => ke_met.
call (KERS.ke_real_simp_term_invoke ke_met).
auto; smt(real_ke_real_term_metric0 KERS.ge0_ke_real_simp_term_metric).
case (r{1} = None).
rcondf{1} 1; first auto.
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{2} 1; first auto.
rcondf{2} 2; first auto.
rcondf{2} 2; first auto.
rcondf{2} 2; first auto.
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
rcondt{2} 3; first auto.
rcondf{2} 4; first auto.
auto.
rcondf{2} 1; first auto.
case (MI.func{1} ++ [2] <= (oget r{1}).`2.`1).
rcondt{1} 1; first auto; smt(not_le_ext_nonnil_l le_trans le_ext_r).
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
rcondt{2} 4; first auto. 
rcondf{2} 6; first auto.
rcondf{2} 6; first auto.
rcondf{2} 6; first auto.
rcondt{2} 6; first auto.
rcondf{2} 7; first auto.
rcondt{2} 7; first auto.
rcondf{2} 8; first auto.
auto.
rcondf{2} 4; first auto.
case ((oget r{1}).`1 = Dir).
rcondt{2} 4; first auto.
case (MI.adv{1} <= (oget r{1}).`2.`1).
rcondt{2} 5; first auto.
rcondf{2} 6; first auto.
rcondf{2} 6; first auto.
rcondf{2} 6; first auto.
rcondt{2} 6; first auto.
rcondf{2} 7; first auto.
rcondt{2} 7; first auto.
rcondf{2} 8; first auto.
rcondt{1} 1; first auto; smt(incP not_dir not_le_ext_nonnil_l).
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
auto.
rcondf{2} 5; first auto.
rcondf{2} 5; first auto.
rcondt{2} 5; first auto.
rcondf{2} 8; first auto; smt().
sp 0 7.
if => //.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondt{1} 3; first auto.
rcondt{2} 3; first auto.
rcondf{1} 4; first auto.
rcondf{2} 4; first auto.
auto.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
sp 4 4.
rcondf{1} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondt{1} 1; first auto; smt().
rcondt{2} 1; first auto; smt().
sp 1 1.
rcondf{1} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{1} 1; first auto.
rcondf{2} 1; first auto.
auto.
sp 1 1.
conseq
  (_ :
   not_done{1} /\ not_done0{1} /\ not_done{2} /\ not_done1{2} /\
   ={m, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
    (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
    MI.func{1} ++ [1] <= m{1}.`2.`1 \/
    (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
   real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _); first smt().
(* use part 1 of induction *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KERS.KERealSimp).rest(m, r);}
(={m, r, glob MI, glob SMCReal, glob KERS.KERealSimp,
   glob Adv} /\
 not_done{1} /\ not_done0{1} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob Adv})
(={m, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
  (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m{1}.`2.`1 \/
  (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
 real_ke_real_term_metric
 {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
   real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
   real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 not_done{2} /\ not_done1{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} m{2} r{1}.
inline SMCSec1Bridge_Left(KERS.KERealSimp).rest.
sp 0 4.
sim; smt().
transitivity{2}
{r <@ SMCSec1Bridge_TopRight(KERS.KERealSimp).rest(m, r);}
(={m, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
  (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m{1}.`2.`1 \/
  (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
  real_ke_real_term_metric
  {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
    real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
    real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
    real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m, r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done1{2} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          MI.adv{2} (MI.func{1} ++ [2]) MI.in_guard{2} m{2} r{2}.
exlim
  (real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|}) => met.
have [IH_first _] := IH.
call IH_first.
auto.
inline SMCSec1Bridge_TopRight(KERS.KERealSimp).rest.
sp 4 0.
sim; smt().
(* end of use of part 1 of induction *)
rcondf{2} 4; first auto.
case ((oget r{1}).`2.`1 <> MI.adv{1} \/ (oget r{1}).`2.`2 = 0).
rcondt{2} 4; first auto.
rcondf{2} 6; first auto.
rcondf{2} 6; first auto.
rcondf{2} 6; first auto.
rcondt{2} 6; first auto.
rcondf{2} 7; first auto.
rcondt{2} 7; first auto.
rcondf{2} 8; first auto.
if{1}.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
auto.
rcondt{1} 1; first auto; smt().
rcondf{1} 2; first auto.
rcondf{1} 2; first auto.
rcondf{1} 5; first auto; smt().
rcondf{1} 5; first auto.
rcondt{1} 5; first auto.
rcondf{1} 7; first auto.
auto.
rcondf{2} 4; first auto.
rcondt{2} 4; first auto.
rcondf{2} 6; first auto.
rcondf{1} 1; first auto.
move => /> &hr; case (r{m}) => // [[]] ? [] ? ? ? ?.
rewrite not_dir negb_or /=.
smt(inc_nle_l).
rcondt{1} 1; first auto; smt().
rcondf{1} 2; first auto.
rcondf{1} 2; first auto.
rcondf{1} 5; first auto; smt().
rcondf{1} 5; first auto.
rcondf{1} 5; first auto.
rcondt{1} 5; first auto.
rcondf{1} 7; first auto; smt().
sp 6 5.
seq 1 1 :
  (!not_done0{1} /\ not_done{1} /\ not_done{2} /\
   not_done1{2} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\
   real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n).
call (_ : true).
auto; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondf{2} 2; first auto.
rcondf{2} 2; first auto.
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
rcondt{2} 3; first auto.
rcondf{2} 4; first auto.
auto.
sp 3 3.
if; first smt().
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondf{2} 3; first auto.
rcondf{2} 3; first auto.
rcondt{2} 3; first auto.
rcondf{2} 4; first auto.
rcondt{2} 4; first auto.
rcondf{2} 5; first auto.
auto.
case (MI.func{1} ++ [2] <= (oget r{1}).`2.`1).
rcondf{2} 1; first auto; smt().
rcondf{1} 1; first auto; smt(le_ext_r le_trans).
rcondt{1} 1; first auto.
rcondt{1} 3; first auto; smt(le_ext_r le_trans).
inline{1} (1) SMCReal(KERS.KERealSimp).invoke.
rcondt{1} 7; first auto.
move => |> &hr <- [#] -> -> /=.
by rewrite negb_or not_dir.
inline{1} (1) SMCReal(KERS.KERealSimp).loop.
sp 9 0.
conseq
  (_ :
   not_done{1} /\ not_done1{1} /\ not_done{2} /\ not_done0{2} /\ not_done1{2} /\
   ={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   m1{1} = m{2} /\
   m1{1}.`1 = Adv /\ MI.func{1} ++ [2] <= m1{1}.`2.`1 /\
   real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _).
move => &1 &2 />. rewrite negb_or not_dir /#.
(* use part 2 of induction: *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KERS.KERealSimp).rest(m1, r1);}
(={m1, r1, glob MI, glob SMCReal, glob KERS.KERealSimp,
   glob Adv} /\
 not_done{1} /\ not_done1{1} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob Adv})
(={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 m1{1} = m{2} /\
 m1{1}.`1 = Adv /\ MI.func{1} ++ [2] <= m1{1}.`2.`1 /\
 real_ke_real_term_metric
 {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
   real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
   real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 not_done{2} /\ not_done0{2} /\ not_done1{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} m{2} r1{1}.
inline SMCSec1Bridge_Left(KERS.KERealSimp).rest.
sp 0 4.
seq 3 1 :
  (={glob MI, glob SMCReal, glob KERS.KERealSimp,
     glob Adv} /\
   r{1} = r2{2} /\ not_done{1} = not_done2{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
transitivity{2}
{r <@ SMCSec1Bridge_BotRightKE(KERS.KERealSimp).rest(m, r);}
(={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 m1{1} = m{2} /\
 m1{1}.`1 = UCCore'.Adv /\ MI.func{1} ++ [2] <= m1{1}.`2.`1 /\
 real_ke_real_term_metric
 {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
   real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
   real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m, r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done0{2} /\ not_done1{2} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} MI.adv{2} (MI.func{1} ++ [2])
          MI.in_guard{2} m{2} r{2}.
exlim
  (real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|}) => met.
have [_ [IH_second _]] := IH.
call IH_second.
auto.
inline SMCSec1Bridge_BotRightKE(KERS.KERealSimp).rest.
sp 5 0.
seq 1 1 :
  (={glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv,
     glob Adv} /\
   r0{1} = r{2} /\ not_done00{1} = not_done0{2} /\
   not_done10{1} = not_done1{2} /\ not_done2{1} = not_done{2}).
sim; smt().
if => //.
sim.
rcondf{1} 1; first auto.
rcondf{2} 1; first auto.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
(* end of use of part 2 of induction *)
rcondt{2} 1; first auto; smt().
rcondf{2} 2; first auto.
rcondt{2} 2; first auto.
rcondt{2} 5; first auto.
move => &hr /> <- [#] -> /=.
by rewrite negb_or not_dir.
rcondf{2} 7; first auto.
move => &hr /> <- [#] -> -> /=; smt(incP).
rcondt{2} 7; first auto.
move => &hr /> <- [#] -> ->.
rewrite /=; smt(incP).
rcondf{2} 8; first auto.
rcondf{2} 8; first auto.
sp 0 10.
rcondf{2} 1; first auto.
move => &hr />; smt(inc_nle_l).
rcondf{2} 1; first auto.
rcondf{2} 1; first auto.
rcondt{2} 1; first auto.
rcondf{2} 3; first auto.
move => &hr />.
rewrite /=; smt(inc_nle_l).
inline{2} (1) CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubAdv.invoke.
rcondt{2} 4; first auto.
rcondf{2} 7; first auto.
sp 0 9.
rcondf{2} 1; first auto.
move => &hr />; move => <- //.
if; first auto => &1 &2 /> <- //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto; progress; by rewrite some_oget.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
sp 2 2.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
move => &hr /> <- //.
inline{1} (1) SMCReal(KERS.KERealSimp).invoke.
inline{2} (1) SMCReal(CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubKE).invoke.
sp 4 4.
if; first auto => &1 &2 /> <- //.
inline{1} (1) SMCReal(KERS.KERealSimp).loop.
inline{2} (1) SMCReal(CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubKE).loop.
sp 3 3.
conseq
  (_ :
   not_done{1} /\ not_done1{1} /\ not_done{2} /\ not_done2{2} /\
   ={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   m1{1} = m2{2} /\
   (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = MI.func{1} /\
    (m1{1}.`2.`2 = 1 \/ m1{1}.`2.`2 = 2 \/ m1{1}.`2.`2 = 3 \/ m1{1}.`2.`2 = 4) \/
    MI.func{1} ++ [1] <= m1{1}.`2.`1 \/
    (m1{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m1{1}.`2.`1)) /\
   real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _).
move => &1 &2 /> /= /#.
(* use part 1 of induction *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KERS.KERealSimp).rest(m1, r1);}
(={m1, r1, glob MI, glob SMCReal, glob KERS.KERealSimp,
   glob Adv} /\
 not_done{1} /\ not_done1{1} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob Adv})
(={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 m1{1} = m2{2} /\
 (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = MI.func{1} /\
  (m1{1}.`2.`2 = 1 \/ m1{1}.`2.`2 = 2 \/ m1{1}.`2.`2 = 3 \/ m1{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m1{1}.`2.`1 \/
  (m1{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m1{1}.`2.`1)) /\
 real_ke_real_term_metric
 {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
   real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
   real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 not_done{2} /\ not_done2{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} m2{2} r1{1}.
inline SMCSec1Bridge_Left(KERS.KERealSimp).rest.
sp 0 4.
seq 3 1 :
  (={glob MI, glob SMCReal, glob KERS.KERealSimp,
     glob Adv} /\
   r{1} = r2{2} /\ not_done{1} = not_done2{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim; smt().
transitivity{2}
{r <@ SMCSec1Bridge_TopRight(KERS.KERealSimp).rest(m2, r2);}
(={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 m1{1} = m2{2} /\
 (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = MI.func{1} /\
  (m1{1}.`2.`2 = 1 \/ m1{1}.`2.`2 = 2 \/ m1{1}.`2.`2 = 3 \/ m1{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m1{1}.`2.`1 \/
  (m1{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m1{1}.`2.`1)) /\
  real_ke_real_term_metric
  {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
    real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
    real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
    real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m2, r2, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done2{2} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          MI.adv{2} (MI.func{1} ++ [2]) MI.in_guard{2} m2{2} r2{2}.
exlim
  (real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|}) => met.
have [IH_first _] := IH.
call IH_first.
auto.
inline SMCSec1Bridge_TopRight(KERS.KERealSimp).rest.
sp 4 0.
seq 1 3 :
  (={glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv,
     glob Adv} /\
   r3{1} = r{2} /\ not_done3{1} = not_done{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
(* end of use of part 1 of induction *)
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
(* SMCSec1Bridge_Left(KERS.KERealSimp).rest ~
   SMCSec1Bridge_BotRightAdv(KERS.KERealSimp).rest *)
proc.
rcondt{1} 3; first auto.
rcondt{2} 3; first auto.
rcondt{2} 5; first auto.
rcondf{1} 3; first auto; smt(not_le_ext_nonnil_l).
rcondf{1} 3; first auto; smt(not_le_ext_nonnil_l).
rcondf{1} 3; first auto; smt(not_le_other_branch).
sp 2 4.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\
   (r{1} = None \/
    real_ke_real_term_metric
    {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
      real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
      real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
      real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n)).
exlim (KERS.ke_real_simp_term_metric KERS.KERealSimp.st{1}) => ke_met.
call (KERS.ke_real_simp_term_invoke ke_met).
auto; smt(real_ke_real_term_metric0 KERS.ge0_ke_real_simp_term_metric).
case (r{1} = None).
rcondf{1} 1; first auto.
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{2} 1; first auto.
rcondf{2} 2; first auto.
rcondf{2} 2; first auto.
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
auto.
rcondf{2} 1; first auto.
case (MI.func{1} ++ [2] <= (oget r{1}).`2.`1).
rcondt{1} 1; first auto; smt(not_le_ext_nonnil_l le_trans le_ext_r).
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
rcondt{2} 4; first auto. 
rcondf{2} 6; first auto.
rcondf{2} 6; first auto.
rcondt{2} 6; first auto.
rcondf{2} 7; first auto.
auto.
rcondf{2} 4; first auto.
case ((oget r{1}).`1 = Dir).
rcondt{2} 4; first auto.
case (MI.adv{1} <= (oget r{1}).`2.`1).
rcondt{2} 5; first auto.
rcondf{2} 6; first auto.
rcondf{2} 6; first auto.
rcondt{2} 6; first auto.
rcondf{2} 7; first auto.
rcondt{1} 1; first auto; smt(incP not_dir not_le_ext_nonnil_l).
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
auto.
rcondf{2} 5; first auto.
rcondf{2} 5; first auto.
rcondt{2} 5; first auto.
rcondt{2} 8; first auto.
rcondf{2} 10; first auto.
rcondf{2} 13; first auto.
move => &hr /> /=.
smt(inc_le1_not_rl le_ext_r).
rcondf{2} 13; first auto.
move => &hr /> /=.
smt(inc_le1_not_rl le_ext_r).
rcondt{2} 13; first auto.
rcondt{2} 15; first auto.
move => &hr /> /=.
smt(inc_le1_not_rl le_ext_r).
inline{2} (1) SMCReal(CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubKE).invoke.
rcondt{2} 19; first auto.
move => &hr />; smt(le_refl).
inline{2} (1) SMCReal(CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubKE).loop.
rcondt{2} 22; first auto.
rcondf{2} 22; first auto.
move => &hr /> /=.
smt(ne_cat_nonnil_r).
rcondf{2} 22; first auto.
rcondf{2} 22; first auto.
move => &hr /> /=.
rewrite (not_le_other_branch MI.func{m} (MI.func{m} ++ [2]) 2 1) // le_refl.
inline{2} (1) CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubKE.invoke.
rcondt{2} 23; first auto.
sp 0 25.
if; first auto => &1 &2 />.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
rcondt{2} 5; first auto.
rcondf{2} 6; first auto.
auto.
rcondf{1} 1; first auto; smt(le_refl).
rcondf{2} 1; first auto.
move => &hr />; smt(le_refl).
sp 1 1.
conseq
  (_ :
   not_done{1} /\ not_done0{1} /\ not_done{2} /\ not_done1{2} /\
   ={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   m{1} = m1{2} /\
   (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
    (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
    MI.func{1} ++ [1] <= m{1}.`2.`1 \/
    (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
   real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _).
move => &1 &2 />; smt().
(* use part 1 of induction *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KERS.KERealSimp).rest(m, r);}
(={m, r, glob MI, glob SMCReal, glob KERS.KERealSimp,
   glob Adv} /\
 not_done{1} /\ not_done0{1} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob Adv})
(={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 m{1} = m1{2} /\
 (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
  (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m{1}.`2.`1 \/
  (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
 real_ke_real_term_metric
 {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
   real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
   real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 not_done{2} /\ not_done1{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          m1{2} r{1}.
inline SMCSec1Bridge_Left(KERS.KERealSimp).rest.
sp 0 4.
sim; smt().
transitivity{2}
{r <@ SMCSec1Bridge_TopRight(KERS.KERealSimp).rest(m1, r1);}
(={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 m{1} = m1{2} /\
 (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
  (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m{1}.`2.`1 \/
  (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
  real_ke_real_term_metric
  {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
    real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
    real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
    real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m1, r1, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done1{2} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} MI.adv{2} (MI.func{1} ++ [2])
          MI.in_guard{2} m1{2} r1{2}.
exlim
  (real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|}) => met.
have [IH_first _] := IH.
call IH_first.
auto.
inline SMCSec1Bridge_TopRight(KERS.KERealSimp).rest.
sp 4 0.
seq 1 3 :
  (={glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv,
     glob Adv} /\
   r3{1} = r{2} /\ not_done2{1} = not_done{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
(* end of use of part 1 of induction *)
rcondf{2} 4; first auto.
case ((oget r{1}).`2.`1 <> MI.adv{1} \/ (oget r{1}).`2.`2 = 0).
rcondt{2} 4; first auto.
rcondf{2} 6; first auto.
rcondf{2} 6; first auto.
rcondt{2} 6; first auto.
rcondf{2} 7; first auto.
if{1}.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
auto.
rcondt{1} 1; first auto; smt().
rcondf{1} 2; first auto.
rcondf{1} 2; first auto.
rcondf{1} 5; first auto; smt().
rcondf{1} 5; first auto.
rcondt{1} 5; first auto.
rcondf{1} 7; first auto.
auto.
rcondf{2} 4; first auto.
rcondt{2} 4; first auto.
rcondf{2} 6; first auto.
rcondf{1} 1; first auto.
move => /> &hr; case (r{m}) => // [[]] ? [] ? ? ? ?.
rewrite not_dir negb_or /=.
smt(inc_nle_l).
rcondt{1} 1; first auto; smt().
rcondf{1} 2; first auto.
rcondf{1} 2; first auto.
rcondf{1} 5; first auto; smt().
rcondf{1} 5; first auto.
rcondf{1} 5; first auto.
rcondt{1} 5; first auto.
rcondf{1} 7; first auto; smt().
sp 6 5.
seq 1 1 :
  (!not_done0{1} /\ not_done{1} /\ not_done{2} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\
   real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n).
call (_ : true).
auto; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondf{2} 2; first auto.
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
auto.
sp 3 3.
if; first smt().
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondf{2} 3; first auto.
rcondt{2} 3; first auto.
rcondf{2} 4; first auto.
auto.
case (MI.func{1} ++ [2] <= (oget r{1}).`2.`1).
rcondf{2} 1; first auto; smt().
rcondf{1} 1; first auto; smt(le_ext_r le_trans).
rcondt{1} 1; first auto.
rcondt{1} 3; first auto; smt(le_ext_r le_trans).
inline{1} (1) SMCReal(KERS.KERealSimp).invoke.
rcondt{1} 7; first auto.
move => |> &hr <- [#] -> -> /=.
by rewrite negb_or not_dir.
inline{1} (1) SMCReal(KERS.KERealSimp).loop.
sp 9 0.
conseq
  (_ :
   not_done{1} /\ not_done1{1} = true /\ not_done{2} /\ not_done0{2} /\
   ={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   m1{1} = m{2} /\
   m1{1}.`1 = Adv /\ MI.func{1} ++ [2] <= m1{1}.`2.`1 /\
   real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _).
move => &1 &2 />. rewrite negb_or not_dir /#.
(* use part 3 of induction: *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KERS.KERealSimp).rest(m1, r1);}
(={m1, r1, glob MI, glob SMCReal, glob KERS.KERealSimp,
   glob Adv} /\
 not_done{1} /\ not_done1{1} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob Adv})
(={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 m1{1} = m{2} /\
 m1{1}.`1 = Adv /\ MI.func{1} ++ [2] <= m1{1}.`2.`1 /\
 real_ke_real_term_metric
 {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
   real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
   real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 not_done{2} /\ not_done0{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          m{2} r1{1}.
inline SMCSec1Bridge_Left(KERS.KERealSimp).rest.
sp 0 4.
seq 3 1 :
  (={glob MI, glob SMCReal, glob KERS.KERealSimp,
     glob Adv} /\
   r{1} = r2{2} /\ not_done{1} = not_done2{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
transitivity{2}
{r <@ SMCSec1Bridge_BotRightAdv(KERS.KERealSimp).rest(m, r);}
(={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 m1{1} = m{2} /\
 m1{1}.`1 = UCCore'.Adv /\ MI.func{1} ++ [2] <= m1{1}.`2.`1 /\
 real_ke_real_term_metric
 {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
   real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
   real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m, r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done0{2} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          MI.adv{2} (MI.func{1} ++ [2]) MI.in_guard{2} m{2} r{2}.
exlim
  (real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|}) => met.
have [_ [_ IH_third]] := IH.
call IH_third.
auto.
inline SMCSec1Bridge_BotRightAdv(KERS.KERealSimp).rest.
sp 4 0.
seq 2 2 :
  (={glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv,
     glob Adv} /\
   r0{1} = r{2} /\ not_done00{1} = not_done0{2} /\ not_done1{1} = not_done{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
(* end of use of part 3 of induction *)
rcondt{2} 1; first auto; smt().
rcondf{2} 2; first auto.
rcondt{2} 2; first auto.
rcondf{2} 5; first auto; smt().
rcondf{2} 5; first auto.
rcondf{2} 8; first auto; smt().
sp 0 7.
if; first smt().
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
rcondt{1} 3; first auto; smt().
rcondt{2} 3; first auto; smt().
sp 2 2.
inline{1} (1) SMCReal(KERS.KERealSimp).invoke.
inline{2} (1) SMCReal(CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubKE).invoke.
sp 4 4.
if; first smt().
inline{1} (1) SMCReal(KERS.KERealSimp).loop.
inline{2} (1) SMCReal(CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubKE).loop.
sp 3 3.
conseq
  (_ :
   not_done{1} /\ not_done1{1} /\ not_done{2} /\ not_done1{2} /\
   ={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   m1{1} = m1{2} /\
   (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = MI.func{1} /\
    (m1{1}.`2.`2 = 1 \/ m1{1}.`2.`2 = 2 \/ m1{1}.`2.`2 = 3 \/ m1{1}.`2.`2 = 4) \/
    MI.func{1} ++ [1] <= m1{1}.`2.`1 \/
    (m1{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m1{1}.`2.`1)) /\
   real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _); first smt().
(* use part 1 of induction *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KERS.KERealSimp).rest(m1, r1);}
(={m1, r1, glob MI, glob SMCReal, glob KERS.KERealSimp,
   glob Adv} /\
 not_done{1} /\ not_done1{1} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob Adv})
(={m1, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = MI.func{1} /\
  (m1{1}.`2.`2 = 1 \/ m1{1}.`2.`2 = 2 \/ m1{1}.`2.`2 = 3 \/ m1{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m1{1}.`2.`1 \/
  (m1{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m1{1}.`2.`1)) /\
 real_ke_real_term_metric
 {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
   real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
   real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 not_done{2} /\ not_done1{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          m1{2} r1{1}.
inline SMCSec1Bridge_Left(KERS.KERealSimp).rest.
sp 0 4.
seq 3 1 :
  (={glob MI, glob SMCReal, glob KERS.KERealSimp,
     glob Adv} /\
   r{1} = r2{2} /\ not_done{1} = not_done2{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim; smt().
transitivity{2}
{r <@ SMCSec1Bridge_TopRight(KERS.KERealSimp).rest(m1, r1);}
(={m1, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = MI.func{1} /\
  (m1{1}.`2.`2 = 1 \/ m1{1}.`2.`2 = 2 \/ m1{1}.`2.`2 = 3 \/ m1{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m1{1}.`2.`1 \/
  (m1{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m1{1}.`2.`1)) /\
  real_ke_real_term_metric
  {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
    real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
    real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
    real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m1, r1, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done1{2} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          MI.adv{2} (MI.func{1} ++ [2]) MI.in_guard{2} m1{2} r1{2}.
exlim
  (real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|}) => met.
have [IH_first _] := IH.
call IH_first.
auto.
inline SMCSec1Bridge_TopRight(KERS.KERealSimp).rest.
sp 4 0.
seq 1 3 :
  (={glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv,
     glob Adv} /\
   r2{1} = r{2} /\ not_done2{1} = not_done{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim; smt().
(* end of use of part 1 of induction *)
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
qed.

local lemma smc_sec1_ke_real_simp_bridge_invoke :
  equiv
  [MI(SMCReal(KERS.KERealSimp), Adv).invoke ~
   MakeInt'.MI
   (SMCReal(CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubKE),
    CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubAdv).invoke :
   ={m, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   MakeInt'.MI.in_guard{2} \subset MI.in_guard{2} /\
   adv_fw_pi \in MI.in_guard{2} /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   ={res, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   CompEnv.stub_st{2} = None].
proof.
proc => /=.
sp 2 2.
if => //.
inline MI(SMCReal(KERS.KERealSimp), Adv).loop.
inline MakeInt'.MI
       (SMCReal(CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubKE),
        CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubAdv).loop.
sp 3 3.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
sp 2 2.
if => //.
inline{1} (1) SMCReal(KERS.KERealSimp).invoke.
inline{2} (1) SMCReal(CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubKE).invoke.
sp 4 4.
if => //.
inline{1} (1) SMCReal(KERS.KERealSimp).loop.
inline{2} (1) SMCReal(CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubKE).loop.
sp 3 3.
transitivity{1}
{r <@ SMCSec1Bridge_Left(KERS.KERealSimp).rest(m2, r2);}
(={m2, r2, glob MI, glob SMCReal, glob KERS.KERealSimp,
   glob Adv} /\
 not_done{1} /\ not_done0{1} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob Adv})
(={m2, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 (m2{1}.`1 = Dir /\ m2{1}.`2.`1 = MI.func{1} /\
  (m2{1}.`2.`2 = 1 \/ m2{1}.`2.`2 = 2 \/ m2{1}.`2.`2 = 3 \/ m2{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m2{1}.`2.`1 \/
  (m2{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m2{1}.`2.`1)) /\
 not_done{2} /\ not_done0{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 MakeInt'.MI.in_guard{2} \subset MI.in_guard{2} /\
 adv_fw_pi \in MI.in_guard{2} /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
       SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
       Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
       KERS.KERealSimp.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
       (mod1{2}, (addr11{2}, n11{2}), pt21{2}, u1{2}) None.
progress; smt(not_dir).
inline SMCSec1Bridge_Left(KERS.KERealSimp).rest.
sp 0 4.
seq 3 1 :
  (={glob MI, glob SMCReal, glob KERS.KERealSimp,
     glob Adv} /\
   r0{1} = r3{2} /\ not_done{1} = not_done1{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
transitivity{2}
{r <@ SMCSec1Bridge_TopRight(KERS.KERealSimp).rest(m2, r2);}
(={m2, MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 (m2{1}.`1 = Dir /\ m2{1}.`2.`1 = MI.func{1} /\
  (m2{1}.`2.`2 = 1 \/ m2{1}.`2.`2 = 2 \/ m2{1}.`2.`2 = 3 \/ m2{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m2{1}.`2.`1 \/
  (m2{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m2{1}.`2.`1)) /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 MakeInt'.MI.in_guard{2} \subset MI.in_guard{2} /\
 adv_fw_pi \in MI.in_guard{2} /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m2, r2, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done0{2} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} MI.adv{2} (MI.func{1} ++ [2]) MI.in_guard{2}
          m2{2} r2{2}.
exlim
  (real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|}) => met.
have [lem_first _] := smc_sec1_ke_real_simp_bridge_induction met.
call lem_first.
auto.
inline SMCSec1Bridge_TopRight(KERS.KERealSimp).rest.
sp 4 0.
seq 1 3 :
  (={glob MI, glob SMCReal, glob KERS.KERealSimp,
     glob Adv, glob CompEnv, glob MakeInt'.MI} /\
   r3{1} = r0{2} /\ not_done1{1} = not_done{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
inline{2} (1) CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubAdv.invoke.
rcondf{2} 2; first auto.
inline{2} (1) MI(KERS.KERealSimp, Adv).invoke.
rcondt{2} 5; first auto; smt().
inline{2} (1) MI(KERS.KERealSimp, Adv).loop.
rcondt{2} 8; first auto.
rcondf{2} 10; first auto; smt(not_le_ext).
sp 0 9.
seq 1 1 :
  (r0{1} = r3{2} /\ not_done{1} /\ not_done{2} /\ not_done0{2} /\
   ={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   MakeInt'.MI.in_guard{2} \subset MI.in_guard{2} /\
   adv_fw_pi \in MI.in_guard{2} /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None).
call (_ : true).
auto.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondf{2} 4; first auto.
rcondt{2} 5; first auto.
rcondf{2} 6; first auto.
auto.
sp 3 3.
if; first smt().
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondf{2} 5; first auto.
rcondt{2} 6; first auto.
rcondf{2} 7; first auto.
auto.
case (MI.func{2} <= addr13{2}).
rcondf{1} 1; first auto; smt(le_ext_r le_trans).
rcondt{1} 1; first auto.
rcondt{1} 3; first auto; smt(le_ext_r le_trans).
inline{1} (1) SMCReal(KERS.KERealSimp).invoke.
rcondt{1} 7; first auto.
move => |> &hr <- /=; rewrite negb_or not_dir /#.
rcondf{2} 1; first auto.
inline{1} (1) SMCReal(KERS.KERealSimp).loop.
sp 9 0.
transitivity{1}
{r <@ SMCSec1Bridge_Left(KERS.KERealSimp).rest(m2, r2);}
(={m2, r2, glob MI, glob SMCReal, glob KERS.KERealSimp,
   glob Adv} /\
 not_done{1} /\ not_done0{1} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob Adv})
(={ MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 m2{1} = m3{2} /\ oget r3{2} = m3{2} /\
 m2{1}.`1 = Adv /\ MI.func{1} ++ [2] <= m2{1}.`2.`1 /\
 not_done{2} /\ not_done0{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 MakeInt'.MI.in_guard{2} \subset MI.in_guard{2} /\
 adv_fw_pi \in MI.in_guard{2} /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
move => |> &1 &2 <- [#] -> ->; progress.
exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
       SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
       Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
       KERS.KERealSimp.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
       (mod3{2}, (addr13{2}, n13{2}), pt23{2}, u3{2}) None.
progress; rewrite negb_or not_dir in H6; smt().
inline SMCSec1Bridge_Left(KERS.KERealSimp).rest.
sp 0 4.
seq 3 1 :
  (={glob MI, glob SMCReal, glob KERS.KERealSimp,
     glob Adv} /\
   r0{1} = r3{2} /\ not_done{1} = not_done1{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
transitivity{2}
{r <@ SMCSec1Bridge_BotRightAdv(KERS.KERealSimp).rest(m3, r3);}
(={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 m2{1} = m3{2} /\
 m2{1}.`1 = Adv /\ MI.func{1} ++ [2] <= m2{1}.`2.`1 /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 MakeInt'.MI.in_guard{2} \subset MI.in_guard{2} /\
 adv_fw_pi \in MI.in_guard{2} /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv, glob Adv} /\
 ={m3, r3} /\ not_done{2} /\ not_done0{2} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2} None
          MI.adv{2} MI.func{1} SMCReal.st1{2} SMCReal.st2{2}
          Fwd.Forw.adv{2} Fwd.Forw.self{2} Fwd.Forw.st{2}
          KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          MI.adv{2} (MI.func{1} ++ [2]) MI.in_guard{2} (oget r3{2}) r3{2}.
exlim
  (real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|}) => met.
have [_ [_ lem_third]] := smc_sec1_ke_real_simp_bridge_induction met.
call lem_third.
auto.
inline SMCSec1Bridge_BotRightAdv(KERS.KERealSimp).rest.
sp 4 0.
seq 1 3 :
  (={glob MI, glob SMCReal, glob KERS.KERealSimp,
     glob Adv, glob CompEnv, glob MakeInt'.MI} /\
   r4{1} = r1{2} /\ not_done1{1} = not_done{2}).
sim; smt().
seq 1 2 :
  (={glob MI, glob SMCReal, glob KERS.KERealSimp,
     glob Adv, glob CompEnv, glob MakeInt'.MI} /\
   r4{1} = r0{2} /\ not_done1{1} = not_done{2}).
sim.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
rcondt{2} 1; first auto.
rcondf{2} 2; first auto.
rcondt{2} 4; first auto.
rcondf{2} 7; first auto; smt().
rcondf{2} 8; first auto.
rcondf{2} 11; first auto; smt().
sp 0 10.
if; first smt().
rcondf{1} 2; first auto. rcondf{2} 2; first auto.
auto.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
rcondt{1} 3; first auto; smt().
rcondt{2} 3; first auto; smt().
inline{1} (1) SMCReal(KERS.KERealSimp).invoke.
inline{2} (1) SMCReal(CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubKE).invoke.
sp 6 6.
if; first smt().
inline{1} (1) SMCReal(KERS.KERealSimp).loop.
inline{2} (1) SMCReal(CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubKE).loop.
sp 3 3.
transitivity{1}
{r <@ SMCSec1Bridge_Left(KERS.KERealSimp).rest(m2, r2);}
(={m2, r2, glob MI, glob SMCReal, glob KERS.KERealSimp,
   glob Adv} /\
 not_done{1} /\ not_done0{1} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob Adv})
(={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 m2{1} = m5{2} /\
 (m2{1}.`1 = Dir /\ m2{1}.`2.`1 = MI.func{1} /\
  (m2{1}.`2.`2 = 1 \/ m2{1}.`2.`2 = 2 \/ m2{1}.`2.`2 = 3 \/ m2{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m2{1}.`2.`1 \/
  (m2{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m2{1}.`2.`1)) /\
 not_done{2} /\ not_done1{2} /\ r5{2} = None /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
move => |> &1 &2 not_done0_R <- [#] -> -> -> -> ->.
progress.
exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
       SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
       Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
       KERS.KERealSimp.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
       (mod1{2}, (addr11{2}, n11{2}), pt21{2}, u1{2}) None.
progress; smt().
inline SMCSec1Bridge_Left(KERS.KERealSimp).rest.
sp 0 4.
seq 3 1 :
  (={glob MI, glob SMCReal, glob KERS.KERealSimp,
     glob Adv} /\
   r0{1} = r3{2} /\ not_done{1} = not_done1{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
transitivity{2}
{r <@ SMCSec1Bridge_TopRight(KERS.KERealSimp).rest(m5, r5);}
(={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 m2{1} = m5{2} /\
 (m2{1}.`1 = Dir /\ m2{1}.`2.`1 = MI.func{1} /\
  (m2{1}.`2.`2 = 1 \/ m2{1}.`2.`2 = 2 \/ m2{1}.`2.`2 = 3 \/ m2{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m2{1}.`2.`1 \/
  (m2{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m2{1}.`2.`1)) /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv,
   glob Adv} /\
 ={m5, r5} /\ not_done{2} /\ not_done1{2} ==>
 ={r, glob MI, glob SMCReal, glob KERS.KERealSimp, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2} None
          MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KERS.KERealSimp.adv{2} KERS.KERealSimp.self{2}
          KERS.KERealSimp.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} MI.adv{2} (MI.func{1} ++ [2])
          MI.in_guard{2} m5{2} None.
exlim
  (real_ke_real_term_metric
   {|real_ke_real_simp_term_met_st_p1s = SMCReal.st1{1};
     real_ke_real_simp_term_met_st_p2s = SMCReal.st2{1};
     real_ke_real_simp_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_real_simp_term_met_st_kes = KERS.KERealSimp.st{1}|}) => met.
have [lem_first _] := smc_sec1_ke_real_simp_bridge_induction met.
     call lem_first.
auto.
inline SMCSec1Bridge_TopRight(KERS.KERealSimp).rest.
sp 4 0.
seq 1 3 :
  (={glob MI, glob SMCReal, glob KERS.KERealSimp,
     glob Adv, glob CompEnv, glob MakeInt'.MI} /\
   r6{1} = r0{2} /\ not_done2{1} = not_done{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
rcondt{1} 2; first auto. rcondt{2} 2; first auto.
rcondf{1} 3; first auto. rcondf{2} 3; first auto.
auto.
auto.
qed.

local lemma smc_sec1_ke_real_simp_bridge
            (func' adv' : addr, in_guard_low' in_guard_hi' : int fset) &m :
  exper_pre func' adv' =>
  in_guard_low' \subset in_guard_hi' => adv_fw_pi \in in_guard_hi' =>
  CompEnv.in_guard_low{m} = in_guard_low' =>
  Pr[Exper(MI(SMCReal(KERS.KERealSimp), Adv), Env).main
       (func', adv', in_guard_low') @ &m : res] =
  Pr[Exper(MI(KERS.KERealSimp, Adv), CompEnv(Env)).main
       (func' ++ [2], adv', in_guard_hi') @ &m : res].
proof.
move => pre in_guard'_sub not_in_guard' ce_in_guard'_eq.
byequiv => //.
proc.
inline MI(SMCReal(KERS.KERealSimp), Adv).init
       MI(KERS.KERealSimp, Adv).init
       SMCReal(KERS.KERealSimp).init
       Exper(MI(KERS.KERealSimp, Adv), CompEnv(Env)).E.main
       Exper
       (MI'
        (SMCReal
         (CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubKE),
          CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubAdv),
        Env).main
       MakeInt'.MI
       (SMCReal
        (CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubKE),
         CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubAdv).init
       CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubKE.init
       CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubAdv.init
       SMCReal(CompEnv(Env, MI(KERS.KERealSimp, Adv)).StubKE).init.
seq 15 34 :
  (={adv, MI.adv, glob SMCReal,
     glob KERS.KERealSimp, glob Env, glob Adv} /\
   exper_pre func{1} adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   MakeInt'.MI.in_guard{2} \subset MI.in_guard{2} /\
   adv_fw_pi \in MI.in_guard{2} /\
   in_guard{1} = in_guard1{2} /\
   func{2} = func{1} ++ [2] /\ func0{2} = func{1} /\
   adv0{2} = adv{2} /\ 
   MI.func{1} = func{1} /\ MI.func{2} = func{2} /\
   MI.adv{1} = adv{1} /\ 
   MakeInt'.MI.func{2} = func{1} /\ MakeInt'.MI.adv{2} = adv{2} /\
   SMCReal.self{1} = func{1} /\ SMCReal.adv{1} = adv{1} /\
   CompEnv.func{2} = func{1} /\ CompEnv.adv{2} = adv{1} /\
   CompEnv.stub_st{2} = None).
swap{1} [11..12] 2.
swap{2} 28 6.
swap{2} [7..8] 26.
call (_ : true).
call KERS.ke_real_simp_init.
call Fwd.term_init.
auto; progress; smt(size_cat take_size_cat).
wp.
call
  (_ :
   ={MI.adv, glob SMCReal, glob KERS.KERealSimp, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   MakeInt'.MI.in_guard{2} \subset MI.in_guard{2} /\
   adv_fw_pi \in MI.in_guard{2} /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\ MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None).
conseq smc_sec1_ke_real_simp_bridge_invoke => // |>.
auto.
qed.

(* end of core of KERealSimp bridging lemma proof *)

lemma smc_sec1_ke_real_bridge
      (func' adv' : addr, in_guard_low' in_guard_hi' : int fset) &m :
  exper_pre func' adv' =>
  in_guard_low' \subset in_guard_hi' => adv_fw_pi \in in_guard_hi' =>
  CompEnv.in_guard_low{m} = in_guard_low' =>
  Pr[Exper(MI(SMCReal(KeyEx.KEReal), Adv), Env).main
       (func', adv', in_guard_low') @ &m : res] =
  Pr[Exper(MI(KeyEx.KEReal, Adv), CompEnv(Env)).main
       (func' ++ [2], adv', in_guard_hi') @ &m : res].
proof.
move => pre in_guard'_sub not_in_guard' ce_in_guard'_eq.
rewrite (smc_real_ke_real_simp func' adv' in_guard_low' &m) //.
rewrite (KERS.Exper_KEReal_KERealSimp Adv (CompEnv(Env))
        (func' ++ [2]) adv' in_guard_hi' &m) 1:inc_ext1 //.
by rewrite (smc_sec1_ke_real_simp_bridge func' adv' in_guard_low'
           in_guard_hi' &m).
qed.

(* start of core of KEIdeal bridging lemma proof

   NOTE: this is formed via textual substitutions of the KERealSimp
   version - except that final local lemma is a non-local lemma *)

local module StubKE_KEIdeal = CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubKE.

type real_ke_ideal_term_met_st = {
  real_ke_ideal_term_met_st_p1s : smc_real_p1_state;
  real_ke_ideal_term_met_st_p2s : smc_real_p2_state;
  real_ke_ideal_term_met_st_fws : Fwd.fw_state;
  real_ke_ideal_term_met_st_kes : KeyEx.ke_ideal_state
}.

op real_ke_ideal_term_metric_max : int =
     real_p1_term_metric_max +
     real_p2_term_metric_max +
     Fwd.term_metric_max +
     KeyEx.ke_ideal_term_metric_max.

op real_ke_ideal_term_metric (rtms : real_ke_ideal_term_met_st) : int =
     real_p1_term_metric rtms.`real_ke_ideal_term_met_st_p1s +
     real_p2_term_metric rtms.`real_ke_ideal_term_met_st_p2s +
     Fwd.term_metric rtms.`real_ke_ideal_term_met_st_fws +
     KeyEx.ke_ideal_term_metric rtms.`real_ke_ideal_term_met_st_kes.

lemma ge0_real_ke_ideal_term_metric (rtms : real_ke_ideal_term_met_st) :
  0 <= real_ke_ideal_term_metric rtms.
proof.
smt(ge0_real_p1_term_metric ge0_real_p2_term_metric
    Fwd.ge0_term_metric KeyEx.ge0_ke_ideal_term_metric).
qed.

lemma real_ke_ideal_term_metric0 (rtms : real_ke_ideal_term_met_st) :
  real_ke_ideal_term_metric rtms = 0 =>
  real_p1_term_metric rtms.`real_ke_ideal_term_met_st_p1s = 0 /\
  real_p2_term_metric rtms.`real_ke_ideal_term_met_st_p2s = 0 /\
  Fwd.term_metric rtms.`real_ke_ideal_term_met_st_fws = 0 /\
  KeyEx.ke_ideal_term_metric rtms.`real_ke_ideal_term_met_st_kes = 0.
proof.
smt(ge0_real_p1_term_metric ge0_real_p2_term_metric
    Fwd.ge0_term_metric KeyEx.ge0_ke_ideal_term_metric).
qed.

local lemma smc_sec1_ke_ideal_bridge_induction (n : int) :
  equiv
  [SMCSec1Bridge_Left(KeyEx.KEIdeal).rest ~
   SMCSec1Bridge_TopRight(KeyEx.KEIdeal).rest :
   ={m, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
    (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
    MI.func{1} ++ [1] <= m{1}.`2.`1 \/
    (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
   real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   ={res, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   CompEnv.stub_st{2} = None] /\
  equiv
  [SMCSec1Bridge_Left(KeyEx.KEIdeal).rest ~
   SMCSec1Bridge_BotRightKE(KeyEx.KEIdeal).rest :
   ={m, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   m{1}.`1 = Adv /\ MI.func{1} ++ [2] <= m{1}.`2.`1 /\
   real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   ={res, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   CompEnv.stub_st{2} = None] /\
  equiv
  [SMCSec1Bridge_Left(KeyEx.KEIdeal).rest ~
   SMCSec1Bridge_BotRightAdv(KeyEx.KEIdeal).rest :
   ={m, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   m{1}.`1 = Adv /\ MI.func{1} ++ [2] <= m{1}.`2.`1 /\
   real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   ={res, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   CompEnv.stub_st{2} = None].
proof.
case (n < 0).
move => lt0_n.
(split; last split); proc; exfalso; smt(ge0_real_ke_ideal_term_metric).
rewrite -lezNgt.
elim n => [| n ge0_n IH].
(* basis step *)
split; last split.
(* SMCSec1Bridge_Left(KeyEx.KEIdeal).rest ~
   SMCSec1Bridge_TopRight(KeyEx.KEIdeal).rest *)
proc.
rcondt{1} 3; first auto.
rcondt{2} 3; first auto.
sp 2 2.
if => //.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\ r{1} = None).
exlim (real_p1_term_metric SMCReal.st1{1}) => p1_met.
call (smc_party1_met KeyEx.KEIdeal StubKE_KEIdeal p1_met).
auto; smt(real_ke_ideal_term_metric0 ge0_real_p1_term_metric).
rcondf{1} 1; first auto.
rcondf{2} 1; first auto.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
if => //.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\ r{1} = None).
exlim (real_p2_term_metric SMCReal.st2{1}) => p2_met.
call (smc_party2_met KeyEx.KEIdeal StubKE_KEIdeal p2_met).
auto; smt(real_ke_ideal_term_metric0 ge0_real_p2_term_metric).
rcondf{1} 1; first auto.
rcondf{2} 1; first auto.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
if => //.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\ r{1} = None).
exlim (Fwd.term_metric Fwd.Forw.st{1}) => fwd_met.
call (Fwd.term_invoke fwd_met).
auto; smt(real_ke_ideal_term_metric0 Fwd.ge0_term_metric).
rcondf{1} 1; first auto.
rcondf{2} 1; first auto.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
inline{2} (1) CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubKE.invoke.
rcondf{2} 2; first auto.
inline{2} (1) MI(KeyEx.KEIdeal, Adv).invoke.
rcondt{2} 5; first auto; smt().
inline{2} (1) MI(KeyEx.KEIdeal, Adv).loop.
rcondt{2} 8; first auto.
rcondt{2} 10; first auto; smt().
sp 0 9.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done0{2}
   /\ r{1} = r2{2} /\
   ={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\ r{1} = None).
exlim (KeyEx.ke_ideal_term_metric KeyEx.KEIdeal.st{1}) => ke_met.
call (KeyEx.ke_ideal_term_invoke ke_met).
auto; smt(real_ke_ideal_term_metric0 KeyEx.ge0_ke_ideal_term_metric).
rcondt{2} 1; first auto.
rcondf{2} 2; first auto.
sp 0 5.
rcondf{1} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondt{1} 1; first auto; smt().
rcondt{2} 1; first auto; smt().
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondt{1} 2; first auto; smt().
rcondt{2} 2; first auto; smt().
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto; smt().
(* SMCSec1Bridge_Left(KeyEx.KEIdeal).rest ~
   SMCSec1Bridge_BotRightKE(KeyEx.KEIdeal).rest *)
proc.
rcondt{1} 3; first auto.
rcondt{2} 4; first auto.
rcondt{2} 6; first auto.
rcondf{1} 3; first auto; smt(not_le_ext_nonnil_l).
rcondf{1} 3; first auto; smt(not_le_ext_nonnil_l).
rcondf{1} 3; first auto; smt(not_le_other_branch).
sp 2 5.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done1{2} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\ r{1} = None).
exlim (KeyEx.ke_ideal_term_metric KeyEx.KEIdeal.st{1}) => ke_met.
call (KeyEx.ke_ideal_term_invoke ke_met).
auto; smt(real_ke_ideal_term_metric0 KeyEx.ge0_ke_ideal_term_metric).
rcondf{1} 1; first auto.
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{2} 1; first auto.
rcondf{2} 2; first auto.
rcondf{2} 2; first auto.
rcondf{2} 2; first auto.
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
rcondt{2} 3; first auto.
rcondf{2} 4; first auto.
auto.
(* SMCSec1Bridge_Left(KeyEx.KEIdeal).rest ~
   SMCSec1Bridge_BotRightAdv(KeyEx.KEIdeal).rest *)
proc.
rcondt{1} 3; first auto.
rcondt{2} 3; first auto.
rcondt{2} 5; first auto.
rcondf{1} 3; first auto; smt(not_le_ext_nonnil_l).
rcondf{1} 3; first auto; smt(not_le_ext_nonnil_l).
rcondf{1} 3; first auto; smt(not_le_other_branch).
sp 2 4.
seq 1 1 :
  (not_done{1} /\ not_done0{1} /\ not_done{2} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\ r{1} = None).
exlim (KeyEx.ke_ideal_term_metric KeyEx.KEIdeal.st{1}) => ke_met.
call (KeyEx.ke_ideal_term_invoke ke_met).
auto; smt(real_ke_ideal_term_metric0 KeyEx.ge0_ke_ideal_term_metric).
rcondf{1} 1; first auto.
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{2} 1; first auto.
rcondf{2} 2; first auto.
rcondf{2} 2; first auto.
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
auto.
(* inductive step *)
split; last split.
(* SMCSec1Bridge_Left(KeyEx.KEIdeal).rest ~
   SMCSec1Bridge_TopRight(KeyEx.KEIdeal).rest *)
proc; sp 2 2.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
if => //.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\
   (r{1} = None \/
    real_ke_ideal_term_metric
    {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
      real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
      real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
      real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n)).
exlim (real_p1_term_metric SMCReal.st1{1}) => p1_met.
call (smc_party1_met KeyEx.KEIdeal StubKE_KEIdeal p1_met).
auto; progress; smt().
if => //.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondt{1} 3; first auto.
rcondt{2} 3; first auto.
rcondf{1} 4; first auto.
rcondf{2} 4; first auto.
auto.
case (r{1} = None).
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
conseq
  (_ :
   not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\
   real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
   r{1} <> None /\
   (oget r{1}).`1 = Dir /\
   (SMCReal.self{1} ++ [2] <= (oget r{1}).`2.`1 \/
    SMCReal.self{1} ++ [1] <= (oget r{1}).`2.`1) ==>
   _); first smt(le_trans le_ext_r).
rcondf{1} 1; first auto.
progress; smt(le_trans le_ext_r).
rcondf{2} 1; first auto.
progress; smt(le_trans le_ext_r).
sp 1 1.
conseq
  (_ :
   not_done{1} /\ not_done0{1} /\ not_done{2} /\ not_done0{2} /\
   ={m, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
    (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
    MI.func{1} ++ [1] <= m{1}.`2.`1 \/
    (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
   real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _); first smt().
(* use part 1 of induction *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KeyEx.KEIdeal).rest(m, r);}
(={m, r, glob MI, glob SMCReal, glob KeyEx.KEIdeal,
   glob Adv} /\
 not_done{1} /\ not_done0{1} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob Adv})
(={m, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
  (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m{1}.`2.`1 \/
  (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
 real_ke_ideal_term_metric
 {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
   real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
   real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 not_done{2} /\ not_done0{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} m{2} r{1}.
inline SMCSec1Bridge_Left(KeyEx.KEIdeal).rest.
sp 0 4.
sim; smt().
transitivity{2}
{r <@ SMCSec1Bridge_TopRight(KeyEx.KEIdeal).rest(m, r);}
(={m, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
  (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m{1}.`2.`1 \/
  (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
  real_ke_ideal_term_metric
  {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
    real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
    real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
    real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m, r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done0{2} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          MI.adv{2} (MI.func{1} ++ [2]) MI.in_guard{2} m{2} r{2}.
exlim
  (real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|}) => met.
have [IH_first _] := IH.
call IH_first.
auto.
inline SMCSec1Bridge_TopRight(KeyEx.KEIdeal).rest.
sp 4 0.
sim; smt().
(* end of use of part 1 of induction *)
if => //.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\
   (r{1} = None \/
    real_ke_ideal_term_metric
    {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
      real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
      real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
      real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n)).
exlim (real_p2_term_metric SMCReal.st2{1}) => p2_met.
call (smc_party2_met KeyEx.KEIdeal StubKE_KEIdeal p2_met).
auto; progress; smt().
if => //.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondt{1} 3; first auto.
rcondt{2} 3; first auto.
rcondf{1} 4; first auto.
rcondf{2} 4; first auto.
auto.
case (r{1} = None).
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
conseq
  (_ :
   not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\
   real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
   r{1} <> None /\
   (oget r{1}).`1 = Dir /\
   (SMCReal.self{1} ++ [2] <= (oget r{1}).`2.`1 \/
    ! SMCReal.self{1} <= (oget r{1}).`2.`1) ==>
   _); first smt(le_trans le_ext_r).
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondf{1} 5; first auto; smt().
rcondf{2} 5; first auto; smt().
rcondt{1} 5; first auto.
rcondt{2} 5; first auto.
sp 5 5.
if; first smt().
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
rcondf{1} 1; first auto.
rcondf{2} 1; first auto.
auto.
sp 1 1.
conseq
  (_ :
   not_done{1} /\ not_done0{1} /\ not_done{2} /\ not_done0{2} /\
   ={m, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
    (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
    MI.func{1} ++ [1] <= m{1}.`2.`1 \/
    (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
   real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _); first smt().
(* use part 1 of induction *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KeyEx.KEIdeal).rest(m, r);}
(={m, r, glob MI, glob SMCReal, glob KeyEx.KEIdeal,
   glob Adv} /\
 not_done{1} /\ not_done0{1} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob Adv})
(={m, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
  (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m{1}.`2.`1 \/
  (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
 real_ke_ideal_term_metric
 {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
   real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
   real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 not_done{2} /\ not_done0{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} m{2} r{1}.
inline SMCSec1Bridge_Left(KeyEx.KEIdeal).rest.
sp 0 4.
sim; smt().
transitivity{2}
{r <@ SMCSec1Bridge_TopRight(KeyEx.KEIdeal).rest(m, r);}
(={m, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
  (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m{1}.`2.`1 \/
  (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
  real_ke_ideal_term_metric
  {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
    real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
    real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
    real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m, r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done0{2} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} MI.adv{2} (MI.func{1} ++ [2])
          MI.in_guard{2}  m{2} r{2}.
exlim
  (real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|}) => met.
have [IH_first _] := IH.
call IH_first.
auto.
inline SMCSec1Bridge_TopRight(KeyEx.KEIdeal).rest.
sp 4 0.
sim; smt().
(* end of use of part 1 of induction *)
if => //.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\
   (r{1} = None \/
    real_ke_ideal_term_metric
    {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
      real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
      real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
      real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n)).
exlim (Fwd.term_metric Fwd.Forw.st{1}) => fwd_met.
call (Fwd.term_invoke fwd_met).
auto; progress; smt().
if => //.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondt{1} 3; first auto.
rcondt{2} 3; first auto.
rcondf{1} 4; first auto.
rcondf{2} 4; first auto.
auto.
case (r{1} = None).
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
conseq
  (_ :
   not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\
   real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
   r{1} <> None /\
   ((oget r{1}).`1 = Dir /\ (oget r{1}).`2.`1 = MI.func{1} /\
    (oget r{1}).`2.`2 = 4 \/
    (oget r{1}).`1 = Adv /\ ! MI.func{1} <= (oget r{1}).`2.`1 /\
    (oget r{1}).`2.`2 = adv_fw_pi) ==>
   _); first smt(le_trans le_ext_r).
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondf{1} 5; first auto; smt().
rcondf{2} 5; first auto; smt().
rcondf{1} 5; first auto; smt(le_refl).
rcondf{2} 5; first auto; smt(le_refl).
sp 4 4.
if; first smt().
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
rcondf{1} 3; first auto; smt().
rcondf{2} 3; first auto; smt().
sp 2 2.
inline{2} (1) CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubAdv.invoke.
rcondf{2} 2; first auto.
inline{2} (1) MI(KeyEx.KEIdeal, Adv).invoke.
rcondt{2} 5; first auto; smt(in_fset1 le_refl incP).
inline MI(KeyEx.KEIdeal, Adv).loop.
rcondt{2} 8; first auto.
rcondf{2} 10; first auto; smt(inc_le1_not_lr le_ext_r).
sp 0 9.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ !not_done0{1} /\ !not_done0{2} /\
   not_done1{2} /\ r{1} = r2{2} /\
   ={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\
   real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n).
call (_ : true).
auto; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondf{2} 4; first auto.
rcondt{2} 5; first auto.
rcondf{2} 6; first auto.
auto.
sp 3 3.
if; first smt().
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondf{2} 5; first auto.
rcondt{2} 6; first auto.
rcondf{2} 7; first auto.
auto.
case (MI.func{1} ++ [2] <= addr1{1}).
rcondf{1} 1; first auto; smt(le_trans le_ext_r).
rcondf{2} 1; first auto; smt().
rcondt{1} 1; first auto.
rcondt{1} 3; first auto; smt(le_ext_r le_trans).
inline{1} (1) SMCReal(KeyEx.KEIdeal).invoke.
rcondt{1} 7; first auto; progress.
right; rewrite negb_or not_dir in H10.
smt(le_ext_r le_trans).
inline{1} (1) SMCReal(KeyEx.KEIdeal).loop.
sp 9 0.
conseq
  (_ :
   not_done{1} /\ not_done1{1} /\ not_done{2} /\ not_done1{2} /\
   ={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   m1{1} = m2{2} /\
   m1{1}.`1 = Adv /\ MI.func{1} ++ [2] <= m1{1}.`2.`1 /\
   real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _).
move => &1 &2 />. rewrite negb_or not_dir /#.
(* use part 3 of induction: *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KeyEx.KEIdeal).rest(m1, r1);}
(={m1, r1, glob MI, glob SMCReal, glob KeyEx.KEIdeal,
   glob Adv} /\
 not_done{1} /\ not_done1{1} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob Adv})
(={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 m1{1} = m2{2} /\
 m1{1}.`1 = Adv /\ MI.func{1} ++ [2] <= m1{1}.`2.`1 /\
 real_ke_ideal_term_metric
 {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
   real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
   real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 not_done{2} /\ not_done1{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} m2{2} r1{1}.
inline SMCSec1Bridge_Left(KeyEx.KEIdeal).rest.
sp 0 4.
seq 3 1 :
  (={glob MI, glob SMCReal, glob KeyEx.KEIdeal,
     glob Adv} /\
   r{1} = r2{2} /\ not_done{1} = not_done2{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
transitivity{2}
{r <@ SMCSec1Bridge_BotRightAdv(KeyEx.KEIdeal).rest(m2, r2);}
(={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 m1{1} = m2{2} /\
 m1{1}.`1 = UCCore'.Adv /\ MI.func{1} ++ [2] <= m1{1}.`2.`1 /\
 real_ke_ideal_term_metric
 {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
   real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
   real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m2, r2, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done1{2} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} MI.adv{2} (MI.func{1} ++ [2])
          MI.in_guard{2} m2{2} r2{2}.
exlim
  (real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|}) => met.
have [_ [_ IH_third]] := IH.
call IH_third.
auto.
inline SMCSec1Bridge_BotRightAdv(KeyEx.KEIdeal).rest.
sp 4 0.
seq 1 3 :
  (={glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv,
     glob Adv} /\
   r3{1} = r0{2} /\ not_done00{1} = not_done1{2} /\ not_done2{1} = not_done{2}).
sim; smt().
seq 1 2 :
  (={glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv,
     glob Adv} /\
   r3{1} = r{2} /\ not_done00{1} = not_done1{2} /\ not_done2{1} = not_done{2}).
sim.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
(* end of use of part 3 of induction *)
rcondt{2} 1; first auto; smt().
rcondf{2} 2; first auto.
rcondt{2} 4; first auto; smt().
rcondf{2} 7; first auto; smt().
rcondf{2} 8; first auto.
rcondf{2} 11; first auto; smt().
sp 0 10.
if; first smt().
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
rcondt{1} 3; first auto; smt().
rcondt{2} 3; first auto; smt().
inline{1} (1) SMCReal(KeyEx.KEIdeal).invoke.
inline{2} (1) SMCReal(CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubKE).invoke.
sp 6 6.
if; first smt().
inline{1} (1) SMCReal(KeyEx.KEIdeal).loop.
inline{2} (1) SMCReal(CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubKE).loop.
sp 3 3.
conseq
  (_ :
   not_done{1} /\ not_done1{1} /\ not_done{2} /\ not_done2{2} /\
   ={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   m1{1} = m4{2} /\
   (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = MI.func{1} /\
    (m1{1}.`2.`2 = 1 \/ m1{1}.`2.`2 = 2 \/ m1{1}.`2.`2 = 3 \/ m1{1}.`2.`2 = 4) \/
    MI.func{1} ++ [1] <= m1{1}.`2.`1 \/
    (m1{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m1{1}.`2.`1)) /\
   real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _).
move => &1 &2 /> _ <- [#] -> -> -> -> -> /#.
(* use part 1 of induction *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KeyEx.KEIdeal).rest(m1, r1);}
(={m1, r1, glob MI, glob SMCReal, glob KeyEx.KEIdeal,
   glob Adv} /\
 not_done{1} /\ not_done1{1} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob Adv})
(={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 m1{1} = m4{2} /\
 (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = MI.func{1} /\
  (m1{1}.`2.`2 = 1 \/ m1{1}.`2.`2 = 2 \/ m1{1}.`2.`2 = 3 \/ m1{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m1{1}.`2.`1 \/
  (m1{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m1{1}.`2.`1)) /\
 real_ke_ideal_term_metric
 {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
   real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
   real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 not_done{2} /\ not_done2{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} m4{2} r1{1}.
inline SMCSec1Bridge_Left(KeyEx.KEIdeal).rest.
sp 0 4.
seq 3 1 :
  (={glob MI, glob SMCReal, glob KeyEx.KEIdeal,
     glob Adv} /\
   r{1} = r2{2} /\ not_done{1} = not_done2{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim; smt().
transitivity{2}
{r <@ SMCSec1Bridge_TopRight(KeyEx.KEIdeal).rest(m4, r4);}
(={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 m1{1} = m4{2} /\
 (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = MI.func{1} /\
  (m1{1}.`2.`2 = 1 \/ m1{1}.`2.`2 = 2 \/ m1{1}.`2.`2 = 3 \/ m1{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m1{1}.`2.`1 \/
  (m1{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m1{1}.`2.`1)) /\
  real_ke_ideal_term_metric
  {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
    real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
    real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
    real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m4, r4, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done2{2} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} MI.adv{2} (MI.func{1} ++ [2])
          MI.in_guard{2} m4{2} r4{2}.
exlim
  (real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|}) => met.
have [IH_first _] := IH.
call IH_first.
auto.
inline SMCSec1Bridge_TopRight(KeyEx.KEIdeal).rest.
sp 4 0.
seq 1 3 :
  (={glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv,
     glob Adv} /\
   r5{1} = r{2} /\ not_done3{1} = not_done{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
(* end of use of part 1 of induction *)
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
sp 1 1.
conseq
  (_ :
   not_done{1} /\ not_done0{1} /\ not_done{2} /\ not_done0{2} /\
   ={m, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
    (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
    MI.func{1} ++ [1] <= m{1}.`2.`1 \/
    (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
   real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _); first smt().
(* use part 1 of induction *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KeyEx.KEIdeal).rest(m, r);}
(={m, r, glob MI, glob SMCReal, glob KeyEx.KEIdeal,
   glob Adv} /\
 not_done{1} /\ not_done0{1} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob Adv})
(={m, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
  (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m{1}.`2.`1 \/
  (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
 real_ke_ideal_term_metric
 {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
   real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
   real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 not_done{2} /\ not_done0{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          m{2} r{1}.
inline SMCSec1Bridge_Left(KeyEx.KEIdeal).rest.
sp 0 4.
sim; smt().
transitivity{2}
{r <@ SMCSec1Bridge_TopRight(KeyEx.KEIdeal).rest(m, r);}
(={m, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
  (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m{1}.`2.`1 \/
  (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
  real_ke_ideal_term_metric
  {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
    real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
    real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
    real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m, r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done0{2} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          MI.adv{2} (MI.func{1} ++ [2]) MI.in_guard{2} m{2} r{2}.
exlim
  (real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|}) => met.
have [IH_first _] := IH.
call IH_first.
auto.
inline SMCSec1Bridge_TopRight(KeyEx.KEIdeal).rest.
sp 4 0.
sim; smt().
(* end of use of part 1 of induction *)
inline{2} (1) CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubKE.invoke.
rcondf{2} 2; first auto.
inline{2} (1) MI(KeyEx.KEIdeal, Adv).invoke.
rcondt{2} 5; first auto; smt().
inline{2} (1) MI(KeyEx.KEIdeal, Adv).loop.
rcondt{2} 8; first auto.
rcondt{2} 10; first auto; smt().
sp 0 9.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done0{2} /\
   not_done1{2} /\ r{1} = r2{2} /\
   ={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\
   (r{1} = None \/
   real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n)).
exlim (KeyEx.ke_ideal_term_metric KeyEx.KEIdeal.st{1}) => ke_met.
call (KeyEx.ke_ideal_term_invoke ke_met).
auto; progress; smt().
case (r{1} = None).
rcondt{2} 1; first auto.
rcondf{2} 2; first auto.
rcondf{2} 4; first auto.
rcondf{1} 1; first auto.
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 5; first auto.
rcondt{2} 5; first auto.
rcondf{2} 6; first auto.
rcondt{2} 6; first auto.
rcondf{2} 7; first auto.
auto.
rcondf{2} 1; first auto.
case (MI.func{1} ++ [2] <= (oget r{1}).`2.`1).
rcondt{1} 1; first auto; smt(not_le_ext_nonnil_l le_trans le_ext_r).
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
rcondt{2} 4; first auto. 
rcondf{2} 6; first auto.
rcondf{2} 8; first auto.
rcondf{2} 9; first auto.
rcondt{2} 9; first auto.
rcondf{2} 10; first auto.
rcondt{2} 10; first auto.
rcondf{2} 11; first auto.
auto.
rcondf{2} 4; first auto.
case ((oget r{1}).`1 = Dir).
rcondt{2} 4; first auto.
case (MI.adv{1} <= (oget r{1}).`2.`1).
rcondt{2} 5; first auto.
rcondf{2} 6; first auto.
rcondf{2} 8; first auto.
sp 0 8.
rcondt{1} 1; first auto; smt(incP le_refl).
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
rcondf{2} 1; first auto.
rcondt{2} 1; first auto.
rcondf{2} 2; first auto.
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
auto.
rcondf{2} 5; first auto.
rcondf{2} 5; first auto.
rcondt{2} 7; first auto.
rcondf{2} 10; first auto; smt().
sp 0 10.
if => //.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondt{1} 3; first auto.
rcondt{2} 3; first auto.
rcondf{1} 4; first auto.
rcondf{2} 4; first auto.
auto.
rcondf{1} 1; first auto; smt(le_refl).
rcondf{2} 1; first auto; smt(le_refl).
sp 1 1.
conseq
  (_ :
   not_done{1} /\ not_done0{1} /\ not_done{2} /\ not_done0{2} /\
   ={m, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
    (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
    MI.func{1} ++ [1] <= m{1}.`2.`1 \/
    (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
   real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _); first smt().
(* use part 1 of induction *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KeyEx.KEIdeal).rest(m, r);}
(={m, r, glob MI, glob SMCReal, glob KeyEx.KEIdeal,
   glob Adv} /\
 not_done{1} /\ not_done0{1} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob Adv})
(={m, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
  (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m{1}.`2.`1 \/
  (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
 real_ke_ideal_term_metric
 {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
   real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
   real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 not_done{2} /\ not_done0{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          m{2} r{1}.
inline SMCSec1Bridge_Left(KeyEx.KEIdeal).rest.
sp 0 4.
sim; smt().
transitivity{2}
{r <@ SMCSec1Bridge_TopRight(KeyEx.KEIdeal).rest(m, r);}
(={m, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
  (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m{1}.`2.`1 \/
  (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
  real_ke_ideal_term_metric
  {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
    real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
    real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
    real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m, r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done0{2} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          MI.adv{2} (MI.func{1} ++ [2]) MI.in_guard{2} m{2} r{2}.
exlim
  (real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|}) => met.
have [IH_first _] := IH.
call IH_first.
auto.
inline SMCSec1Bridge_TopRight(KeyEx.KEIdeal).rest.
sp 4 0.
sim; smt().
(* end of use of part 1 of induction *)
rcondf{2} 4; first auto.
case ((oget r{1}).`2.`1 <> MI.adv{1} \/ (oget r{1}).`2.`2 = 0).
rcondt{2} 4; first auto.
rcondf{2} 6; first auto.
rcondf{2} 8; first auto.
rcondf{2} 9; first auto.
rcondt{2} 9; first auto.
rcondf{2} 10; first auto.
rcondt{2} 10; first auto.
rcondf{2} 11; first auto.
wp.
if{1}.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
auto.
rcondt{1} 1; first auto; smt().
rcondf{1} 2; first auto.
rcondf{1} 2; first auto.
rcondf{1} 5; first auto; smt().
rcondf{1} 5; first auto.
rcondt{1} 5; first auto.
rcondf{1} 7; first auto.
auto.
rcondf{1} 1; first auto.
move => |> &hr _ _ _ _ _ ep _.
case (r2{m}) => // msg.
case msg => mod pt1 pt2 u.
case pt1 => addr1 n1 /= _.
rewrite not_dir negb_or /=.
smt(inc_nle_l).
rcondf{2} 4; first auto.
rcondt{1} 1; first auto; smt().
rcondf{1} 2; first auto.
rcondf{1} 2; first auto.
rcondf{1} 5; first auto; smt().
rcondf{1} 5; first auto.
rcondf{1} 5; first auto.
sp 4 3.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
rcondf{1} 3; first auto; smt().
rcondf{2} 3; first auto; smt().
sp 2 2.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ not_done0{2} /\ not_done1{2} /\
   r{1} = r2{2} /\
   ={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\
   (r{1} = None \/
    real_ke_ideal_term_metric
    {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
      real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
      real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
      real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n)).
call (_ : true).
auto; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondf{2} 4; first auto.
rcondf{2} 5; first auto.
rcondt{2} 5; first auto.
rcondf{2} 6; first auto.
rcondt{2} 6; first auto.
rcondf{2} 7; first auto.
auto.
sp 3 3.
if; first smt().
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondf{2} 5; first auto.
rcondf{2} 6; first auto.
rcondt{2} 6; first auto.
rcondf{2} 7; first auto.
rcondt{2} 7; first auto.
rcondf{2} 8; first auto.
auto.
case (MI.func{1} ++ [2] <= (oget r{1}).`2.`1).
rcondf{1} 1; first auto; smt(le_trans le_ext_r).
rcondf{2} 1; first auto; smt().
rcondt{1} 1; first auto.
rcondt{1} 3; first auto; smt(le_trans le_ext_r).
inline{1} (1) SMCReal(KeyEx.KEIdeal).invoke.
rcondt{1} 7; first auto.
move => |> &hr <-; by rewrite negb_or not_dir.
inline{1} (1) SMCReal(KeyEx.KEIdeal).loop.
sp 9 0.
conseq
  (_ :
   not_done{1} /\ not_done1{1} /\ not_done{2} /\ not_done0{2} /\ not_done1{2} /\
   ={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   m1{1} = m2{2} /\
   m1{1}.`1 = Adv /\ MI.func{1} ++ [2] <= m1{1}.`2.`1 /\
   real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _).
move => &1 &2 />. rewrite negb_or not_dir /#.
(* use part 2 of induction: *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KeyEx.KEIdeal).rest(m1, r1);}
(={m1, r1, glob MI, glob SMCReal, glob KeyEx.KEIdeal,
   glob Adv} /\
 not_done{1} /\ not_done1{1} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob Adv})
(={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 m1{1} = m2{2} /\
 m1{1}.`1 = Adv /\ MI.func{1} ++ [2] <= m1{1}.`2.`1 /\
 real_ke_ideal_term_metric
 {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
   real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
   real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 not_done{2} /\ not_done0{2} /\ not_done1{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          m2{2} r1{1}.
inline SMCSec1Bridge_Left(KeyEx.KEIdeal).rest.
sp 0 4.
seq 3 1 :
  (={glob MI, glob SMCReal, glob KeyEx.KEIdeal,
     glob Adv} /\
   r{1} = r2{2} /\ not_done{1} = not_done2{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
transitivity{2}
{r <@ SMCSec1Bridge_BotRightKE(KeyEx.KEIdeal).rest(m2, r2);}
(={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 m1{1} = m2{2} /\
 m1{1}.`1 = UCCore'.Adv /\ MI.func{1} ++ [2] <= m1{1}.`2.`1 /\
 real_ke_ideal_term_metric
 {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
   real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
   real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m2, r2, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done0{2} /\ not_done1{2} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} MI.adv{2} (MI.func{1} ++ [2])
          MI.in_guard{2} m2{2} r2{2}.
exlim
  (real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|}) => met.
have [_ [IH_second _]] := IH.
call IH_second.
auto.
inline SMCSec1Bridge_BotRightKE(KeyEx.KEIdeal).rest.
sp 5 0.
seq 1 3 :
  (={glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv,
     glob Adv} /\
   r3{1} = r0{2} /\ not_done00{1} = not_done1{2} /\
   not_done10{1} = not_done0{2} /\ not_done2{1} = not_done{2}).
sim; smt().
seq 1 2 :
  (={glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv,
     glob Adv} /\
   r3{1} = r{2} /\ not_done00{1} = not_done1{2} /\
   not_done10{1} = not_done0{2} /\ not_done2{1} = not_done{2}).
sim.
if => //.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondt{1} 3; first auto.
rcondt{2} 3; first auto.
rcondf{1} 4; first auto.
rcondf{2} 4; first auto.
auto.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
sp 1 1.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
sim.
(* end of use of part 2 of induction *)
rcondt{2} 1; first auto; smt().
rcondf{2} 2; first auto.
rcondt{2} 4; first auto.
rcondt{2} 7; first auto.
move => |> &hr <-; by rewrite negb_or not_dir.
rcondf{2} 10; first auto => |> &hr <-; progress; smt(incP).
rcondt{2} 10; first auto => |> &hr <- /=; smt(incP).
rcondf{2} 11; first auto.
rcondf{2} 11; first auto.
rcondf{2} 14; first auto => |> &hr <- /=; smt(incP).
rcondf{2} 14; first auto.
rcondf{2} 14; first auto.
rcondt{2} 14; first auto.
rcondf{2} 16; first auto => |> &hr <- /=; smt(incP).
inline{2} (1) CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubAdv.invoke.
rcondt{2} 17; first auto.
rcondf{2} 20; first auto.
rcondf{2} 23; first auto => |> &hr <- /#.
sp 0 22.
if; first auto => |> &1 &2 _ _ <- //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto; progress; by rewrite some_oget.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
sp 2 2.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto => |> &hr _ _ <- //.
inline{1} (1) SMCReal(KeyEx.KEIdeal).invoke.
inline{2} (1) SMCReal(CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubKE).invoke.
sp 4 4.
if.
auto => |> &1 &2 _ _ <- //.
inline{1} (1) SMCReal(KeyEx.KEIdeal).loop.
inline{2} (1) SMCReal(CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubKE).loop.
sp 3 3.
conseq
  (_ :
   not_done{1} /\ not_done1{1} /\ not_done{2} /\ not_done2{2} /\
   ={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   m1{1} = m5{2} /\
   (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = MI.func{1} /\
    (m1{1}.`2.`2 = 1 \/ m1{1}.`2.`2 = 2 \/ m1{1}.`2.`2 = 3 \/ m1{1}.`2.`2 = 4) \/
    MI.func{1} ++ [1] <= m1{1}.`2.`1 \/
    (m1{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m1{1}.`2.`1)) /\
   real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _).
move => &1 &2 /> _ _ <- [#] -> -> -> -> -> /#.
(* use part 1 of induction *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KeyEx.KEIdeal).rest(m1, r1);}
(={m1, r1, glob MI, glob SMCReal, glob KeyEx.KEIdeal,
   glob Adv} /\
 not_done{1} /\ not_done1{1} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob Adv})
(={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 m1{1} = m5{2} /\
 (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = MI.func{1} /\
  (m1{1}.`2.`2 = 1 \/ m1{1}.`2.`2 = 2 \/ m1{1}.`2.`2 = 3 \/ m1{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m1{1}.`2.`1 \/
  (m1{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m1{1}.`2.`1)) /\
 real_ke_ideal_term_metric
 {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
   real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
   real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 not_done{2} /\ not_done2{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} m5{2} r1{1}.
inline SMCSec1Bridge_Left(KeyEx.KEIdeal).rest.
sp 0 4.
seq 3 1 :
  (={glob MI, glob SMCReal, glob KeyEx.KEIdeal,
     glob Adv} /\
   r{1} = r2{2} /\ not_done{1} = not_done2{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim; smt().
transitivity{2}
{r <@ SMCSec1Bridge_TopRight(KeyEx.KEIdeal).rest(m5, r5);}
(={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 m1{1} = m5{2} /\
 (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = MI.func{1} /\
  (m1{1}.`2.`2 = 1 \/ m1{1}.`2.`2 = 2 \/ m1{1}.`2.`2 = 3 \/ m1{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m1{1}.`2.`1 \/
  (m1{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m1{1}.`2.`1)) /\
  real_ke_ideal_term_metric
  {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
    real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
    real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
    real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m5, r5, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done2{2} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} MI.adv{2} (MI.func{1} ++ [2])
          MI.in_guard{2} m5{2} r5{2}.
exlim
  (real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|}) => met.
have [IH_first _] := IH.
call IH_first.
auto.
inline SMCSec1Bridge_TopRight(KeyEx.KEIdeal).rest.
sp 4 0.
seq 1 3 :
  (={glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv,
     glob Adv} /\
   r6{1} = r{2} /\ not_done3{1} = not_done{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
(* end of use of part 1 of induction *)
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
(* SMCSec1Bridge_Left(KeyEx.KEIdeal).rest ~
   SMCSec1Bridge_BotRightKE(KeyEx.KEIdeal).rest *)
proc.
rcondt{1} 3; first auto.
rcondt{2} 4; first auto.
rcondt{2} 6; first auto.
rcondf{1} 3; first auto; smt(not_le_ext_nonnil_l).
rcondf{1} 3; first auto; smt(not_le_ext_nonnil_l).
rcondf{1} 3; first auto; smt(not_le_other_branch).
sp 2 5.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done1{2} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\
   (r{1} = None \/
    real_ke_ideal_term_metric
    {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
      real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
      real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
      real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n)).
exlim (KeyEx.ke_ideal_term_metric KeyEx.KEIdeal.st{1}) => ke_met.
call (KeyEx.ke_ideal_term_invoke ke_met).
auto; smt(real_ke_ideal_term_metric0 KeyEx.ge0_ke_ideal_term_metric).
case (r{1} = None).
rcondf{1} 1; first auto.
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{2} 1; first auto.
rcondf{2} 2; first auto.
rcondf{2} 2; first auto.
rcondf{2} 2; first auto.
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
rcondt{2} 3; first auto.
rcondf{2} 4; first auto.
auto.
rcondf{2} 1; first auto.
case (MI.func{1} ++ [2] <= (oget r{1}).`2.`1).
rcondt{1} 1; first auto; smt(not_le_ext_nonnil_l le_trans le_ext_r).
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
rcondt{2} 4; first auto. 
rcondf{2} 6; first auto.
rcondf{2} 6; first auto.
rcondf{2} 6; first auto.
rcondt{2} 6; first auto.
rcondf{2} 7; first auto.
rcondt{2} 7; first auto.
rcondf{2} 8; first auto.
auto.
rcondf{2} 4; first auto.
case ((oget r{1}).`1 = Dir).
rcondt{2} 4; first auto.
case (MI.adv{1} <= (oget r{1}).`2.`1).
rcondt{2} 5; first auto.
rcondf{2} 6; first auto.
rcondf{2} 6; first auto.
rcondf{2} 6; first auto.
rcondt{2} 6; first auto.
rcondf{2} 7; first auto.
rcondt{2} 7; first auto.
rcondf{2} 8; first auto.
rcondt{1} 1; first auto; smt(incP not_dir not_le_ext_nonnil_l).
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
auto.
rcondf{2} 5; first auto.
rcondf{2} 5; first auto.
rcondt{2} 5; first auto.
rcondf{2} 8; first auto; smt().
sp 0 7.
if => //.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondt{1} 3; first auto.
rcondt{2} 3; first auto.
rcondf{1} 4; first auto.
rcondf{2} 4; first auto.
auto.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
sp 4 4.
rcondf{1} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondt{1} 1; first auto; smt().
rcondt{2} 1; first auto; smt().
sp 1 1.
rcondf{1} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{1} 1; first auto.
rcondf{2} 1; first auto.
auto.
sp 1 1.
conseq
  (_ :
   not_done{1} /\ not_done0{1} /\ not_done{2} /\ not_done1{2} /\
   ={m, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
    (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
    MI.func{1} ++ [1] <= m{1}.`2.`1 \/
    (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
   real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _); first smt().
(* use part 1 of induction *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KeyEx.KEIdeal).rest(m, r);}
(={m, r, glob MI, glob SMCReal, glob KeyEx.KEIdeal,
   glob Adv} /\
 not_done{1} /\ not_done0{1} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob Adv})
(={m, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
  (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m{1}.`2.`1 \/
  (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
 real_ke_ideal_term_metric
 {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
   real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
   real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 not_done{2} /\ not_done1{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} m{2} r{1}.
inline SMCSec1Bridge_Left(KeyEx.KEIdeal).rest.
sp 0 4.
sim; smt().
transitivity{2}
{r <@ SMCSec1Bridge_TopRight(KeyEx.KEIdeal).rest(m, r);}
(={m, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
  (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m{1}.`2.`1 \/
  (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
  real_ke_ideal_term_metric
  {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
    real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
    real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
    real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m, r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done1{2} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          MI.adv{2} (MI.func{1} ++ [2]) MI.in_guard{2} m{2} r{2}.
exlim
  (real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|}) => met.
have [IH_first _] := IH.
call IH_first.
auto.
inline SMCSec1Bridge_TopRight(KeyEx.KEIdeal).rest.
sp 4 0.
sim; smt().
(* end of use of part 1 of induction *)
rcondf{2} 4; first auto.
case ((oget r{1}).`2.`1 <> MI.adv{1} \/ (oget r{1}).`2.`2 = 0).
rcondt{2} 4; first auto.
rcondf{2} 6; first auto.
rcondf{2} 6; first auto.
rcondf{2} 6; first auto.
rcondt{2} 6; first auto.
rcondf{2} 7; first auto.
rcondt{2} 7; first auto.
rcondf{2} 8; first auto.
if{1}.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
auto.
rcondt{1} 1; first auto; smt().
rcondf{1} 2; first auto.
rcondf{1} 2; first auto.
rcondf{1} 5; first auto; smt().
rcondf{1} 5; first auto.
rcondt{1} 5; first auto.
rcondf{1} 7; first auto.
auto.
rcondf{2} 4; first auto.
rcondt{2} 4; first auto.
rcondf{2} 6; first auto.
rcondf{1} 1; first auto.
move => /> &hr; case (r{m}) => // [[]] ? [] ? ? ? ?.
rewrite not_dir negb_or /=.
smt(inc_nle_l).
rcondt{1} 1; first auto; smt().
rcondf{1} 2; first auto.
rcondf{1} 2; first auto.
rcondf{1} 5; first auto; smt().
rcondf{1} 5; first auto.
rcondf{1} 5; first auto.
rcondt{1} 5; first auto.
rcondf{1} 7; first auto; smt().
sp 6 5.
seq 1 1 :
  (!not_done0{1} /\ not_done{1} /\ not_done{2} /\
   not_done1{2} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\
   real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n).
call (_ : true).
auto; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondf{2} 2; first auto.
rcondf{2} 2; first auto.
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
rcondt{2} 3; first auto.
rcondf{2} 4; first auto.
auto.
sp 3 3.
if; first smt().
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondf{2} 3; first auto.
rcondf{2} 3; first auto.
rcondt{2} 3; first auto.
rcondf{2} 4; first auto.
rcondt{2} 4; first auto.
rcondf{2} 5; first auto.
auto.
case (MI.func{1} ++ [2] <= (oget r{1}).`2.`1).
rcondf{2} 1; first auto; smt().
rcondf{1} 1; first auto; smt(le_ext_r le_trans).
rcondt{1} 1; first auto.
rcondt{1} 3; first auto; smt(le_ext_r le_trans).
inline{1} (1) SMCReal(KeyEx.KEIdeal).invoke.
rcondt{1} 7; first auto.
move => |> &hr <- [#] -> -> /=.
by rewrite negb_or not_dir.
inline{1} (1) SMCReal(KeyEx.KEIdeal).loop.
sp 9 0.
conseq
  (_ :
   not_done{1} /\ not_done1{1} /\ not_done{2} /\ not_done0{2} /\ not_done1{2} /\
   ={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   m1{1} = m{2} /\
   m1{1}.`1 = Adv /\ MI.func{1} ++ [2] <= m1{1}.`2.`1 /\
   real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _).
move => &1 &2 />. rewrite negb_or not_dir /#.
(* use part 2 of induction: *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KeyEx.KEIdeal).rest(m1, r1);}
(={m1, r1, glob MI, glob SMCReal, glob KeyEx.KEIdeal,
   glob Adv} /\
 not_done{1} /\ not_done1{1} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob Adv})
(={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 m1{1} = m{2} /\
 m1{1}.`1 = Adv /\ MI.func{1} ++ [2] <= m1{1}.`2.`1 /\
 real_ke_ideal_term_metric
 {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
   real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
   real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 not_done{2} /\ not_done0{2} /\ not_done1{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} m{2} r1{1}.
inline SMCSec1Bridge_Left(KeyEx.KEIdeal).rest.
sp 0 4.
seq 3 1 :
  (={glob MI, glob SMCReal, glob KeyEx.KEIdeal,
     glob Adv} /\
   r{1} = r2{2} /\ not_done{1} = not_done2{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
transitivity{2}
{r <@ SMCSec1Bridge_BotRightKE(KeyEx.KEIdeal).rest(m, r);}
(={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 m1{1} = m{2} /\
 m1{1}.`1 = UCCore'.Adv /\ MI.func{1} ++ [2] <= m1{1}.`2.`1 /\
 real_ke_ideal_term_metric
 {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
   real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
   real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m, r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done0{2} /\ not_done1{2} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} MI.adv{2} (MI.func{1} ++ [2])
          MI.in_guard{2} m{2} r{2}.
exlim
  (real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|}) => met.
have [_ [IH_second _]] := IH.
call IH_second.
auto.
inline SMCSec1Bridge_BotRightKE(KeyEx.KEIdeal).rest.
sp 5 0.
seq 1 1 :
  (={glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv,
     glob Adv} /\
   r0{1} = r{2} /\ not_done00{1} = not_done0{2} /\
   not_done10{1} = not_done1{2} /\ not_done2{1} = not_done{2}).
sim; smt().
if => //.
sim.
rcondf{1} 1; first auto.
rcondf{2} 1; first auto.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
(* end of use of part 2 of induction *)
rcondt{2} 1; first auto; smt().
rcondf{2} 2; first auto.
rcondt{2} 2; first auto.
rcondt{2} 5; first auto.
move => &hr /> <- [#] -> /=.
by rewrite negb_or not_dir.
rcondf{2} 7; first auto.
move => &hr /> <- [#] -> -> /=; smt(incP).
rcondt{2} 7; first auto.
move => &hr /> <- [#] -> ->.
rewrite /=; smt(incP).
rcondf{2} 8; first auto.
rcondf{2} 8; first auto.
sp 0 10.
rcondf{2} 1; first auto.
move => &hr />; smt(inc_nle_l).
rcondf{2} 1; first auto.
rcondf{2} 1; first auto.
rcondt{2} 1; first auto.
rcondf{2} 3; first auto.
move => &hr />.
smt(inc_nle_l).
inline{2} (1) CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubAdv.invoke.
rcondt{2} 4; first auto.
rcondf{2} 7; first auto.
sp 0 9.
rcondf{2} 1; first auto.
move => &hr /> <- //.
if; first auto => &1 &2 /> <- //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto; progress; by rewrite some_oget.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
sp 2 2.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
move => &hr /> <- //.
inline{1} (1) SMCReal(KeyEx.KEIdeal).invoke.
inline{2} (1) SMCReal(CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubKE).invoke.
sp 4 4.
if; first auto => &1 &2 /> <- //.
inline{1} (1) SMCReal(KeyEx.KEIdeal).loop.
inline{2} (1) SMCReal(CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubKE).loop.
sp 3 3.
conseq
  (_ :
   not_done{1} /\ not_done1{1} /\ not_done{2} /\ not_done2{2} /\
   ={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   m1{1} = m2{2} /\
   (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = MI.func{1} /\
    (m1{1}.`2.`2 = 1 \/ m1{1}.`2.`2 = 2 \/ m1{1}.`2.`2 = 3 \/ m1{1}.`2.`2 = 4) \/
    MI.func{1} ++ [1] <= m1{1}.`2.`1 \/
    (m1{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m1{1}.`2.`1)) /\
   real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _).
move => &1 &2 /> /#.
(* use part 1 of induction *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KeyEx.KEIdeal).rest(m1, r1);}
(={m1, r1, glob MI, glob SMCReal, glob KeyEx.KEIdeal,
   glob Adv} /\
 not_done{1} /\ not_done1{1} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob Adv})
(={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 m1{1} = m2{2} /\
 (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = MI.func{1} /\
  (m1{1}.`2.`2 = 1 \/ m1{1}.`2.`2 = 2 \/ m1{1}.`2.`2 = 3 \/ m1{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m1{1}.`2.`1 \/
  (m1{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m1{1}.`2.`1)) /\
 real_ke_ideal_term_metric
 {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
   real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
   real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 not_done{2} /\ not_done2{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} m2{2} r1{1}.
inline SMCSec1Bridge_Left(KeyEx.KEIdeal).rest.
sp 0 4.
seq 3 1 :
  (={glob MI, glob SMCReal, glob KeyEx.KEIdeal,
     glob Adv} /\
   r{1} = r2{2} /\ not_done{1} = not_done2{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim; smt().
transitivity{2}
{r <@ SMCSec1Bridge_TopRight(KeyEx.KEIdeal).rest(m2, r2);}
(={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 m1{1} = m2{2} /\
 (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = MI.func{1} /\
  (m1{1}.`2.`2 = 1 \/ m1{1}.`2.`2 = 2 \/ m1{1}.`2.`2 = 3 \/ m1{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m1{1}.`2.`1 \/
  (m1{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m1{1}.`2.`1)) /\
  real_ke_ideal_term_metric
  {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
    real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
    real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
    real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m2, r2, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done2{2} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          MI.adv{2} (MI.func{1} ++ [2]) MI.in_guard{2} m2{2} r2{2}.
exlim
  (real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|}) => met.
have [IH_first _] := IH.
call IH_first.
auto.
inline SMCSec1Bridge_TopRight(KeyEx.KEIdeal).rest.
sp 4 0.
seq 1 3 :
  (={glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv,
     glob Adv} /\
   r3{1} = r{2} /\ not_done3{1} = not_done{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
(* end of use of part 1 of induction *)
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
(* SMCSec1Bridge_Left(KeyEx.KEIdeal).rest ~
   SMCSec1Bridge_BotRightAdv(KeyEx.KEIdeal).rest *)
proc.
rcondt{1} 3; first auto.
rcondt{2} 3; first auto.
rcondt{2} 5; first auto.
rcondf{1} 3; first auto; smt(not_le_ext_nonnil_l).
rcondf{1} 3; first auto; smt(not_le_ext_nonnil_l).
rcondf{1} 3; first auto; smt(not_le_other_branch).
sp 2 4.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ not_done0{1} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\
   (r{1} = None \/
    real_ke_ideal_term_metric
    {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
      real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
      real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
      real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n)).
exlim (KeyEx.ke_ideal_term_metric KeyEx.KEIdeal.st{1}) => ke_met.
call (KeyEx.ke_ideal_term_invoke ke_met).
auto; smt(real_ke_ideal_term_metric0 KeyEx.ge0_ke_ideal_term_metric).
case (r{1} = None).
rcondf{1} 1; first auto.
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{2} 1; first auto.
rcondf{2} 2; first auto.
rcondf{2} 2; first auto.
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
auto.
rcondf{2} 1; first auto.
case (MI.func{1} ++ [2] <= (oget r{1}).`2.`1).
rcondt{1} 1; first auto; smt(not_le_ext_nonnil_l le_trans le_ext_r).
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
rcondt{2} 4; first auto. 
rcondf{2} 6; first auto.
rcondf{2} 6; first auto.
rcondt{2} 6; first auto.
rcondf{2} 7; first auto.
auto.
rcondf{2} 4; first auto.
case ((oget r{1}).`1 = Dir).
rcondt{2} 4; first auto.
case (MI.adv{1} <= (oget r{1}).`2.`1).
rcondt{2} 5; first auto.
rcondf{2} 6; first auto.
rcondf{2} 6; first auto.
rcondt{2} 6; first auto.
rcondf{2} 7; first auto.
rcondt{1} 1; first auto; smt(incP not_dir not_le_ext_nonnil_l).
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
auto.
rcondf{2} 5; first auto.
rcondf{2} 5; first auto.
rcondt{2} 5; first auto.
rcondt{2} 8; first auto.
rcondf{2} 10; first auto.
rcondf{2} 13; first auto.
move => &hr /> /=.
smt(inc_le1_not_rl le_ext_r).
rcondf{2} 13; first auto.
move => &hr /> /=.
smt(inc_le1_not_rl le_ext_r).
rcondt{2} 13; first auto.
rcondt{2} 15; first auto.
move => &hr /> /=.
smt(inc_le1_not_rl le_ext_r).
inline{2} (1) SMCReal(CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubKE).invoke.
rcondt{2} 19; first auto.
move => &hr /> /=. smt(le_refl).
inline{2} (1) SMCReal(CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubKE).loop.
rcondt{2} 22; first auto.
rcondf{2} 22; first auto.
move => &hr /> /=.
smt(ne_cat_nonnil_r).
rcondf{2} 22; first auto.
rcondf{2} 22; first auto.
move => &hr /> /=.
rewrite (not_le_other_branch MI.func{m} (MI.func{m} ++ [2]) 2 1) // le_refl.
inline{2} (1) CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubKE.invoke.
rcondt{2} 23; first auto.
sp 0 25.
if; first auto => &1 &2 />.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
rcondt{2} 5; first auto.
rcondf{2} 6; first auto.
auto.
rcondf{1} 1; first auto; smt(le_refl).
rcondf{2} 1; first auto.
move => &hr />; smt(le_refl).
sp 1 1.
conseq
  (_ :
   not_done{1} /\ not_done0{1} /\ not_done{2} /\ not_done1{2} /\
   ={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   m{1} = m1{2} /\
   (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
    (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
    MI.func{1} ++ [1] <= m{1}.`2.`1 \/
    (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
   real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _).
move => &1 &2 />; smt().
(* use part 1 of induction *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KeyEx.KEIdeal).rest(m, r);}
(={m, r, glob MI, glob SMCReal, glob KeyEx.KEIdeal,
   glob Adv} /\
 not_done{1} /\ not_done0{1} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob Adv})
(={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 m{1} = m1{2} /\
 (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
  (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m{1}.`2.`1 \/
  (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
 real_ke_ideal_term_metric
 {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
   real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
   real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 not_done{2} /\ not_done1{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          m1{2} r{1}.
inline SMCSec1Bridge_Left(KeyEx.KEIdeal).rest.
sp 0 4.
sim; smt().
transitivity{2}
{r <@ SMCSec1Bridge_TopRight(KeyEx.KEIdeal).rest(m1, r1);}
(={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 m{1} = m1{2} /\
 (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{1} /\
  (m{1}.`2.`2 = 1 \/ m{1}.`2.`2 = 2 \/ m{1}.`2.`2 = 3 \/ m{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m{1}.`2.`1 \/
  (m{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m{1}.`2.`1)) /\
  real_ke_ideal_term_metric
  {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
    real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
    real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
    real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m1, r1, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done1{2} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} MI.adv{2} (MI.func{1} ++ [2])
          MI.in_guard{2} m1{2} r1{2}.
exlim
  (real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|}) => met.
have [IH_first _] := IH.
call IH_first.
auto.
inline SMCSec1Bridge_TopRight(KeyEx.KEIdeal).rest.
sp 4 0.
seq 1 3 :
  (={glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv,
     glob Adv} /\
   r3{1} = r{2} /\ not_done2{1} = not_done{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
(* end of use of part 1 of induction *)
rcondf{2} 4; first auto.
case ((oget r{1}).`2.`1 <> MI.adv{1} \/ (oget r{1}).`2.`2 = 0).
rcondt{2} 4; first auto.
rcondf{2} 6; first auto.
rcondf{2} 6; first auto.
rcondt{2} 6; first auto.
rcondf{2} 7; first auto.
if{1}.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
auto.
rcondt{1} 1; first auto; smt().
rcondf{1} 2; first auto.
rcondf{1} 2; first auto.
rcondf{1} 5; first auto; smt().
rcondf{1} 5; first auto.
rcondt{1} 5; first auto.
rcondf{1} 7; first auto.
auto.
rcondf{2} 4; first auto.
rcondt{2} 4; first auto.
rcondf{2} 6; first auto.
rcondf{1} 1; first auto.
move => /> &hr; case (r{m}) => // [[]] ? [] ? ? ? ?.
rewrite not_dir negb_or /=.
smt(inc_nle_l).
rcondt{1} 1; first auto; smt().
rcondf{1} 2; first auto.
rcondf{1} 2; first auto.
rcondf{1} 5; first auto; smt().
rcondf{1} 5; first auto.
rcondf{1} 5; first auto.
rcondt{1} 5; first auto.
rcondf{1} 7; first auto; smt().
sp 6 5.
seq 1 1 :
  (!not_done0{1} /\ not_done{1} /\ not_done{2} /\ not_done0{2} /\
   ={r, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None /\
   real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n).
call (_ : true).
auto; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondf{2} 2; first auto.
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
auto.
sp 3 3.
if; first smt().
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondf{2} 3; first auto.
rcondt{2} 3; first auto.
rcondf{2} 4; first auto.
auto.
case (MI.func{1} ++ [2] <= (oget r{1}).`2.`1).
rcondf{2} 1; first auto; smt().
rcondf{1} 1; first auto; smt(le_ext_r le_trans).
rcondt{1} 1; first auto.
rcondt{1} 3; first auto; smt(le_ext_r le_trans).
inline{1} (1) SMCReal(KeyEx.KEIdeal).invoke.
rcondt{1} 7; first auto.
move => |> &hr <- [#] -> -> /=.
by rewrite negb_or not_dir.
inline{1} (1) SMCReal(KeyEx.KEIdeal).loop.
sp 9 0.
conseq
  (_ :
   not_done{1} /\ not_done1{1} = true /\ not_done{2} /\ not_done0{2} /\
   ={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   m1{1} = m{2} /\
   m1{1}.`1 = Adv /\ MI.func{1} ++ [2] <= m1{1}.`2.`1 /\
   real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _).
move => &1 &2 />. rewrite negb_or not_dir /#.
(* use part 3 of induction: *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KeyEx.KEIdeal).rest(m1, r1);}
(={m1, r1, glob MI, glob SMCReal, glob KeyEx.KEIdeal,
   glob Adv} /\
 not_done{1} /\ not_done1{1} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob Adv})
(={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 m1{1} = m{2} /\
 m1{1}.`1 = Adv /\ MI.func{1} ++ [2] <= m1{1}.`2.`1 /\
 real_ke_ideal_term_metric
 {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
   real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
   real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 not_done{2} /\ not_done0{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          m{2} r1{1}.
inline SMCSec1Bridge_Left(KeyEx.KEIdeal).rest.
sp 0 4.
seq 3 1 :
  (={glob MI, glob SMCReal, glob KeyEx.KEIdeal,
     glob Adv} /\
   r{1} = r2{2} /\ not_done{1} = not_done2{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
transitivity{2}
{r <@ SMCSec1Bridge_BotRightAdv(KeyEx.KEIdeal).rest(m, r);}
(={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 m1{1} = m{2} /\
 m1{1}.`1 = UCCore'.Adv /\ MI.func{1} ++ [2] <= m1{1}.`2.`1 /\
 real_ke_ideal_term_metric
 {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
   real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
   real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m, r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done0{2} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          MI.adv{2} (MI.func{1} ++ [2]) MI.in_guard{2} m{2} r{2}.
exlim
  (real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|}) => met.
have [_ [_ IH_third]] := IH.
call IH_third.
auto.
inline SMCSec1Bridge_BotRightAdv(KeyEx.KEIdeal).rest.
sp 4 0.
seq 2 2 :
  (={glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv,
     glob Adv} /\
   r0{1} = r{2} /\ not_done00{1} = not_done0{2} /\ not_done1{1} = not_done{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
(* end of use of part 3 of induction *)
rcondt{2} 1; first auto; smt().
rcondf{2} 2; first auto.
rcondt{2} 2; first auto.
rcondf{2} 5; first auto; smt().
rcondf{2} 5; first auto.
rcondf{2} 8; first auto; smt().
sp 0 7.
if; first smt().
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
rcondt{1} 3; first auto; smt().
rcondt{2} 3; first auto; smt().
sp 2 2.
inline{1} (1) SMCReal(KeyEx.KEIdeal).invoke.
inline{2} (1) SMCReal(CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubKE).invoke.
sp 4 4.
if; first smt().
inline{1} (1) SMCReal(KeyEx.KEIdeal).loop.
inline{2} (1) SMCReal(CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubKE).loop.
sp 3 3.
conseq
  (_ :
   not_done{1} /\ not_done1{1} /\ not_done{2} /\ not_done1{2} /\
   ={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   m1{1} = m1{2} /\
   (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = MI.func{1} /\
    (m1{1}.`2.`2 = 1 \/ m1{1}.`2.`2 = 2 \/ m1{1}.`2.`2 = 3 \/ m1{1}.`2.`2 = 4) \/
    MI.func{1} ++ [1] <= m1{1}.`2.`1 \/
    (m1{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m1{1}.`2.`1)) /\
   real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
   (adv_fw_pi \in MI.in_guard{2}) /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   _); first smt().
(* use part 1 of induction *)
transitivity{1}
{r <@ SMCSec1Bridge_Left(KeyEx.KEIdeal).rest(m1, r1);}
(={m1, r1, glob MI, glob SMCReal, glob KeyEx.KEIdeal,
   glob Adv} /\
 not_done{1} /\ not_done1{1} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob Adv})
(={m1, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = MI.func{1} /\
  (m1{1}.`2.`2 = 1 \/ m1{1}.`2.`2 = 2 \/ m1{1}.`2.`2 = 3 \/ m1{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m1{1}.`2.`1 \/
  (m1{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m1{1}.`2.`1)) /\
 real_ke_ideal_term_metric
 {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
   real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
   real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
   real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 not_done{2} /\ not_done1{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          m1{2} r1{1}.
inline SMCSec1Bridge_Left(KeyEx.KEIdeal).rest.
sp 0 4.
seq 3 1 :
  (={glob MI, glob SMCReal, glob KeyEx.KEIdeal,
     glob Adv} /\
   r{1} = r2{2} /\ not_done{1} = not_done2{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim; smt().
transitivity{2}
{r <@ SMCSec1Bridge_TopRight(KeyEx.KEIdeal).rest(m1, r1);}
(={m1, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = MI.func{1} /\
  (m1{1}.`2.`2 = 1 \/ m1{1}.`2.`2 = 2 \/ m1{1}.`2.`2 = 3 \/ m1{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m1{1}.`2.`1 \/
  (m1{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m1{1}.`2.`1)) /\
  real_ke_ideal_term_metric
  {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
    real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
    real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
    real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|} = n /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m1, r1, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done1{2} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          MI.adv{2} (MI.func{1} ++ [2]) MI.in_guard{2} m1{2} r1{2}.
exlim
  (real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|}) => met.
have [IH_first _] := IH.
call IH_first.
auto.
inline SMCSec1Bridge_TopRight(KeyEx.KEIdeal).rest.
sp 4 0.
seq 1 3 :
  (={glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv,
     glob Adv} /\
   r2{1} = r{2} /\ not_done2{1} = not_done{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim; smt().
(* end of use of part 1 of induction *)
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
qed.

local lemma smc_sec1_ke_ideal_bridge_invoke :
  equiv
  [MI(SMCReal(KeyEx.KEIdeal), Adv).invoke ~
   MakeInt'.MI
   (SMCReal(CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubKE),
    CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubAdv).invoke :
   ={m, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   MakeInt'.MI.in_guard{2} \subset MI.in_guard{2} /\
   adv_fw_pi \in MI.in_guard{2} /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None ==>
   ={res, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   CompEnv.stub_st{2} = None].
proof.
proc => /=.
sp 2 2.
if => //.
inline MI(SMCReal(KeyEx.KEIdeal), Adv).loop.
inline MakeInt'.MI
       (SMCReal(CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubKE),
        CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubAdv).loop.
sp 3 3.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
sp 2 2.
if => //.
inline{1} (1) SMCReal(KeyEx.KEIdeal).invoke.
inline{2} (1) SMCReal(CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubKE).invoke.
sp 4 4.
if => //.
inline{1} (1) SMCReal(KeyEx.KEIdeal).loop.
inline{2} (1) SMCReal(CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubKE).loop.
sp 3 3.
transitivity{1}
{r <@ SMCSec1Bridge_Left(KeyEx.KEIdeal).rest(m2, r2);}
(={m2, r2, glob MI, glob SMCReal, glob KeyEx.KEIdeal,
   glob Adv} /\
 not_done{1} /\ not_done0{1} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob Adv})
(={m2, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 (m2{1}.`1 = Dir /\ m2{1}.`2.`1 = MI.func{1} /\
  (m2{1}.`2.`2 = 1 \/ m2{1}.`2.`2 = 2 \/ m2{1}.`2.`2 = 3 \/ m2{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m2{1}.`2.`1 \/
  (m2{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m2{1}.`2.`1)) /\
 not_done{2} /\ not_done0{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 MakeInt'.MI.in_guard{2} \subset MI.in_guard{2} /\
 adv_fw_pi \in MI.in_guard{2} /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
progress.
exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
       SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
       Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
       KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
       (mod1{2}, (addr11{2}, n11{2}), pt21{2}, u1{2}) None.
progress; smt(not_dir).
inline SMCSec1Bridge_Left(KeyEx.KEIdeal).rest.
sp 0 4.
seq 3 1 :
  (={glob MI, glob SMCReal, glob KeyEx.KEIdeal,
     glob Adv} /\
   r0{1} = r3{2} /\ not_done{1} = not_done1{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
transitivity{2}
{r <@ SMCSec1Bridge_TopRight(KeyEx.KEIdeal).rest(m2, r2);}
(={m2, MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 (m2{1}.`1 = Dir /\ m2{1}.`2.`1 = MI.func{1} /\
  (m2{1}.`2.`2 = 1 \/ m2{1}.`2.`2 = 2 \/ m2{1}.`2.`2 = 3 \/ m2{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m2{1}.`2.`1 \/
  (m2{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m2{1}.`2.`1)) /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 MakeInt'.MI.in_guard{2} \subset MI.in_guard{2} /\
 adv_fw_pi \in MI.in_guard{2} /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={m2, r2, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv,
   glob Adv} /\
 not_done{2} /\ not_done0{2} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2}
          None MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} MI.adv{2} (MI.func{1} ++ [2]) MI.in_guard{2}
          m2{2} r2{2}.
exlim
  (real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|}) => met.
have [lem_first _] := smc_sec1_ke_ideal_bridge_induction met.
call lem_first.
auto.
inline SMCSec1Bridge_TopRight(KeyEx.KEIdeal).rest.
sp 4 0.
seq 1 3 :
  (={glob MI, glob SMCReal, glob KeyEx.KEIdeal,
     glob Adv, glob CompEnv, glob MakeInt'.MI} /\
   r3{1} = r0{2} /\ not_done1{1} = not_done{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
inline{2} (1) CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubAdv.invoke.
rcondf{2} 2; first auto.
inline{2} (1) MI(KeyEx.KEIdeal, Adv).invoke.
rcondt{2} 5; first auto; smt().
inline{2} (1) MI(KeyEx.KEIdeal, Adv).loop.
rcondt{2} 8; first auto.
rcondf{2} 10; first auto; smt(not_le_ext).
sp 0 9.
seq 1 1 :
  (r0{1} = r3{2} /\ not_done{1} /\ not_done{2} /\ not_done0{2} /\
   ={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   MakeInt'.MI.in_guard{2} \subset MI.in_guard{2} /\
   adv_fw_pi \in MI.in_guard{2} /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\
   MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None).
call (_ : true).
auto.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondf{2} 4; first auto.
rcondt{2} 5; first auto.
rcondf{2} 6; first auto.
auto.
sp 3 3.
if; first smt().
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondf{2} 5; first auto.
rcondt{2} 6; first auto.
rcondf{2} 7; first auto.
auto.
case (MI.func{2} <= addr13{2}).
rcondf{1} 1; first auto; smt(le_ext_r le_trans).
rcondt{1} 1; first auto.
rcondt{1} 3; first auto; smt(le_ext_r le_trans).
inline{1} (1) SMCReal(KeyEx.KEIdeal).invoke.
rcondt{1} 7; first auto.
move => |> &hr <- /=; rewrite negb_or not_dir /#.
rcondf{2} 1; first auto.
inline{1} (1) SMCReal(KeyEx.KEIdeal).loop.
sp 9 0.
transitivity{1}
{r <@ SMCSec1Bridge_Left(KeyEx.KEIdeal).rest(m2, r2);}
(={m2, r2, glob MI, glob SMCReal, glob KeyEx.KEIdeal,
   glob Adv} /\
 not_done{1} /\ not_done0{1} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob Adv})
(={ MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 m2{1} = m3{2} /\ oget r3{2} = m3{2} /\
 m2{1}.`1 = Adv /\ MI.func{1} ++ [2] <= m2{1}.`2.`1 /\
 not_done{2} /\ not_done0{2} /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 MakeInt'.MI.in_guard{2} \subset MI.in_guard{2} /\
 adv_fw_pi \in MI.in_guard{2} /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
move => |> &1 &2 <- [#] -> ->; progress.
exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
       SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
       Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
       KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
       (mod3{2}, (addr13{2}, n13{2}), pt23{2}, u3{2}) None.
progress; rewrite negb_or not_dir in H6; smt().
inline SMCSec1Bridge_Left(KeyEx.KEIdeal).rest.
sp 0 4.
seq 3 1 :
  (={glob MI, glob SMCReal, glob KeyEx.KEIdeal,
     glob Adv} /\
   r0{1} = r3{2} /\ not_done{1} = not_done1{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
transitivity{2}
{r <@ SMCSec1Bridge_BotRightAdv(KeyEx.KEIdeal).rest(m3, r3);}
(={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 m2{1} = m3{2} /\
 m2{1}.`1 = Adv /\ MI.func{1} ++ [2] <= m2{1}.`2.`1 /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 MakeInt'.MI.in_guard{2} \subset MI.in_guard{2} /\
 adv_fw_pi \in MI.in_guard{2} /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv, glob Adv} /\
 ={m3, r3} /\ not_done{2} /\ not_done0{2} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2} None
          MI.adv{2} MI.func{1} SMCReal.st1{2} SMCReal.st2{2}
          Fwd.Forw.adv{2} Fwd.Forw.self{2} Fwd.Forw.st{2}
          KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
          MI.adv{2} (MI.func{1} ++ [2]) MI.in_guard{2} (oget r3{2}) r3{2}.
exlim
  (real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|}) => met.
have [_ [_ lem_third]] := smc_sec1_ke_ideal_bridge_induction met.
call lem_third.
auto.
inline SMCSec1Bridge_BotRightAdv(KeyEx.KEIdeal).rest.
sp 4 0.
seq 1 3 :
  (={glob MI, glob SMCReal, glob KeyEx.KEIdeal,
     glob Adv, glob CompEnv, glob MakeInt'.MI} /\
   r4{1} = r1{2} /\ not_done1{1} = not_done{2}).
sim; smt().
seq 1 2 :
  (={glob MI, glob SMCReal, glob KeyEx.KEIdeal,
     glob Adv, glob CompEnv, glob MakeInt'.MI} /\
   r4{1} = r0{2} /\ not_done1{1} = not_done{2}).
sim.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
rcondt{2} 1; first auto.
rcondf{2} 2; first auto.
rcondt{2} 4; first auto.
rcondf{2} 7; first auto; smt().
rcondf{2} 8; first auto.
rcondf{2} 11; first auto; smt().
sp 0 10.
if; first smt().
rcondf{1} 2; first auto. rcondf{2} 2; first auto.
auto.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
rcondt{1} 3; first auto; smt().
rcondt{2} 3; first auto; smt().
inline{1} (1) SMCReal(KeyEx.KEIdeal).invoke.
inline{2} (1) SMCReal(CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubKE).invoke.
sp 6 6.
if; first smt().
inline{1} (1) SMCReal(KeyEx.KEIdeal).loop.
inline{2} (1) SMCReal(CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubKE).loop.
sp 3 3.
transitivity{1}
{r <@ SMCSec1Bridge_Left(KeyEx.KEIdeal).rest(m2, r2);}
(={m2, r2, glob MI, glob SMCReal, glob KeyEx.KEIdeal,
   glob Adv} /\
 not_done{1} /\ not_done0{1} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob Adv})
(={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 m2{1} = m5{2} /\
 (m2{1}.`1 = Dir /\ m2{1}.`2.`1 = MI.func{1} /\
  (m2{1}.`2.`2 = 1 \/ m2{1}.`2.`2 = 2 \/ m2{1}.`2.`2 = 3 \/ m2{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m2{1}.`2.`1 \/
  (m2{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m2{1}.`2.`1)) /\
 not_done{2} /\ not_done1{2} /\ r5{2} = None /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None) => //.
move => |> &1 &2 not_done0_R <- [#] -> -> -> -> ->.
progress.
exists (glob Adv){2} MI.adv{2} MI.func{1} SMCReal.st1{2}
       SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
       Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
       KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1} MakeInt'.MI.in_guard{2}
       (mod1{2}, (addr11{2}, n11{2}), pt21{2}, u1{2}) None.
progress; smt().
inline SMCSec1Bridge_Left(KeyEx.KEIdeal).rest.
sp 0 4.
seq 3 1 :
  (={glob MI, glob SMCReal, glob KeyEx.KEIdeal,
     glob Adv} /\
   r0{1} = r3{2} /\ not_done{1} = not_done1{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
transitivity{2}
{r <@ SMCSec1Bridge_TopRight(KeyEx.KEIdeal).rest(m5, r5);}
(={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 m2{1} = m5{2} /\
 (m2{1}.`1 = Dir /\ m2{1}.`2.`1 = MI.func{1} /\
  (m2{1}.`2.`2 = 1 \/ m2{1}.`2.`2 = 2 \/ m2{1}.`2.`2 = 3 \/ m2{1}.`2.`2 = 4) \/
  MI.func{1} ++ [1] <= m2{1}.`2.`1 \/
  (m2{1}.`1 = Dir /\ MI.func{1} ++ [2] <= m2{1}.`2.`1)) /\
 exper_pre MI.func{1} MI.adv{1} /\
 MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
 (MakeInt'.MI.in_guard{2} \subset MI.in_guard{2}) /\
 (adv_fw_pi \in MI.in_guard{2}) /\
 MI.func{2} = MI.func{1} ++ [2] /\
 MakeInt'.MI.func{2} = MI.func{1} /\
 MakeInt'.MI.adv{2} = MI.adv{2} /\
 SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
 CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
 CompEnv.stub_st{2} = None ==>
 ={r, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
 CompEnv.stub_st{2} = None)
(={glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv,
   glob Adv} /\
 ={m5, r5} /\ not_done{2} /\ not_done1{2} ==>
 ={r, glob MI, glob SMCReal, glob KeyEx.KEIdeal, glob CompEnv, glob Adv}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{1} CompEnv.in_guard_low{2} None
          MI.adv{2} MI.func{1} SMCReal.st1{2}
          SMCReal.st2{2} Fwd.Forw.adv{2} Fwd.Forw.self{2}
          Fwd.Forw.st{2} KeyEx.KEIdeal.adv{2} KeyEx.KEIdeal.self{2}
          KeyEx.KEIdeal.st{2} MI.adv{2} MI.func{1}
          MakeInt'.MI.in_guard{2} MI.adv{2} (MI.func{1} ++ [2])
          MI.in_guard{2} m5{2} None.
exlim
  (real_ke_ideal_term_metric
   {|real_ke_ideal_term_met_st_p1s = SMCReal.st1{1};
     real_ke_ideal_term_met_st_p2s = SMCReal.st2{1};
     real_ke_ideal_term_met_st_fws = Fwd.Forw.st{1};
     real_ke_ideal_term_met_st_kes = KeyEx.KEIdeal.st{1}|}) => met.
have [lem_first _] := smc_sec1_ke_ideal_bridge_induction met.
call lem_first.
auto.
inline SMCSec1Bridge_TopRight(KeyEx.KEIdeal).rest.
sp 4 0.
seq 1 3 :
  (={glob MI, glob SMCReal, glob KeyEx.KEIdeal,
     glob Adv, glob CompEnv, glob MakeInt'.MI} /\
   r6{1} = r0{2} /\ not_done2{1} = not_done{2}).
sim; smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
rcondt{1} 2; first auto. rcondt{2} 2; first auto.
rcondf{1} 3; first auto. rcondf{2} 3; first auto.
auto.
auto.
qed.

lemma smc_sec1_ke_ideal_bridge
            (func' adv' : addr, in_guard_low' in_guard_hi' : int fset) &m :
  exper_pre func' adv' =>
  in_guard_low' \subset in_guard_hi' => adv_fw_pi \in in_guard_hi' =>
  CompEnv.in_guard_low{m} = in_guard_low' =>
  Pr[Exper(MI(SMCReal(KeyEx.KEIdeal), Adv), Env).main
       (func', adv', in_guard_low') @ &m : res] =
  Pr[Exper(MI(KeyEx.KEIdeal, Adv), CompEnv(Env)).main
       (func' ++ [2], adv', in_guard_hi') @ &m : res].
proof.
move => pre in_guard'_sub not_in_guard' ce_in_guard'_eq.
byequiv => //.
proc.
inline MI(SMCReal(KeyEx.KEIdeal), Adv).init
       MI(KeyEx.KEIdeal, Adv).init
       SMCReal(KeyEx.KEIdeal).init
       Exper(MI(KeyEx.KEIdeal, Adv), CompEnv(Env)).E.main
       Exper
       (MI'
        (SMCReal
         (CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubKE),
          CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubAdv),
        Env).main
       MakeInt'.MI
       (SMCReal
        (CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubKE),
         CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubAdv).init
       CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubKE.init
       CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubAdv.init
       SMCReal(CompEnv(Env, MI(KeyEx.KEIdeal, Adv)).StubKE).init.
seq 15 34 :
  (={adv, MI.adv, glob SMCReal,
     glob KeyEx.KEIdeal, glob Env, glob Adv} /\
   exper_pre func{1} adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   MakeInt'.MI.in_guard{2} \subset MI.in_guard{2} /\
   adv_fw_pi \in MI.in_guard{2} /\
   in_guard{1} = in_guard1{2} /\
   func{2} = func{1} ++ [2] /\ func0{2} = func{1} /\
   adv0{2} = adv{2} /\ 
   MI.func{1} = func{1} /\ MI.func{2} = func{2} /\
   MI.adv{1} = adv{1} /\ 
   MakeInt'.MI.func{2} = func{1} /\ MakeInt'.MI.adv{2} = adv{2} /\
   SMCReal.self{1} = func{1} /\ SMCReal.adv{1} = adv{1} /\
   CompEnv.func{2} = func{1} /\ CompEnv.adv{2} = adv{1} /\
   CompEnv.stub_st{2} = None).
swap{1} [11..12] 2.
swap{2} 28 6.
swap{2} [7..8] 26.
call (_ : true).
call KeyEx.ke_ideal_init.
call Fwd.term_init.
auto; progress; smt(size_cat take_size_cat).
wp.
call
  (_ :
   ={MI.adv, glob SMCReal, glob KeyEx.KEIdeal, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   MI.in_guard{1} = MakeInt'.MI.in_guard{2} /\
   MakeInt'.MI.in_guard{2} \subset MI.in_guard{2} /\
   adv_fw_pi \in MI.in_guard{2} /\
   MI.func{2} = MI.func{1} ++ [2] /\
   MakeInt'.MI.func{2} = MI.func{1} /\ MakeInt'.MI.adv{2} = MI.adv{2} /\
   SMCReal.self{1} = MI.func{1} /\ SMCReal.adv{1} = MI.adv{1} /\
   CompEnv.func{2} = MI.func{1} /\ CompEnv.adv{2} = MI.adv{1} /\
   CompEnv.stub_st{2} = None).
conseq smc_sec1_ke_ideal_bridge_invoke => // |>.
auto.
qed.

(* end of core of KEIdeal bridging lemma proof *)

end section.

section.

declare module Adv : FUNC{MI, SMCReal, KeyEx.KEReal, KeyEx.KEIdeal,
                          KeyEx.KESim, KeyEx.DDH_Adv, CompEnv}.
declare module Env : ENV{Adv, MI, SMCReal, KeyEx.KEReal, KeyEx.KEIdeal,
                         KeyEx.KESim, KeyEx.DDH_Adv, CompEnv}.

lemma smc_sec1 (func' adv' : addr, in_guard' : int fset) &m :
  exper_pre func' adv' => ! (ke_sim_adv_pi \in in_guard') =>
  CompEnv.in_guard_low{m} = in_guard' =>
  KeyEx.DDH_Adv.func{m} = func' ++ [2] => KeyEx.DDH_Adv.adv{m} = adv' =>
  KeyEx.DDH_Adv.in_guard{m} = in_guard' `|` fset1 adv_fw_pi =>
  `|Pr[Exper(MI(SMCReal(KeyEx.KEReal), Adv), Env).main
         (func', adv', in_guard') @ &m : res] -
    Pr[Exper(MI(SMCReal(KeyEx.KEIdeal), KeyEx.KESim(Adv)), Env).main
         (func', adv', in_guard') @ &m : res]| <=
  `|Pr[DDH1(KeyEx.DDH_Adv(CompEnv(Env), Adv)).main() @ &m : res] -
    Pr[DDH2(KeyEx.DDH_Adv(CompEnv(Env), Adv)).main() @ &m : res]|.
proof.
move => pre not_in_guard' ce_in_guard'_eq
        ddh_func'_eq ddh_adv'_eq ddh_in_guard'_eq.
rewrite (smc_sec1_ke_real_bridge Adv Env func' adv'
         in_guard' (in_guard' `|` fset1 adv_fw_pi) &m) //
        1:subset_union_l 1:in_fsetU1 //.
rewrite (smc_sec1_ke_ideal_bridge (KeyEx.KESim(Adv)) Env func' adv'
         in_guard' (in_guard' `|` fset1 adv_fw_pi) &m) //
        1:subset_union_l 1:in_fsetU1 //.
rewrite (KeyEx.ke_security Adv (CompEnv(Env)) (func' ++ [2]) adv'
         (in_guard' `|` fset1 adv_fw_pi) &m) 1:exper_pre_ext1 //.
smt(in_fsetU1 smc_pi_uniq).
qed.

end section.

lemma smc_security1
      (Adv <: FUNC{MI, SMCReal, KeyEx.KEReal, KeyEx.KEIdeal,
                   KeyEx.KESim, KeyEx.DDH_Adv, CompEnv})
      (Env <: ENV{Adv, MI, SMCReal, KeyEx.KEReal, KeyEx.KEIdeal,
                  KeyEx.KESim, KeyEx.DDH_Adv, CompEnv})
      (func' adv' : addr, in_guard' : int fset) &m :
  exper_pre func' adv' => ! (ke_sim_adv_pi \in in_guard') =>
  CompEnv.in_guard_low{m} = in_guard' =>
  KeyEx.DDH_Adv.func{m} = func' ++ [2] => KeyEx.DDH_Adv.adv{m} = adv' =>
  KeyEx.DDH_Adv.in_guard{m} = in_guard' `|` fset1 adv_fw_pi =>
  `|Pr[Exper(MI(SMCReal(KeyEx.KEReal), Adv), Env).main
         (func', adv', in_guard') @ &m : res] -
    Pr[Exper(MI(SMCReal(KeyEx.KEIdeal), KeyEx.KESim(Adv)), Env).main
         (func', adv', in_guard') @ &m : res]| <=
  `|Pr[DDH1(KeyEx.DDH_Adv(CompEnv(Env), Adv)).main() @ &m : res] -
    Pr[DDH2(KeyEx.DDH_Adv(CompEnv(Env), Adv)).main() @ &m : res]|.
proof.
move => pre not_in_guard' ce_in_guard'_eq
        ddh_func'_eq ddh_adv'_eq ddh_in_guard'_eq.
by apply (smc_sec1 Adv Env func' adv' in_guard' &m).
qed.

(* padding isomorphism *)

op pad_iso_l (t : text, q : exp) : exp = log (inj t ^^ (g ^ q)).
op pad_iso_r (t : text, q : exp) : exp = log (kinv (inj t) ^^ (g ^ q)).

lemma pad_iso_lr (t : text) : cancel (pad_iso_l t) (pad_iso_r t).
proof.
rewrite /cancel /pad_iso_l /pad_iso_r => q.
by rewrite -/(gen q) -/(gen (log (inj t ^^ (g ^ q))))
   log_gen -kmulA kinv_l kid_l gen_log.
qed.

lemma pad_iso_rl (t : text) : cancel (pad_iso_r t) (pad_iso_l t).
proof.
rewrite /cancel /pad_iso_l /pad_iso_r => q.
by  rewrite -/(gen q) -/(gen (log (kinv (inj t) ^^ gen q)))
            log_gen -kmulA kinv_r kid_l gen_log.
qed.

section.

declare module Adv : FUNC{MI, SMCReal, SMCIdeal, SMCSim, KeyEx.KEIdeal}.
declare module Env : ENV{Adv, MI, SMCReal, SMCIdeal, SMCSim, KeyEx.KEIdeal}.

local clone import SMCRealKEIdealSimp as SRKEIS.

(* relational invariant for connecting SMCRealKEIdealSimp and
   SMCIdeal *)

type smc_sec2_rel_st = {
  smc_sec2_rel_st_func : addr;
  smc_sec2_rel_st_adv  : addr;
  smc_sec2_rel_st_riss : smc_real_ke_ideal_simp_state;
  smc_sec2_rel_st_is   : smc_ideal_state;
  smc_sec2_rel_st_sims : smc_sim_state;
}.

pred smc_sec2_rel0 (st : smc_sec2_rel_st) =
  (st.`smc_sec2_rel_st_riss = SMCRealKEIdealSimpStateWaitReq) /\
  (st.`smc_sec2_rel_st_is   = SMCIdealStateWaitReq) /\
  (st.`smc_sec2_rel_st_sims = SMCSimStateWaitReq).

pred smc_sec2_rel1
     (st : smc_sec2_rel_st, pt1 pt2 : port, t : text) =
  ! (st.`smc_sec2_rel_st_func <= pt1.`1) /\
  ! (st.`smc_sec2_rel_st_func <= pt2.`1) /\
  ! (st.`smc_sec2_rel_st_adv <= pt1.`1) /\
  ! (st.`smc_sec2_rel_st_adv <= pt2.`1) /\
  (st.`smc_sec2_rel_st_riss =
   SMCRealKEIdealSimpStateWaitAdv1 (pt1, pt2, t)) /\
  (st.`smc_sec2_rel_st_is = SMCIdealStateWaitSim (pt1, pt2, t)) /\
  (st.`smc_sec2_rel_st_sims =
   SMCSimStateWaitAdv1 (pt1, pt2, st.`smc_sec2_rel_st_func)).

pred smc_sec2_rel2
     (st : smc_sec2_rel_st, pt1 pt2 : port, t : text, q : exp) =
  ! (st.`smc_sec2_rel_st_func <= pt1.`1) /\
  ! (st.`smc_sec2_rel_st_func <= pt2.`1) /\
  ! (st.`smc_sec2_rel_st_adv <= pt1.`1) /\
  ! (st.`smc_sec2_rel_st_adv <= pt2.`1) /\
  (st.`smc_sec2_rel_st_riss =
   SMCRealKEIdealSimpStateWaitAdv2 (pt1, pt2, t, g ^ q)) /\
  (st.`smc_sec2_rel_st_is = SMCIdealStateWaitSim (pt1, pt2, t)) /\
  (st.`smc_sec2_rel_st_sims =
   SMCSimStateWaitAdv2 (pt1, pt2, st.`smc_sec2_rel_st_func, pad_iso_l t q)).

pred smc_sec2_rel3
     (st : smc_sec2_rel_st, pt1 pt2 : port, t : text, q : exp) =
  ! (st.`smc_sec2_rel_st_func <= pt1.`1) /\
  ! (st.`smc_sec2_rel_st_func <= pt2.`1) /\
  ! (st.`smc_sec2_rel_st_adv <= pt1.`1) /\
  ! (st.`smc_sec2_rel_st_adv <= pt2.`1) /\
  (st.`smc_sec2_rel_st_riss =
   SMCRealKEIdealSimpStateWaitAdv3 (pt1, pt2, t, g ^ q)) /\
  (st.`smc_sec2_rel_st_is = SMCIdealStateWaitSim (pt1, pt2, t)) /\
  (st.`smc_sec2_rel_st_sims =
   SMCSimStateWaitAdv3 (pt1, pt2, st.`smc_sec2_rel_st_func, pad_iso_l t q)).

pred smc_sec2_rel4
     (st : smc_sec2_rel_st, pt1 pt2 : port, t : text, q : exp) =
  ! (st.`smc_sec2_rel_st_func <= pt1.`1) /\
  ! (st.`smc_sec2_rel_st_func <= pt2.`1) /\
  ! (st.`smc_sec2_rel_st_adv <= pt1.`1) /\
  ! (st.`smc_sec2_rel_st_adv <= pt2.`1) /\
  (st.`smc_sec2_rel_st_riss =
   SMCRealKEIdealSimpStateFinal (pt1, pt2, t, g ^ q)) /\
  (st.`smc_sec2_rel_st_is = SMCIdealStateFinal (pt1, pt2, t)) /\
  (st.`smc_sec2_rel_st_sims =
   SMCSimStateFinal (pt1, pt2, st.`smc_sec2_rel_st_func, pad_iso_l t q)).

inductive smc_sec2_rel (st : smc_sec2_rel_st) =
    SMCSec2Rel0 of (smc_sec2_rel0 st)
  | SMCSec2Rel1 (pt1 pt2 : port, t : text) of
      (smc_sec2_rel1 st pt1 pt2 t)
  | SMCSec2Rel2 (pt1 pt2 : port, t : text, q : exp) of
      (smc_sec2_rel2 st pt1 pt2 t q)
  | SMCSec2Rel3 (pt1 pt2 : port, t : text, q : exp) of
      (smc_sec2_rel3 st pt1 pt2 t q)
  | SMCSec2Rel4 (pt1 pt2 : port, t : text, q : exp) of
      (smc_sec2_rel4 st pt1 pt2 t q).

local module MI_SMCRealKEIdealSimp_AfterAdv = {
  proc after_adv(r : msg option) : msg option = {
    var not_done : bool <- true; var m : msg;
    var mod : mode; var pt1, pt2 : port;
    var addr1 : addr; var n1 : int; var u : univ;

    m <- oget r; (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
    if (MI.adv <= addr1 \/ mod = Dir) {
      r <- None; not_done <- false;
    }
    elif (! MI.func <= addr1) {
      not_done <- false;
    }
    while (not_done) {
      (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
      if (MI.func <= addr1) {
        r <@ SMCRealKEIdealSimp.invoke(m);
        if (r = None) {
          not_done <- false;
        }
        else {
          m <- oget r; (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
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
        }
        else {
          m <- oget r; (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
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

local module MI_SMCIdeal_SMCSim_AfterAdv = {
  proc after_adv(r : msg option) : msg option = {
    var not_done : bool <- true; var not_done0 <- true; var m : msg;
    var mod : mode; var pt1, pt2 : port;
    var addr1, addr2, addr : addr; var n1 : int; var u : univ;
    var q : exp;

    m <- oget r; (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
    if (mod = Dir \/ SMCSim.self <= addr1) {
      r <- None; not_done0 <- false;
    }
    elif (is_smc_sim_state_wait_adv1 SMCSim.st) {
      (pt1, pt2, addr) <- oget (dec_smc_sim_state_wait_adv1 SMCSim.st);
      not_done0 <- false;
      if (addr <= addr1) {
        r <- None;
        if (KeyEx.is_ke_sim_rsp m) {
          (addr1, addr2) <- oget (KeyEx.dec_ke_sim_rsp m);
          if (addr1 = addr ++ [2]) {
            q <$ dexp;
            m <- KeyEx.ke_sim_req2 (addr ++ [2]) SMCSim.self;
            not_done0 <- true;
            SMCSim.st <- SMCSimStateWaitAdv2 (pt1, pt2, addr, q);
          }
        }
      }
    }
    elif (is_smc_sim_state_wait_adv2 SMCSim.st) {
      (pt1, pt2, addr, q) <- oget (dec_smc_sim_state_wait_adv2 SMCSim.st);
      not_done0 <- false;
      if (addr <= addr1) {
        r <- None;
        if (KeyEx.is_ke_sim_rsp m) {
          (addr1, addr2) <- oget (KeyEx.dec_ke_sim_rsp m);
          if (addr1 = addr ++ [2]) {
            m <-
              Fwd.fw_obs
              (addr ++ [1]) SMCSim.self (addr, 3) (addr, 4)
              (univ_triple
               (UnivPort pt1) (UnivPort pt2)
               (UnivBase (BaseKey (g ^ q))));
            not_done0 <- true;
            SMCSim.st <- SMCSimStateWaitAdv3 (pt1, pt2, addr, q);
          }
        }
      }
    }
    elif (is_smc_sim_state_wait_adv3 SMCSim.st) {
      (pt1, pt2, addr, q) <- oget (dec_smc_sim_state_wait_adv3 SMCSim.st);
      not_done0 <- false;
      if (addr <= addr1) {
        r <- None;
        if (Fwd.is_fw_ok m) {
          (addr1, addr2) <- oget (Fwd.dec_fw_ok m);
          if (addr1 = addr ++ [1]) {
            r <-Some (smc_sim_rsp addr SMCSim.self);
            SMCSim.st <- SMCSimStateFinal (pt1, pt2, addr, q);
          }
        }
      }
    }
    else {
      not_done0 <- false;
    }
    while (not_done0) {
      (mod, pt1, pt2, u) <- m;
      if (pt1.`2 = smc_sim_adv_pi) {
        r <- None; not_done0 <- false;
        if (SMCSim.st = SMCSimStateWaitReq) {
          if (is_smc_sim_req m) {
            (addr1, addr2, pt1, pt2) <- oget (dec_smc_sim_req m);
            m <-
              KeyEx.ke_sim_req1 (addr1 ++ [2]) SMCSim.self
              (addr1, 3) (addr1, 4);
            not_done0 <- true;
            SMCSim.st <- SMCSimStateWaitAdv1 (pt1, pt2, addr1);
          }
        }
      }
      else {
        r <@ Adv.invoke(m);
        if (r = None) {
          not_done0 <- false;
        }
        else {
          m <- oget r; (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
          if (mod = Dir \/ SMCSim.self <= addr1) {
            r <- None; not_done0 <- false;
          }
          elif (is_smc_sim_state_wait_adv1 SMCSim.st) {
            (pt1, pt2, addr) <- oget (dec_smc_sim_state_wait_adv1 SMCSim.st);
            not_done0 <- false;
            if (addr <= addr1) {
              r <- None;
              if (KeyEx.is_ke_sim_rsp m) {
                (addr1, addr2) <- oget (KeyEx.dec_ke_sim_rsp m);
                if (addr1 = addr ++ [2]) {
                  q <$ dexp;
                  m <- KeyEx.ke_sim_req2 (addr ++ [2]) SMCSim.self;
                  not_done0 <- true;
                  SMCSim.st <- SMCSimStateWaitAdv2 (pt1, pt2, addr, q);
                }
              }
            }
          }
          elif (is_smc_sim_state_wait_adv2 SMCSim.st) {
            (pt1, pt2, addr, q) <- oget (dec_smc_sim_state_wait_adv2 SMCSim.st);
            not_done0 <- false;
            if (addr <= addr1) {
              r <- None;
              if (KeyEx.is_ke_sim_rsp m) {
                (addr1, addr2) <- oget (KeyEx.dec_ke_sim_rsp m);
                if (addr1 = addr ++ [2]) {
                  m <-
                    Fwd.fw_obs
                    (addr ++ [1]) SMCSim.self (addr, 3) (addr, 4)
                    (univ_triple
                     (UnivPort pt1) (UnivPort pt2)
                     (UnivBase (BaseKey (g ^ q))));
                  not_done0 <- true;
                  SMCSim.st <- SMCSimStateWaitAdv3 (pt1, pt2, addr, q);
                }
              }
            }
          }
          elif (is_smc_sim_state_wait_adv3 SMCSim.st) {
            (pt1, pt2, addr, q) <- oget (dec_smc_sim_state_wait_adv3 SMCSim.st);
            not_done0 <- false;
            if (addr <= addr1) {
              r <- None;
              if (Fwd.is_fw_ok m) {
                (addr1, addr2) <- oget (Fwd.dec_fw_ok m);
                if (addr1 = addr ++ [1]) {
                  r <-Some (smc_sim_rsp addr SMCSim.self);
                  SMCSim.st <- SMCSimStateFinal (pt1, pt2, addr, q);
                }
              }
            }
          }
          else {
            not_done0 <- false;
          }
        }
      }
    }
    if (r = None) {
      not_done <- false;
    }
    else {
      m <- oget r; (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
      if (MI.adv <= addr1 \/ mod = Dir) {
        r <- None; not_done <- false;
      }
      elif (! MI.func <= addr1) {
        not_done <- false;
      }
    }
    while (not_done) {
      (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
      if (MI.func <= addr1) {
        r <@ SMCIdeal.invoke(m);
        if (r = None) {
          not_done <- false;
        }
        else {
          m <- oget r; (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
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
        r <@ SMCSim(Adv).invoke(m);
        if (r = None) {
          not_done <- false;
        }
        else {
          m <- oget r; (mod, pt1, pt2, u) <- m; (addr1, n1) <- pt1;
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

local lemma MI_KEHybrid_KEIdeal_KESim_after_adv_3
            (pt1' pt2' : port, t' : text, q' : exp) :
  equiv
  [MI_SMCRealKEIdealSimp_AfterAdv.after_adv ~
   MI_SMCIdeal_SMCSim_AfterAdv.after_adv :
   ={r, MI.func, MI.adv, MI.in_guard, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   smc_sec2_rel3
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t' q' ==>
   ={res, glob Adv} /\
   smc_sec2_rel
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}].
proof.
proc.
sp 4 5.
if; first smt().
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondt{2} 3; first auto.
rcondf{2} 4; first auto.
auto; progress; by apply (SMCSec2Rel3 _ pt1' pt2' t' q').
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_smc_sim_state_wait_adv3).
case (! MI.func{1} <= addr1{1}).
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 3; first auto.
move =>
  |> &hr <- [#] -> -> _ _ _ _ [] /= _ [#] _ _ _ _ _ -> //.
rcondf{2} 3; first auto.
sp 0 2.
if{2}.
rcondf{2} 2; first auto.
auto; progress; by apply (SMCSec2Rel3 _ pt1' pt2' t' q').
rcondf{2} 4; first auto; smt().
rcondt{2} 4; first auto; smt().
rcondf{2} 5; first auto.
auto; progress; by apply (SMCSec2Rel3 _ pt1' pt2' t' q').
rcondf{1} 1; first auto.
rcondt{1} 1; first auto.
rcondt{1} 3; first auto; smt().
inline{1} (1) SMCRealKEIdealSimp.invoke.
rcondt{2} 3; first auto.
move => |> &hr <- [#] -> -> _ _ _ _ [] /= _ [#] _ _ _ _ _ -> //.
case (MI.func{2} ++ [1] = m{2}.`2.`1).
case (Fwd.is_fw_ok m{2}).
rcondt{2} 4; first auto.
rcondt{2} 5; first auto.
move =>
  |> &hr <- [#] -> -> _ _ _ _ [] /= _ [#] _ _ _ _ _ ->.
rewrite /= negb_or not_dir.
smt(Fwd.dest_good_fw_ok).
rcondt{1} 7; first auto.
move => |> &hr <- /= [#] -> -> <- <- <- _ _.
rewrite negb_or not_dir.
move => [#] _ -> _ -> _ /=.
left; apply le_refl.
inline{1} (1) SMCRealKEIdealSimp.parties.
rcondf{1} 9; first auto; smt().
rcondf{1} 9; first auto; smt().
rcondf{1} 9; first auto; smt().
rcondt{1} 9; first auto; smt(is_smc_real_ke_ideal_simp_state_wait_adv3).
rcondt{1} 10; first auto.
rcondt{1} 11; first auto; smt(Fwd.dest_good_fw_ok).
rcondf{1} 15; first auto.
rcondf{1} 18; first auto.
move => |> &hr <- [#] -> -> _ _ _ exp_pre [] /= _ [#] out_pt1'_func _ _ -> _ _.
by rewrite /smc_rsp.
rcondt{1} 18; first auto.
rcondf{1} 19; first auto.
move => |> &hr <- [#] -> -> _ _ _ exp_pre [] /= _ [#] _ _ out_pt2'_adv -> _ _.
by rewrite enc_dec_smc_real_ke_ideal_simp_state_wait_adv3 /=
           /smc_rsp.
rcondf{1} 19; first auto.
rcondf{2} 7; first auto.
rcondf{2} 7; first auto.
rcondf{2} 10; first auto.
move => |> &hr <- [#] -> -> _ _ _ exp [] /= _ [#] _ _ _ _ _ ->.
rewrite enc_dec_smc_sim_state_wait_adv3 /= /smc_sim_rsp /=.
smt(inc_nle_r).
rcondf{2} 10; first auto.
move => |> &hr <- [#] -> -> _ _ _ exp [] /= _ [#] _ _ _ _ _ ->.
rewrite enc_dec_smc_sim_state_wait_adv3 /= /smc_sim_rsp /=.
smt(le_refl).
rcondt{2} 10; first auto.
rcondt{2} 12; first auto.
move => |> &hr <- [#] -> -> _ _ _ exp [] /= _ [#] _ _ _ _ _ ->.
rewrite enc_dec_smc_sim_state_wait_adv3 /= /smc_sim_rsp /=.
smt(le_refl).
inline{2} (1) SMCIdeal.invoke.
rcondt{2} 16; first auto.
move => |> &hr <- [#] -> -> _ _ _ exp [] /= _ [#] _ _ _ _ _ ->.
by rewrite enc_dec_smc_sim_state_wait_adv3 /= /smc_sim_rsp.
inline{2} (1) SMCIdeal.parties.
rcondf{2} 18; first auto; smt().
rcondt{2} 18; first auto; smt(is_smc_ideal_state_wait_sim).
rcondt{2} 19; first auto.
rcondf{2} 24; first auto.
rcondf{2} 27; first auto.
move =>
  |> &hr <- [#] -> -> _ _ _ exppre [] /= _ [#] out_pt2'_func _ _ _ -> _.
by rewrite enc_dec_smc_ideal_state_wait_sim /= /smc_rsp.
rcondt{2} 27; first auto.
rcondf{2} 28; first auto.
move =>
  |> &hr <- [#] -> -> _ _ _ exppre [] /= _ [#] out_pt2'_func _ _ _ -> _.
by rewrite enc_dec_smc_ideal_state_wait_sim /= /smc_rsp.
rcondf{2} 28; first auto.
auto =>
  |> &1 &2 <- [#] -> -> _ _ _ exppre [] /= out_pt1'_func [#]
  out_pt2'_func out_pt1'_adv out_pt2'_adv -> -> ->
  /negb_or [#] _ _ _ _ _.
rewrite enc_dec_smc_sim_state_wait_adv3
        enc_dec_smc_real_ke_ideal_simp_state_wait_adv3
        enc_dec_smc_ideal_state_wait_sim /smc_rsp /=.
by rewrite (SMCSec2Rel4 _ pt1' pt2' t' q').
rcondf{2} 4; first auto.
rcondf{2} 4; first auto.
rcondt{2} 4; first auto.
rcondf{2} 5; first auto.
sp 6 0.
if{1}.
inline{1} (1) SMCRealKEIdealSimp.parties.
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondt{1} 3; first auto; smt(is_smc_real_ke_ideal_simp_state_wait_adv2).
rcondf{1} 4; first auto; smt().
rcondt{1} 6; first auto; smt().
rcondf{1} 7; first auto.
auto; progress; by apply (SMCSec2Rel3 _ pt1' pt2' t' q').
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto; progress; by apply (SMCSec2Rel3 _ pt1' pt2' t' q').
seq 10 0 :
  (r{1} = None /\
   not_done{2} = true /\ not_done0{2} = true /\
   m{2} = oget r{2} /\ (mod{2}, pt1{2}, pt2{2}, u{2}) = m{2} /\
   (addr1{2}, n1{2}) = pt1{2} /\
   ={MI.func, MI.adv, MI.in_guard, glob Adv} /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   smc_sec2_rel3
   {|smc_sec2_rel_st_func = MI.func{1}; smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t' q' /\
   mod{2} = Adv /\ m{2}.`2.`1 <= addr1{2} /\
   MI.func{2} ++ [1] <> m{2}.`2.`1).
sp.
if{1}.
inline{1} (1) SMCRealKEIdealSimp.parties.
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondt{1} 3; first auto; smt(is_smc_real_ke_ideal_simp_state_wait_adv3).
sp 3 0.
if{1}.
rcondf{1} 2; first auto; smt(Fwd.dest_good_fw_ok).
rcondt{1} 4; first auto.
rcondf{1} 5; first auto; smt(not_dir).
auto; smt(le_refl).
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
auto; smt(le_refl).
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto => |> &1 &2 <- [#] -> -> _ _ _ _ _ /= /negb_or [#] _ /not_dir ->.
smt(le_refl).
sp 0 3.
if{2}.
rcondf{2} 2; first auto.
move =>
  |> &hr r_R pt2_r oget_dec_smc_sim_state_wait_adv3 <-
  [] /= _ [#] _ _ _ _ _ ->>.
rewrite /= in oget_dec_smc_sim_state_wait_adv3.
smt(Fwd.dest_good_fw_ok).
rcondf{2} 2; first auto.
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
auto; progress; rewrite (SMCSec2Rel3 _ pt1' pt2' t' q') /#.
rcondf{2} 1; first auto.
rcondt{2} 1; first auto.        
rcondf{2} 2; first auto.
auto; progress; rewrite (SMCSec2Rel3 _ pt1' pt2' t' q') /#.
qed.

local lemma MI_KEHybrid_KEIdeal_KESim_after_adv_2
            (pt1' pt2' : port, t' : text, q' : exp) :
  equiv
  [MI_SMCRealKEIdealSimp_AfterAdv.after_adv ~
   MI_SMCIdeal_SMCSim_AfterAdv.after_adv :
   ={r, MI.func, MI.adv, MI.in_guard, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   smc_sec2_rel2
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t' q' ==>
   ={res, glob Adv} /\
   smc_sec2_rel
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}].
proof.
proc.
sp 4 5.
if; first smt().
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondt{2} 3; first auto.
rcondf{2} 4; first auto.
auto; progress; by apply (SMCSec2Rel2 _ pt1' pt2' t' q').
rcondf{2} 1; first auto; smt().
rcondt{2} 1; first auto; smt(is_smc_sim_state_wait_adv2).
case (! MI.func{1} <= addr1{1}).
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 3; first auto.
move => |> &hr <- [#] -> -> _ _ _ _ [] /= _ [#] _ _ _ _ _ -> //.
rcondf{2} 3; first auto.
sp 0 2.
if{2}.
rcondf{2} 2; first auto.
auto; progress; by apply (SMCSec2Rel2 _ pt1' pt2' t' q').
rcondf{2} 4; first auto; smt().
rcondt{2} 4; first auto; smt().
rcondf{2} 5; first auto.
auto; progress; by apply (SMCSec2Rel2 _ pt1' pt2' t' q').
rcondf{1} 1; first auto.
rcondt{1} 1; first auto.
rcondt{1} 3; first auto; smt().
inline{1} (1) SMCRealKEIdealSimp.invoke.
rcondt{2} 3; first auto.
move => |> &hr <- [#] -> -> _ _ _ _ [] /= _ [#] _ _ _ _ _ -> //.
case (MI.func{2} ++ [2] = m{2}.`2.`1).
case (KeyEx.is_ke_sim_rsp m{2}).
rcondt{2} 4; first auto.
rcondt{2} 5; first auto.
move => |> &hr <- [#] -> -> _ _ _ _ [] /= _ [#] _ _ _ _ _ ->.
rewrite negb_or not_dir.
move => [#] _ -> _.
smt(KeyEx.dest_good_ke_sim_rsp).
rcondt{1} 7; first auto.
move => |> &hr <- /= [#] -> -> <- <- <- _ _.
rewrite negb_or not_dir.
move => [#] _ -> _ -> _ /=.
right; apply le_refl.
inline{1} (1) SMCRealKEIdealSimp.parties.
rcondf{1} 9; first auto; smt().
rcondf{1} 9; first auto; smt().
rcondt{1} 9; first auto; smt(is_smc_real_ke_ideal_simp_state_wait_adv2).
rcondt{1} 10; first auto.
rcondt{1} 11; first auto; smt(KeyEx.dest_good_ke_sim_rsp).
rcondf{1} 15; first auto.
rcondf{1} 18; first auto.
move => |> &hr.
rewrite /Fwd.fw_obs /=; smt(inc_nle_r).
rcondf{1} 18; first auto.
rcondf{1} 18; first auto.
move => |> &hr.
rewrite /Fwd.fw_obs /=; smt(Fwd.fwd_pi_uniq).
rcondt{1} 18; first auto.
rcondf{1} 20; first auto.
move => |> &hr.
rewrite /Fwd.fw_obs /=; smt(inc_nle_r).
rcondt{2} 8; first auto.
rcondf{2} 9; first auto.
move => |> &hr.
rewrite /Fwd.fw_obs /=; smt(smc_pi_uniq).
seq 20 9 :
  (={r, MI.func, MI.adv, MI.in_guard, glob Adv} /\
   not_done{1} /\ not_done{2} /\ not_done0{2} /\
   exper_pre MI.func{1} MI.adv{1} /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\
   SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\
   SMCSim.adv{2} = [] /\
   smc_sec2_rel3
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t' q').
call (_ : true).
auto =>
  |> &1 &2 <- [#] -> -> _ _ _ _ [] /= out_pt1'_func [#]
  out_pt2'_func out_pt1'_adv out_pt2'_adv -> -> -> /negb_or
  [#] _ /not_dir -> _ _ _ //.
split => [| _ //].
congr; congr; first 5 smt().
congr; congr.
by rewrite /pad_iso_l -/(gen q') -/(gen (log (inj t' ^^ gen q')))
           log_gen.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
auto; progress; by apply (SMCSec2Rel3 _ pt1' pt2' t' q').
transitivity{1}
  {r <- MI_SMCRealKEIdealSimp_AfterAdv.after_adv(r);}
  (={r, MI.func, MI.adv, MI.in_guard,
     SMCRealKEIdealSimp.self, SMCRealKEIdealSimp.adv,
     SMCRealKEIdealSimp.st, glob Adv} /\
   not_done{1} ==>
   ={r, MI.func, MI.adv, MI.in_guard,
     SMCRealKEIdealSimp.self, SMCRealKEIdealSimp.adv,
     SMCRealKEIdealSimp.st, glob Adv})
  (={r} /\ r{1} <> None /\ not_done{2} /\ not_done0{2} /\
   ={MI.func, MI.adv, MI.in_guard, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   smc_sec2_rel3
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t' q' ==>
   ={r, glob Adv} /\
   smc_sec2_rel
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{2} SMCRealKEIdealSimp.st{1}
          MI.adv{2} MI.func{2} MI.in_guard{2} r{2}.
inline MI_SMCRealKEIdealSimp_AfterAdv.after_adv.
sim; auto => |>.
transitivity{2}
  {r <- MI_SMCIdeal_SMCSim_AfterAdv.after_adv(r);}
  (={r, MI.func, MI.adv, MI.in_guard, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   smc_sec2_rel3
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t' q' ==>
   ={r, glob Adv} /\
   smc_sec2_rel
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|})
   (={r} /\ not_done{2} /\ not_done0{2} /\
    ={MI.func, MI.adv, MI.in_guard, glob Adv,
      SMCIdeal.self, SMCIdeal.adv, SMCIdeal.st,
      SMCSim.self, SMCSim.adv, SMCSim.st} ==>
    ={r, MI.func, MI.adv, MI.in_guard, glob Adv,
      SMCIdeal.self, SMCIdeal.adv, SMCIdeal.st,
      SMCSim.self, SMCSim.adv, SMCSim.st}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{2} SMCIdeal.st{2}
       [] MI.adv{2} SMCSim.st{2} MI.adv{2} MI.func{2}
       MI.in_guard{2} r{2}.
call (MI_KEHybrid_KEIdeal_KESim_after_adv_3 pt1' pt2' t' q').
auto.
inline MI_SMCIdeal_SMCSim_AfterAdv.after_adv.
sp 3 0.
seq 5 5 :
  (r0{1} = r{2} /\
   not_done1{1} = not_done{2} /\
   ={MI.func, MI.adv, MI.in_guard,
   SMCIdeal.self, SMCIdeal.adv, SMCIdeal.st,
   SMCSim.self, SMCSim.adv, SMCSim.st, glob Adv}).
sim; progress; by rewrite H.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
rcondf{2} 4; first auto.
rcondf{2} 4; first auto.
rcondt{2} 4; first auto.
rcondf{2} 5; first auto.
sp.
if{1}.
inline SMCRealKEIdealSimp.parties.
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondt{1} 3; first auto; smt(is_smc_real_ke_ideal_simp_state_wait_adv2).
rcondf{1} 4; first auto; smt().
rcondt{1} 6; first auto.
rcondf{1} 7; first auto; smt().
auto; progress.
by rewrite (SMCSec2Rel2 _ pt1' pt2' t' q').
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto; progress.
by rewrite (SMCSec2Rel2 _ pt1' pt2' t' q').
seq 10 0 :
  (r{1} = None /\
   not_done{2} = true /\ not_done0{2} = true /\
   m{2} = oget r{2} /\ (mod{2}, pt1{2}, pt2{2}, u{2}) = m{2} /\
   (addr1{2}, n1{2}) = pt1{2} /\
   ={MI.func, MI.adv, MI.in_guard, glob Adv} /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   smc_sec2_rel2
   {|smc_sec2_rel_st_func = MI.func{1}; smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t' q' /\
   mod{2} = Adv /\ m{2}.`2.`1 <= addr1{2} /\
   MI.func{2} ++ [2] <> m{2}.`2.`1).
sp.
if{1}.
inline{1} (1) SMCRealKEIdealSimp.parties.
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondt{1} 3; first auto; smt(is_smc_real_ke_ideal_simp_state_wait_adv2).
sp 3 0.
if{1}.
rcondf{1} 2; first auto; smt(KeyEx.dest_good_ke_sim_rsp).
rcondt{1} 4; first auto.
rcondf{1} 5; first auto.
auto; smt(le_refl).
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
auto; smt(le_refl).
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto => |> &1 &2 <- [#] -> -> -> _ _ _ _.
rewrite negb_or not_dir /=.
smt(le_refl).
sp 0 3.
if{2}.
rcondf{2} 2; first auto.
move =>
  |> &hr r_R pt2_r oget_dec_smc_sim_state_wait_adv2 <-
  [] /= _ [#] _ _ _ _ _ ->>.
elim oget_dec_smc_sim_state_wait_adv2 => _ _ ->.
smt(KeyEx.dest_good_ke_sim_rsp).
rcondf{2} 2; first auto.
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
auto; progress; rewrite (SMCSec2Rel2 _ pt1' pt2' t' q') /#.
rcondf{2} 1; first auto.
rcondt{2} 1; first auto.        
rcondf{2} 2; first auto.
auto; progress; rewrite (SMCSec2Rel2 _ pt1' pt2' t' q') /#.
qed.

local lemma MI_KEHybrid_KEIdeal_KESim_after_adv_1
            (pt1' pt2' : port, t' : text) :
  equiv
  [MI_SMCRealKEIdealSimp_AfterAdv.after_adv ~
   MI_SMCIdeal_SMCSim_AfterAdv.after_adv :
   ={r, MI.func, MI.adv, MI.in_guard, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   smc_sec2_rel1
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t' ==>
   ={res, glob Adv} /\
   smc_sec2_rel
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}].
proof.
proc.
sp 4 5.
if; first smt().
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondt{2} 3; first auto.
rcondf{2} 4; first auto.
auto; progress; by apply (SMCSec2Rel1 _ pt1' pt2' t').
rcondt{2} 1; first auto; smt(is_smc_sim_state_wait_adv1).
case (! MI.func{1} <= addr1{1}).
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
rcondf{2} 3; first auto.
move => |> &hr <- [#] -> -> _ _ _ _ [] /= _ [#] _ _ _ _ _ -> //.
rcondf{2} 3; first auto.
sp 0 2.
if{2}.
rcondf{2} 2; first auto.
auto; progress; by apply (SMCSec2Rel1 _ pt1' pt2' t').
rcondf{2} 4; first auto; smt().
rcondt{2} 4; first auto; smt().
rcondf{2} 5; first auto.
auto; progress; by apply (SMCSec2Rel1 _ pt1' pt2' t').
rcondf{1} 1; first auto.
rcondt{1} 1; first auto.
rcondt{1} 3; first auto; smt().
inline{1} (1) SMCRealKEIdealSimp.invoke.
rcondt{2} 3; first auto.
move => |> &hr <- [#] -> -> _ _ _ _ [] /= _ [#] _ _ _ _ _ -> //.
case (MI.func{2} ++ [2] = m{2}.`2.`1).
case (KeyEx.is_ke_sim_rsp m{2}).
rcondt{2} 4; first auto.
rcondt{2} 5; first auto.
move =>
  |> &hr <- [#] -> -> _ _ _ _ [] /= _ [#] _ _ _ _ _ ->.
rewrite negb_or not_dir.
move => [#] _ -> _.
smt(KeyEx.dest_good_ke_sim_rsp).
rcondt{1} 7; first auto.
move => |> &hr <- /= [#] -> -> <- <- <- _ _.
rewrite negb_or not_dir.
move => [#] _ -> _ -> _ /=.
right; apply le_refl.
inline{1} (1) SMCRealKEIdealSimp.parties.
rcondf{1} 9; first auto; smt().
rcondt{1} 9; first auto; smt(is_smc_real_ke_ideal_simp_state_wait_adv1).
rcondt{1} 10; first auto.
rcondt{1} 11; first auto; smt(KeyEx.dest_good_ke_sim_rsp).
sp.
seq 1 1 :
  (q{2} = pad_iso_l t' q{1} /\
   not_done{1} /\ not_done{2} /\
   pt11{1} = pt1' /\ pt21{1} = pt2' /\ t{1} = t' /\
   pt1{2} = pt1' /\ pt2{2} = pt2' /\
   ={MI.func, MI.adv, MI.in_guard} /\
   addr{2} = MI.func{1} /\
   exper_pre MI.func{1} MI.adv{1} /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\
   SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\
   SMCSim.adv{2} = [] /\ ={glob Adv} /\
   smc_sec2_rel1
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t').
rnd (pad_iso_l t') (pad_iso_r t').
auto =>
  |> &1 &2 addr1_R pt2_R oget_dec_smc_sim_state_wait_adv1 _
  oget_dec_smc_real_ke_ideal_simp_wait_adv1 _ _ _ _
  [] /= _ [#] _ _ _ ->> _ ->>.
elim oget_dec_smc_sim_state_wait_adv1 => -> [#] -> ->.
elim oget_dec_smc_real_ke_ideal_simp_wait_adv1 => -> [#] -> ->.
progress.
by rewrite pad_iso_rl.
apply dexp_uni => //; rewrite dexp_fu.
rewrite dexp_fu.
by rewrite pad_iso_lr.
rcondf{1} 5; first auto.
rcondf{1} 8; first auto.
move => |> &hr.
rewrite /KeyEx.ke_sim_req2 /=; smt(inc_nle_r).
rcondf{1} 8; first auto.
rcondf{1} 8; first auto.
move => |> &hr.
rewrite /KeyEx.ke_sim_req2 /=; smt(KeyEx.ke_pi_uniq).
rcondt{1} 8; first auto.
rcondf{1} 10; first auto.
move => |> &hr.
rewrite /KeyEx.ke_sim_req2 /=; smt(inc_nle_r).
rcondt{2} 4; first auto.
rcondf{2} 5; first auto.
move => |> &hr.
rewrite /KeyEx.ke_sim_req2 /=; smt(smc_pi_uniq).
seq 10 5 :
  (={r, glob Adv} /\
   not_done{1} /\ not_done{2} /\ not_done0{2} /\ 
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\
   SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\
   SMCSim.adv{2} = [] /\ ={glob Adv} /\
   smc_sec2_rel2
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t' q{1}).
call (_ : true).
auto => |> &1 &2 _ _ exp_pre [] /=.
smt().
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
auto; progress; by rewrite (SMCSec2Rel2 _ pt1' pt2' t' q{1}).
transitivity{1}
  {r <- MI_SMCRealKEIdealSimp_AfterAdv.after_adv(r);}
  (={r, MI.func, MI.adv, MI.in_guard,
     SMCRealKEIdealSimp.self, SMCRealKEIdealSimp.adv,
     SMCRealKEIdealSimp.st, glob Adv} /\
   not_done{1} ==>
   ={r, MI.func, MI.adv, MI.in_guard,
     SMCRealKEIdealSimp.self, SMCRealKEIdealSimp.adv,
     SMCRealKEIdealSimp.st, glob Adv})
  (={r} /\ r{1} <> None /\ not_done{2} /\ not_done0{2} /\
   ={MI.func, MI.adv, MI.in_guard, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   smc_sec2_rel2
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t' q{1} ==>
   ={r, glob Adv} /\
   smc_sec2_rel
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{2} SMCRealKEIdealSimp.st{1}
          MI.adv{2} MI.func{2} MI.in_guard{2} q{1} r{2}.
inline MI_SMCRealKEIdealSimp_AfterAdv.after_adv.
sim; auto => |>.
transitivity{2}
  {r <- MI_SMCIdeal_SMCSim_AfterAdv.after_adv(r);}
  (={r, MI.func, MI.adv, MI.in_guard, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   smc_sec2_rel2
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t' q{1} ==>
   ={r, glob Adv} /\
   smc_sec2_rel
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|})
   (={r} /\ not_done{2} /\ not_done0{2} /\
    ={MI.func, MI.adv, MI.in_guard, glob Adv,
      SMCIdeal.self, SMCIdeal.adv, SMCIdeal.st,
      SMCSim.self, SMCSim.adv, SMCSim.st} ==>
    ={r, MI.func, MI.adv, MI.in_guard, glob Adv,
      SMCIdeal.self, SMCIdeal.adv, SMCIdeal.st,
      SMCSim.self, SMCSim.adv, SMCSim.st}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{2} SMCIdeal.st{2}
          [] MI.adv{2} SMCSim.st{2} MI.adv{2} MI.func{2}
          MI.in_guard{2} r{2}.
exlim q{1} => q'.
call (MI_KEHybrid_KEIdeal_KESim_after_adv_2 pt1' pt2' t' q').
auto.
inline MI_SMCIdeal_SMCSim_AfterAdv.after_adv.
sp 3 0.
seq 5 5 :
  (r0{1} = r{2} /\
   not_done1{1} = not_done{2} /\
   ={MI.func, MI.adv, MI.in_guard,
   SMCIdeal.self, SMCIdeal.adv, SMCIdeal.st,
   SMCSim.self, SMCSim.adv, SMCSim.st, glob Adv}).
sim; progress; by rewrite H.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
rcondf{2} 4; first auto.
rcondf{2} 4; first auto.
rcondt{2} 4; first auto.
rcondf{2} 5; first auto.
sp.
if{1}.
inline SMCRealKEIdealSimp.parties.
rcondf{1} 3; first auto; smt().
rcondt{1} 3; first auto; smt(is_smc_real_ke_ideal_simp_state_wait_adv1).
rcondf{1} 4; first auto; smt().
rcondt{1} 6; first auto.
rcondf{1} 7; first auto; smt().
auto; progress.
by rewrite (SMCSec2Rel1 _ pt1' pt2' t') /smc_sec2_rel1.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto; progress.
by rewrite (SMCSec2Rel1 _ pt1' pt2' t') /smc_sec2_rel1.
seq 10 0 :
  (r{1} = None /\
   not_done{2} = true /\ not_done0{2} = true /\
   m{2} = oget r{2} /\ (mod{2}, pt1{2}, pt2{2}, u{2}) = m{2} /\
   (addr1{2}, n1{2}) = pt1{2} /\
   ={MI.func, MI.adv, MI.in_guard, glob Adv} /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   smc_sec2_rel1
   {|smc_sec2_rel_st_func = MI.func{1}; smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t' /\
   mod{2} = Adv /\ m{2}.`2.`1 <= addr1{2} /\
   MI.func{2} ++ [2] <> m{2}.`2.`1).
sp.
if{1}.
inline{1} (1) SMCRealKEIdealSimp.parties.
rcondf{1} 3; first auto; smt().
rcondt{1} 3; first auto; smt(is_smc_real_ke_ideal_simp_state_wait_adv1).
sp 3 0.
if{1}.
rcondf{1} 2; first auto; smt(KeyEx.dest_good_ke_sim_rsp).
rcondt{1} 4; first auto.
rcondf{1} 5; first auto.
auto; smt(le_refl).
rcondt{1} 3; first auto.
rcondf{1} 4; first auto.
auto; smt(le_refl).
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto => |> &1 &2 <- [#] -> -> -> _ _ _ _.
rewrite negb_or not_dir /=.
smt(le_refl).
sp.
if{2}.
sp.
elim* => addr1_R r_R not_done0_R pt1_R pt2_R.
rcondf{2} 1; first auto.
move =>
  |> &hr oget_dec_ke_sim_rsp oget_dec_smc_sim_state_wait_adv1
  oget_r_R [] /= _ [#] _ _ _ _ _ ->> _ ne is_rsp.
elim oget_dec_smc_sim_state_wait_adv1 => _ _ ->>.
move : oget_dec_ke_sim_rsp.
smt(KeyEx.dest_good_ke_sim_rsp).
rcondf{2} 1; first auto.
rcondt{2} 1; first auto.
rcondf{2} 2; first auto.
auto; progress; rewrite (SMCSec2Rel1 _ pt1' pt2' t') /#.
rcondf{2} 1; first auto.
rcondt{2} 1; first auto.        
rcondf{2} 2; first auto.
auto; progress; rewrite (SMCSec2Rel1 _ pt1' pt2' t') /#.
qed.

local lemma MI_SMCRealKEIdealSimp_SMCIdeal_SMCSim_invoke :
  equiv
  [MI(SMCRealKEIdealSimp, Adv).invoke ~ MI(SMCIdeal, SMCSim(Adv)).invoke :
   ={m, MI.func, MI.adv, MI.in_guard, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   ! (smc_sim_adv_pi \in MI.in_guard{1}) /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\
   SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\
   SMCSim.adv{2} = [] /\
   smc_sec2_rel
   {|smc_sec2_rel_st_func = MI.func{1}; smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|} ==>
   ={res, glob Adv} /\
   smc_sec2_rel
   {|smc_sec2_rel_st_func = MI.func{1}; smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}].
proof.
proc.
case
  (smc_sec2_rel0
   {|smc_sec2_rel_st_func = MI.func{1}; smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}).
sp 2 2.
if => //.
inline MI(SMCRealKEIdealSimp, Adv).loop MI(SMCIdeal, SMCSim(Adv)).loop.
rcondt{1} 4; first auto.
rcondt{2} 4; first auto.
sp 5 5.
if => //.
inline{1} (1) SMCRealKEIdealSimp.invoke.
inline{2} (1) SMCIdeal.invoke.
sp 4 4.
if; first smt().
inline SMCRealKEIdealSimp.parties SMCIdeal.parties.
rcondt{1} 3; first auto; smt().
rcondt{2} 3; first auto; smt().
sp 2 2.
if => //.
sp 1 1.
if; first smt().
rcondf{1} 5; first auto.
rcondf{1} 8; first auto; progress.
rewrite /KeyEx.ke_sim_req1 /#.
rcondf{1} 8; first auto.
rcondf{1} 8; first auto; progress.
rewrite /KeyEx.ke_sim_req1 /=; smt(smc_pi_uniq).
rcondt{1} 8; first auto.
rcondf{1} 10; first auto; progress.
rewrite /KeyEx.ke_sim_req1 /= /#.
rcondf{2} 5; first auto.
rcondf{2} 8; first auto; progress.
rewrite /smc_sim_req /= /#.
rcondf{2} 8; first auto.
rcondf{2} 8; first auto; progress.
rewrite /smc_sim_req /=; smt(smc_pi_uniq).
rcondt{2} 8; first auto.
rcondf{2} 10; first auto; progress.
rewrite /smc_sim_req /= /#.
inline{2} (1) SMCSim(Adv).invoke.
rcondt{2} 13; first auto.
inline{2} (1) SMCSim(Adv).loop.
rcondt{2} 16; first auto.
rcondt{2} 17; first auto.
rcondt{2} 19; first auto; smt().
rcondt{2} 19; first auto; smt().
rcondt{2} 23; first auto.
rcondf{2} 24; first auto; progress.
rewrite enc_dec_smc_sim_req oget_some /= /ke_sim_req1 /=;
  smt(smc_pi_uniq).
seq 10 24 :
  (r0{1} = r4{2} /\ not_done{1} /\ not_done{2} /\ not_done0{2} /\
   ={MI.func, MI.adv, MI.in_guard, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   ! (smc_sim_adv_pi \in MI.in_guard{1}) /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\ SMCIdeal.self{2} = MI.func{1} /\
   SMCIdeal.adv{2} = MI.adv{1} /\ SMCSim.self{2} = MI.adv{1} /\
   SMCSim.adv{2} = [] /\
   ! SMCRealKEIdealSimp.self{1} <= pt12{1}.`1 /\
   ! SMCRealKEIdealSimp.self{1} <= pt22{1}.`1 /\
   ! SMCRealKEIdealSimp.adv{1} <= pt12{1}.`1 /\
   ! SMCRealKEIdealSimp.adv{1} <= pt22{1}.`1 /\
   smc_sec2_rel1
   {|smc_sec2_rel_st_func = MI.func{1}; smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt12{2} pt22{2} t{2}).
call (_ : true).
auto => |> &1 &2 <- [#] _ -> -> -> _ _ [] /= _ [#] _ _;
  by rewrite /KeyEx.ke_sim_req1 /= enc_dec_smc_sim_req.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondt{2} 4; first auto.
rcondf{2} 5; first auto.
auto; progress; by apply (SMCSec2Rel1 _ pt12{2} pt22{2} t{2}).
transitivity{1}
  {r <- MI_SMCRealKEIdealSimp_AfterAdv.after_adv(r0);}
  (={r0, MI.func, MI.adv, MI.in_guard,
     SMCRealKEIdealSimp.self, SMCRealKEIdealSimp.adv,
     SMCRealKEIdealSimp.st, glob Adv} /\
   not_done{1} ==>
   ={r, MI.func, MI.adv, MI.in_guard,
     SMCRealKEIdealSimp.self, SMCRealKEIdealSimp.adv,
     SMCRealKEIdealSimp.st, glob Adv})
  (r0{1} = r4{2} /\ r0{1} <> None /\ not_done{2} /\ not_done0{2} /\
   ={MI.func, MI.adv, MI.in_guard, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   ! (smc_sim_adv_pi \in MI.in_guard{1}) /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   smc_sec2_rel1
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt12{2} pt22{2} t{2} ==>
   ={r, glob Adv} /\
   smc_sec2_rel
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{2} SMCRealKEIdealSimp.st{1}
          MI.adv{2} MI.func{2} MI.in_guard{2} r4{2}.
inline MI_SMCRealKEIdealSimp_AfterAdv.after_adv.
sim; auto => |>.
transitivity{2}
  {r <- MI_SMCIdeal_SMCSim_AfterAdv.after_adv(r0);}
  (={r0, MI.func, MI.adv, MI.in_guard, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   ! (smc_sim_adv_pi \in MI.in_guard{1}) /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   smc_sec2_rel1
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt12{2} pt22{2} t{2} ==>
   ={r, glob Adv} /\
   smc_sec2_rel
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|})
   (r0{1} = r4{2} /\ not_done{2} /\ not_done0{2} /\
    ={MI.func, MI.adv, MI.in_guard, glob Adv,
      SMCIdeal.self, SMCIdeal.adv, SMCIdeal.st,
      SMCSim.self, SMCSim.adv, SMCSim.st} ==>
    ={r, MI.func, MI.adv, MI.in_guard, glob Adv,
      SMCIdeal.self, SMCIdeal.adv, SMCIdeal.st,
      SMCSim.self, SMCSim.adv, SMCSim.st}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{2} SMCIdeal.st{2}
          [] MI.adv{2} SMCSim.st{2} MI.adv{2} MI.func{2}
          MI.in_guard{2} pt12{2} pt22{2} r4{2} t{2}.
exlim pt12{2}, pt22{2}, t{2} => pt1' pt2' t'.
call (MI_KEHybrid_KEIdeal_KESim_after_adv_1 pt1' pt2' t').
auto.
inline MI_SMCIdeal_SMCSim_AfterAdv.after_adv.
sp 3 0.
seq 5 5 :
  (r5{1} = r4{2} /\
   not_done1{1} = not_done{2} /\
   ={MI.func, MI.adv, MI.in_guard,
   SMCIdeal.self, SMCIdeal.adv, SMCIdeal.st,
   SMCSim.self, SMCSim.adv, SMCSim.st, glob Adv}).
sim; progress; by rewrite H.
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
inline{2} (1) SMCSim(Adv).invoke.
rcondt{2} 4; first auto; smt().
inline{2} (1) SMCSim(Adv).loop.
rcondt{2} 7; first auto.
rcondf{2} 8; first auto; smt(smc_pi_uniq).
sp.
seq 1 1 :
  (r0{1} = r2{2} /\ not_done{1} /\ not_done{2} /\ not_done0{2} /\
   ={MI.func, MI.adv, MI.in_guard, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   ! (smc_sim_adv_pi \in MI.in_guard{1}) /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\ SMCIdeal.self{2} = MI.func{1} /\
   SMCIdeal.adv{2} = MI.adv{1} /\ SMCSim.self{2} = MI.adv{1} /\
   SMCSim.adv{2} = [] /\
   smc_sec2_rel0
   {|smc_sec2_rel_st_func = MI.func{1}; smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}).
call (_ : true).
auto.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondt{2} 4; first auto.
rcondf{2} 5; first auto.
auto; progress; by apply SMCSec2Rel0.
sp 3 3.
if; first smt().
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondt{2} 5; first auto.
rcondf{2} 6; first auto.
auto; progress; by apply SMCSec2Rel0.
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 2; first auto.
rcondf{2} 4; first auto.
rcondf{2} 7; first auto; smt().
sp 0 6.
if; first smt().
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto; progress; by apply SMCSec2Rel0.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
rcondt{1} 3; first auto; smt().
rcondt{2} 3; first auto; smt().
inline{1} (1) SMCRealKEIdealSimp.invoke.
inline{2} (1) SMCIdeal.invoke.
sp 6 6.
seq 5 0 :
  (m3{2}.`1 = mod3{2} /\ m3{2}.`2.`1 = addr12{2} /\
   r{1} = None /\ r3{2} = None /\
   mod3{2} = Adv /\ SMCIdeal.self{2} <= addr12{2} /\
   ={MI.func, MI.adv, MI.in_guard, glob Adv} /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\
   SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\
   SMCSim.adv{2} = [] /\
   smc_sec2_rel0
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}).
if{1}.
inline{1} (1) SMCRealKEIdealSimp.parties.
rcondt{1} 3; first auto; smt().
rcondf{1} 3; first auto.
progress.
rewrite /is_smc_req /dec_smc_req /=.
smt(not_dir).
rcondt{1} 5; first auto.
rcondf{1} 6; first auto.
auto; smt().
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto => |> &1 &2 _ <- [#] <- <- <- <- <- [#] -> -> -> _ _ _ _ _ _ _ _ _.
rewrite negb_or not_dir => />.
if{2}.
inline{2} (1) SMCIdeal.parties.
rcondt{2} 3; first auto; smt().
rcondf{2} 3; first auto; progress.
rewrite /is_smc_req /dec_smc_req; smt().
rcondt{2} 5; first auto.
rcondf{2} 6; first auto.
auto; progress; by apply SMCSec2Rel0.
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
auto; progress; by apply SMCSec2Rel0.
auto; progress; by apply SMCSec2Rel0.
case
  (exists pt1' pt2' t',
   smc_sec2_rel1
   {|smc_sec2_rel_st_func = MI.func{1}; smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t').
elim* => pt1' pt2' t'.
sp 2 2.
if => //.
inline MI(SMCRealKEIdealSimp, Adv).loop MI(SMCIdeal, SMCSim(Adv)).loop.
rcondt{1} 4; first auto.
rcondt{2} 4; first auto.
sp 5 5.
if => //.
inline{1} (1) SMCRealKEIdealSimp.invoke.
inline{2} (1) SMCIdeal.invoke.
sp 4 4.
if; first smt().
inline{1} (1) SMCRealKEIdealSimp.parties.
inline{2} (1) SMCIdeal.parties.
rcondf{1} 3; first auto; smt().
rcondt{1} 3; first auto; smt(is_smc_real_ke_ideal_simp_state_wait_adv1).
rcondf{2} 3; first auto; smt().
rcondt{2} 3; first auto; smt(is_smc_ideal_state_wait_sim).
rcondf{1} 4; first auto; progress.
rewrite /is_ke_sim_rsp /dec_ke_sim_rsp /= /#.
rcondf{2} 4; first auto; progress.
rewrite /is_smc_sim_rsp /dec_smc_sim_rsp /= /#.
rcondt{1} 6; first auto.
rcondf{1} 7; first auto.
rcondt{2} 6; first auto.
rcondf{2} 7; first auto.
auto.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
inline{2} (1) SMCSim(Adv).invoke.
rcondt{2} 4; first auto; smt().
inline{2} (1) SMCSim(Adv).loop.
rcondt{2} 7; first auto.
rcondf{2} 8; first auto; progress; smt(smc_pi_uniq).
sp.
seq 1 1 :
  (r0{1} = r2{2} /\ not_done{1} /\ not_done{2} /\ not_done0{2} /\
   ={MI.func, MI.adv, MI.in_guard, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   ! (smc_sim_adv_pi \in MI.in_guard{1}) /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   smc_sec2_rel1
   {|smc_sec2_rel_st_func = MI.func{1}; smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t').
call (_ : true).
auto.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondt{2} 4; first auto.
rcondf{2} 5; first auto.
auto; progress; by apply (SMCSec2Rel1 _ pt1' pt2' t').
transitivity{1}
  {r <- MI_SMCRealKEIdealSimp_AfterAdv.after_adv(r0);}
  (={r0, MI.func, MI.adv, MI.in_guard,
     SMCRealKEIdealSimp.self, SMCRealKEIdealSimp.adv,
     SMCRealKEIdealSimp.st, glob Adv} /\
   not_done{1} ==>
   ={r, MI.func, MI.adv, MI.in_guard,
     SMCRealKEIdealSimp.self, SMCRealKEIdealSimp.adv,
     SMCRealKEIdealSimp.st, glob Adv})
  (r0{1} = r2{2} /\ r0{1} <> None /\ not_done{2} /\ not_done0{2} /\
   ={MI.func, MI.adv, MI.in_guard, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   ! (smc_sim_adv_pi \in MI.in_guard{1}) /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   smc_sec2_rel1
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t' ==>
   ={r, glob Adv} /\
   smc_sec2_rel
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{2} SMCRealKEIdealSimp.st{1}
          MI.adv{2} MI.func{2} MI.in_guard{2} r2{2}.
inline MI_SMCRealKEIdealSimp_AfterAdv.after_adv.
sim; auto => |>.
transitivity{2}
  {r <- MI_SMCIdeal_SMCSim_AfterAdv.after_adv(r0);}
  (={r0, MI.func, MI.adv, MI.in_guard, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   ! (smc_sim_adv_pi \in MI.in_guard{1}) /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   smc_sec2_rel1
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t' ==>
   ={r, glob Adv} /\
   smc_sec2_rel
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|})
   (r0{1} = r2{2} /\ not_done{2} /\ not_done0{2} /\
    ={MI.func, MI.adv, MI.in_guard, glob Adv,
      SMCIdeal.self, SMCIdeal.adv, SMCIdeal.st,
      SMCSim.self, SMCSim.adv, SMCSim.st} ==>
    ={r, MI.func, MI.adv, MI.in_guard, glob Adv,
      SMCIdeal.self, SMCIdeal.adv, SMCIdeal.st,
      SMCSim.self, SMCSim.adv, SMCSim.st}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{2} SMCIdeal.st{2}
          [] MI.adv{2} SMCSim.st{2} MI.adv{2} MI.func{2}
          MI.in_guard{2} r2{2}.
call (MI_KEHybrid_KEIdeal_KESim_after_adv_1 pt1' pt2' t').
auto.
inline MI_SMCIdeal_SMCSim_AfterAdv.after_adv.
sp 3 0.
seq 5 5 :
  (r3{1} = r2{2} /\
   not_done1{1} = not_done{2} /\
   ={MI.func, MI.adv, MI.in_guard,
   SMCIdeal.self, SMCIdeal.adv, SMCIdeal.st,
   SMCSim.self, SMCSim.adv, SMCSim.st, glob Adv}).
sim.
progress; by rewrite H.
sp 0 2.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
auto.
case
  (exists pt1' pt2' t' q',
   smc_sec2_rel2
   {|smc_sec2_rel_st_func = MI.func{1}; smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t' q').
elim* => pt1' pt2' t' q'.
sp 2 2.
if => //.
inline MI(SMCRealKEIdealSimp, Adv).loop MI(SMCIdeal, SMCSim(Adv)).loop.
rcondt{1} 4; first auto.
rcondt{2} 4; first auto.
sp 5 5.
if => //.
inline{1} (1) SMCRealKEIdealSimp.invoke.
inline{2} (1) SMCIdeal.invoke.
sp 4 4.
if; first smt().
inline{1} (1) SMCRealKEIdealSimp.parties.
inline{2} (1) SMCIdeal.parties.
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondt{1} 3; first auto; smt(is_smc_real_ke_ideal_simp_state_wait_adv2).
rcondf{2} 3; first auto; smt().
rcondt{2} 3; first auto; smt(is_smc_ideal_state_wait_sim).
rcondf{1} 4; first auto; progress.
rewrite /is_ke_sim_rsp /dec_ke_sim_rsp /= /#.
rcondf{2} 4; first auto; progress.
rewrite /is_smc_sim_rsp /dec_smc_sim_rsp /= /#.
rcondt{1} 6; first auto.
rcondf{1} 7; first auto.
rcondt{2} 6; first auto.
rcondf{2} 7; first auto.
auto.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
inline{2} (1) SMCSim(Adv).invoke.
rcondt{2} 4; first auto; smt().
inline{2} (1) SMCSim(Adv).loop.
rcondt{2} 7; first auto.
rcondf{2} 8; first auto; progress.
elim H4 => // [#] _ []; smt(smc_pi_uniq).
sp.
seq 1 1 :
  (r0{1} = r2{2} /\ not_done{1} /\ not_done{2} /\ not_done0{2} /\
   ={MI.func, MI.adv, MI.in_guard, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   ! (smc_sim_adv_pi \in MI.in_guard{1}) /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   smc_sec2_rel2
   {|smc_sec2_rel_st_func = MI.func{1}; smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t' q').
call (_ : true).
auto.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondt{2} 4; first auto.
rcondf{2} 5; first auto.
auto; progress; by apply (SMCSec2Rel2 _ pt1' pt2' t' q').
transitivity{1}
  {r <- MI_SMCRealKEIdealSimp_AfterAdv.after_adv(r0);}
  (={r0, MI.func, MI.adv, MI.in_guard,
     SMCRealKEIdealSimp.self, SMCRealKEIdealSimp.adv,
     SMCRealKEIdealSimp.st, glob Adv} /\
   not_done{1} ==>
   ={r, MI.func, MI.adv, MI.in_guard,
     SMCRealKEIdealSimp.self, SMCRealKEIdealSimp.adv,
     SMCRealKEIdealSimp.st, glob Adv})
  (r0{1} = r2{2} /\ r0{1} <> None /\ not_done{2} /\ not_done0{2} /\
   ={MI.func, MI.adv, MI.in_guard, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   ! (smc_sim_adv_pi \in MI.in_guard{1}) /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   smc_sec2_rel2
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t' q' ==>
   ={r, glob Adv} /\
   smc_sec2_rel
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{2} SMCRealKEIdealSimp.st{1}
          MI.adv{2} MI.func{2} MI.in_guard{2} r2{2}.
inline MI_SMCRealKEIdealSimp_AfterAdv.after_adv.
sim; auto => |>.
transitivity{2}
  {r <- MI_SMCIdeal_SMCSim_AfterAdv.after_adv(r0);}
  (={r0, MI.func, MI.adv, MI.in_guard, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   ! (smc_sim_adv_pi \in MI.in_guard{1}) /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   smc_sec2_rel2
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t' q' ==>
   ={r, glob Adv} /\
   smc_sec2_rel
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|})
   (r0{1} = r2{2} /\ not_done{2} /\ not_done0{2} /\
    ={MI.func, MI.adv, MI.in_guard, glob Adv,
      SMCIdeal.self, SMCIdeal.adv, SMCIdeal.st,
      SMCSim.self, SMCSim.adv, SMCSim.st} ==>
    ={r, MI.func, MI.adv, MI.in_guard, glob Adv,
      SMCIdeal.self, SMCIdeal.adv, SMCIdeal.st,
      SMCSim.self, SMCSim.adv, SMCSim.st}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{2} SMCIdeal.st{2}
          [] MI.adv{2} SMCSim.st{2} MI.adv{2} MI.func{2}
          MI.in_guard{2} r2{2}.
call (MI_KEHybrid_KEIdeal_KESim_after_adv_2 pt1' pt2' t' q').
auto.
inline MI_SMCIdeal_SMCSim_AfterAdv.after_adv.
sp 3 0.
seq 5 5 :
  (r3{1} = r2{2} /\
   not_done1{1} = not_done{2} /\
   ={MI.func, MI.adv, MI.in_guard,
   SMCIdeal.self, SMCIdeal.adv, SMCIdeal.st,
   SMCSim.self, SMCSim.adv, SMCSim.st, glob Adv}).
sim.
progress; by rewrite H.
sp 0 2.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
auto.
case
  (exists pt1' pt2' t' q',
   smc_sec2_rel3
   {|smc_sec2_rel_st_func = MI.func{1}; smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t' q').
elim* => pt1' pt2' t' q'.
sp 2 2.
if => //.
inline MI(SMCRealKEIdealSimp, Adv).loop MI(SMCIdeal, SMCSim(Adv)).loop.
rcondt{1} 4; first auto.
rcondt{2} 4; first auto.
sp 5 5.
if => //.
inline{1} (1) SMCRealKEIdealSimp.invoke.
inline{2} (1) SMCIdeal.invoke.
sp 4 4.
if; first smt().
inline{1} (1) SMCRealKEIdealSimp.parties.
inline{2} (1) SMCIdeal.parties.
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondt{1} 3; first auto; smt(is_smc_real_ke_ideal_simp_state_wait_adv3).
rcondf{2} 3; first auto; smt().
rcondt{2} 3; first auto; smt(is_smc_ideal_state_wait_sim).
rcondf{1} 4; first auto; progress.
rewrite /is_fw_ok /dec_fw_ok /= /#.
rcondf{2} 4; first auto; progress.
rewrite /is_smc_sim_rsp /dec_smc_sim_rsp /= /#.
rcondt{1} 6; first auto.
rcondf{1} 7; first auto.
rcondt{2} 6; first auto.
rcondf{2} 7; first auto.
auto.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
inline{2} (1) SMCSim(Adv).invoke.
rcondt{2} 4; first auto; smt().
inline{2} (1) SMCSim(Adv).loop.
rcondt{2} 7; first auto.
rcondf{2} 8; first auto; progress.
elim H5 => // [#] _ []; smt(smc_pi_uniq).
sp.
seq 1 1 :
  (r0{1} = r2{2} /\ not_done{1} /\ not_done{2} /\ not_done0{2} /\
   ={MI.func, MI.adv, MI.in_guard, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   ! (smc_sim_adv_pi \in MI.in_guard{1}) /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   smc_sec2_rel3
   {|smc_sec2_rel_st_func = MI.func{1}; smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t' q').
call (_ : true).
auto.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondt{2} 4; first auto.
rcondf{2} 5; first auto.
auto; progress; by apply (SMCSec2Rel3 _ pt1' pt2' t' q').
transitivity{1}
  {r <- MI_SMCRealKEIdealSimp_AfterAdv.after_adv(r0);}
  (={r0, MI.func, MI.adv, MI.in_guard,
     SMCRealKEIdealSimp.self, SMCRealKEIdealSimp.adv,
     SMCRealKEIdealSimp.st, glob Adv} /\
   not_done{1} ==>
   ={r, MI.func, MI.adv, MI.in_guard,
     SMCRealKEIdealSimp.self, SMCRealKEIdealSimp.adv,
     SMCRealKEIdealSimp.st, glob Adv})
  (r0{1} = r2{2} /\ r0{1} <> None /\ not_done{2} /\ not_done0{2} /\
   ={MI.func, MI.adv, MI.in_guard, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   ! (smc_sim_adv_pi \in MI.in_guard{1}) /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   smc_sec2_rel3
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t' q' ==>
   ={r, glob Adv} /\
   smc_sec2_rel
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{2} SMCRealKEIdealSimp.st{1}
          MI.adv{2} MI.func{2} MI.in_guard{2} r2{2}.
inline MI_SMCRealKEIdealSimp_AfterAdv.after_adv.
sim; auto => |>.
transitivity{2}
  {r <- MI_SMCIdeal_SMCSim_AfterAdv.after_adv(r0);}
  (={r0, MI.func, MI.adv, MI.in_guard, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   ! (smc_sim_adv_pi \in MI.in_guard{1}) /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   smc_sec2_rel3
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t' q' ==>
   ={r, glob Adv} /\
   smc_sec2_rel
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|})
   (r0{1} = r2{2} /\ not_done{2} /\ not_done0{2} /\
    ={MI.func, MI.adv, MI.in_guard, glob Adv,
      SMCIdeal.self, SMCIdeal.adv, SMCIdeal.st,
      SMCSim.self, SMCSim.adv, SMCSim.st} ==>
    ={r, MI.func, MI.adv, MI.in_guard, glob Adv,
      SMCIdeal.self, SMCIdeal.adv, SMCIdeal.st,
      SMCSim.self, SMCSim.adv, SMCSim.st}) => //.
progress.
by exists (glob Adv){2} MI.adv{2} MI.func{2} SMCIdeal.st{2}
          [] MI.adv{2} SMCSim.st{2} MI.adv{2} MI.func{2}
          MI.in_guard{2} r2{2}.
call (MI_KEHybrid_KEIdeal_KESim_after_adv_3 pt1' pt2' t' q').
auto.
inline MI_SMCIdeal_SMCSim_AfterAdv.after_adv.
sp 3 0.
seq 5 5 :
  (r3{1} = r2{2} /\
   not_done1{1} = not_done{2} /\
   ={MI.func, MI.adv, MI.in_guard,
   SMCIdeal.self, SMCIdeal.adv, SMCIdeal.st,
   SMCSim.self, SMCSim.adv, SMCSim.st, glob Adv}).
sim.
progress; by rewrite H.
sp 0 2.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto.
sim.
auto.
case
  (exists pt1' pt2' t' q',
   smc_sec2_rel4
   {|smc_sec2_rel_st_func = MI.func{1}; smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t' q').
elim* => pt1' pt2' t' q'.
sp 2 2.
if => //.
inline MI(SMCRealKEIdealSimp, Adv).loop MI(SMCIdeal, SMCSim(Adv)).loop.
rcondt{1} 4; first auto.
rcondt{2} 4; first auto.
sp 5 5.
if => //.
inline{1} (1) SMCRealKEIdealSimp.invoke.
inline{2} (1) SMCIdeal.invoke.
sp 4 4.
if; first smt().
inline{1} (1) SMCRealKEIdealSimp.parties.
inline{2} (1) SMCIdeal.parties.
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondf{2} 3; first auto; smt().
rcondf{2} 3; first auto; smt().
rcondt{1} 5; first auto.
rcondt{2} 5; first auto.
rcondf{1} 6; first auto.
rcondf{2} 6; first auto.
auto.
rcondt{1} 2; first auto.
rcondt{2} 2; first auto.
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
auto.
inline{2} (1) SMCSim(Adv).invoke.
rcondt{2} 4; first auto; smt().
inline{2} (1) SMCSim(Adv).loop.
rcondt{2} 7; first auto.
rcondf{2} 8; first auto; progress.
elim H6 => // [#] _ []; smt(smc_pi_uniq).
sp.
seq 1 1 :
  (r0{1} = r2{2} /\ not_done{1} /\ not_done{2} /\ not_done0{2} /\
   ={MI.func, MI.adv, MI.in_guard, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   ! (smc_sim_adv_pi \in MI.in_guard{1}) /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   smc_sec2_rel4
   {|smc_sec2_rel_st_func = MI.func{1}; smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t' q').
call (_ : true).
auto.
if => //.
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
rcondt{2} 4; first auto.
rcondf{2} 5; first auto.
auto; progress; by apply (SMCSec2Rel4 _ pt1' pt2' t' q').
sp 3 3.
if; first smt().
rcondf{1} 3; first auto.
rcondf{2} 3; first auto.
rcondt{2} 5; first auto.
rcondf{2} 6; first auto.
auto; progress; by apply (SMCSec2Rel4 _ pt1' pt2' t' q').
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 1; first auto; smt().
rcondf{2} 2; first auto.
rcondf{2} 4; first auto.
rcondf{2} 7; first auto; smt().
sp 0 6.
if; first smt().
rcondf{1} 2; first auto.
rcondf{2} 2; first auto.
auto; progress; by apply (SMCSec2Rel4 _ pt1' pt2' t' q').
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
rcondt{1} 3; first auto; smt().
rcondt{2} 3; first auto; smt().
sp 2 2.
inline{1} (1) SMCRealKEIdealSimp.invoke.
inline{2} (1) SMCIdeal.invoke.
sp 4 4.
seq 5 0 :
  (r{1} = None /\ not_done{2} /\ r3{2} = None /\
   mod3{2} = m3{2}.`1 /\ addr12{2} = m3{2}.`2.`1 /\
   n12{2} = m3{2}.`2.`2 /\
   ={MI.func, MI.adv, MI.in_guard, glob Adv} /\
   exper_pre MI.func{1} MI.adv{1} /\
   ! (smc_sim_adv_pi \in MI.in_guard{1}) /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\
   SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\
   SMCSim.adv{2} = [] /\
   smc_sec2_rel4
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2};|}
   pt1' pt2' t' q').
if{1}.
inline{1} (1) SMCRealKEIdealSimp.parties.
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt().
rcondt{1} 5; first auto.
rcondf{1} 6; first auto.
auto.
rcondt{1} 2; first auto.
rcondf{1} 3; first auto.
auto.
if{2}.
inline{2} (1) SMCIdeal.parties.
rcondf{2} 3; first auto; smt().
rcondf{2} 3; first auto; smt().
rcondt{2} 5; first auto.
rcondf{2} 6; first auto.
auto; progress; by apply (SMCSec2Rel4 _ pt1' pt2' t' q').
rcondt{2} 2; first auto.
rcondf{2} 3; first auto.
auto; progress; by apply (SMCSec2Rel4 _ pt1' pt2' t' q').
auto; progress; by apply (SMCSec2Rel4 _ pt1' pt2' t' q').
exfalso => &1 &2 [#] _ _ _ _ _ _ _ _ _ _ _ _ _ [] /#.
qed.

local lemma Exper_SMCRealKEIdealSimp_SMCIdeal_SMCSim
            (func' adv' : addr, in_guard' : int fset) &m :
  exper_pre func' adv' => ! (smc_sim_adv_pi \in in_guard') =>
  Pr[Exper(MI(SMCRealKEIdealSimp, Adv), Env).main
       (func', adv', in_guard') @ &m : res] =
  Pr[Exper(MI(SMCIdeal, SMCSim(Adv)), Env).main
       (func', adv', in_guard') @ &m : res].
proof.
move => pre not_in_guard'; byequiv => //; proc.
inline MI(SMCRealKEIdealSimp, Adv).init MI(SMCIdeal, SMCSim(Adv)).init
       SMCRealKEIdealSimp.init SMCIdeal.init SMCSim(Adv).init.
seq 12 17 :
  (={func, adv, in_guard, MI.func, MI.adv, MI.in_guard} /\
   func{1} = MI.func{1} /\ adv{1} = MI.adv{1} /\
   in_guard{1} = MI.in_guard{1} /\
   exper_pre MI.func{1} MI.adv{1} /\
   ! (smc_sim_adv_pi \in MI.in_guard{1}) /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   ={glob Adv, glob Env} /\
   SMCRealKEIdealSimp.st{1} = SMCRealKEIdealSimpStateWaitReq /\
   SMCIdeal.st{2} = SMCIdealStateWaitReq /\
   SMCSim.st{2} = SMCSimStateWaitReq).
swap{2} 16 1.
call (_ : true).
auto.
call
  (_ :
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} /\
   ! (smc_sim_adv_pi \in MI.in_guard{1}) /\
   SMCRealKEIdealSimp.self{1} = MI.func{1} /\
   SMCRealKEIdealSimp.adv{1} = MI.adv{1} /\
   SMCIdeal.self{2} = MI.func{1} /\ SMCIdeal.adv{2} = MI.adv{1} /\
   SMCSim.self{2} = MI.adv{1} /\ SMCSim.adv{2} = [] /\
   ={glob Adv} /\
   smc_sec2_rel
   {|smc_sec2_rel_st_func = MI.func{1};
     smc_sec2_rel_st_adv  = MI.adv{1};
     smc_sec2_rel_st_riss = SMCRealKEIdealSimp.st{1};
     smc_sec2_rel_st_is   = SMCIdeal.st{2};
     smc_sec2_rel_st_sims = SMCSim.st{2}|}).
conseq MI_SMCRealKEIdealSimp_SMCIdeal_SMCSim_invoke => //.
auto; progress; by rewrite SMCSec2Rel0.
qed.

lemma smc_sec2 (func adv : addr, in_guard' : int fset) &m :
  exper_pre func adv => ! (smc_sim_adv_pi \in in_guard') =>
  Pr[Exper(MI(SMCReal(KeyEx.KEIdeal), Adv), Env).main
       (func, adv, in_guard') @ &m : res] =
  Pr[Exper(MI(SMCIdeal, SMCSim(Adv)), Env).main
       (func, adv, in_guard') @ &m : res].
proof.
move => pre not_in_guard'.
by rewrite (Exper_SMCReal_KEIdeal_SMCRealKEIdealSimp func adv in_guard'
            &m Adv Env) 1:/#
           (Exper_SMCRealKEIdealSimp_SMCIdeal_SMCSim func adv in_guard' &m).
qed.

end section.

lemma smc_security2
      (Adv <: FUNC{MI, SMCReal, SMCIdeal, SMCSim, KeyEx.KEIdeal})
      (Env <: ENV{Adv, MI, SMCReal, SMCIdeal, SMCSim, KeyEx.KEIdeal})
      (func' adv' : addr, in_guard' : int fset) &m :
  exper_pre func' adv' => ! (smc_sim_adv_pi \in in_guard') =>
  Pr[Exper(MI(SMCReal(KeyEx.KEIdeal), Adv), Env).main
       (func', adv', in_guard') @ &m : res] =
  Pr[Exper(MI(SMCIdeal, SMCSim(Adv)), Env).main
       (func', adv', in_guard') @ &m : res].
proof.
move => pre not_in_guard'.
by apply (smc_sec2 Adv Env func' adv' in_guard' &m).
qed.

module SMCSimComp (Adv : FUNC) = SMCSim(KeyEx.KESim(Adv)).

lemma smc_security
      (Adv <: FUNC{MI, SMCReal, SMCIdeal, SMCSim, KeyEx.KEReal,
                   KeyEx.KEIdeal, KeyEx.KESim, KeyEx.DDH_Adv, CompEnv})
      (Env <: ENV{Adv, MI, SMCReal, SMCIdeal, SMCSim, KeyEx.KEReal,
                  KeyEx.KEIdeal, KeyEx.KESim, KeyEx.DDH_Adv, CompEnv})
      (func' adv' : addr, in_guard' : int fset) &m :
  exper_pre func' adv' =>
  ! (ke_sim_adv_pi \in in_guard') => ! (smc_sim_adv_pi \in in_guard') =>
  (* parameters for modules in upper bound: *)
  CompEnv.in_guard_low{m} = in_guard' =>
  KeyEx.DDH_Adv.func{m} = func' ++ [2] => KeyEx.DDH_Adv.adv{m} = adv' =>
  KeyEx.DDH_Adv.in_guard{m} = in_guard' `|` fset1 adv_fw_pi =>
  (* end of parameters for modules in upper bound *)
  `|Pr[Exper(MI(SMCReal(KeyEx.KEReal), Adv), Env).main
         (func', adv', in_guard') @ &m : res] -
    Pr[Exper(MI(SMCIdeal, SMCSimComp(Adv)), Env).main
         (func', adv', in_guard') @ &m : res]| <=
  `|Pr[DDH1(KeyEx.DDH_Adv(CompEnv(Env), Adv)).main() @ &m : res] -
    Pr[DDH2(KeyEx.DDH_Adv(CompEnv(Env), Adv)).main() @ &m : res]|.
proof.
move => pre not_in_guard'_ke not_in_guard'_smc ce_in_guard'_eq
        ddh_func'_eq ddh_adv'_eq ddh_in_guard'_eq.
by rewrite -(smc_security2 (KeyEx.KESim(Adv)) Env func' adv' in_guard' &m) //
           (smc_security1 Adv Env func' adv' in_guard' &m).
qed.
