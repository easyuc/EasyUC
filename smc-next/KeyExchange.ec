(* KeyExchange.ec *)

(* Diffie-Hellman Key Exchange *)

prover quorum=2 ["Alt-Ergo" "Z3"].

require import AllCore List FSet SmtMap Distr ListAux ListPO
               Encoding DiffieHellman UCCore.
require Forward RedundantHashing.

(* theory parameters *)

(* port indices of adversary that the two forwarding functionalities
   use *)

op adv_fw1_pi : int.
op adv_fw2_pi : int.

(* port index of key exchange simulator *)

op ke_sim_pi : int.

axiom ke_pi_uniq : uniq [ke_sim_pi; adv_fw1_pi; adv_fw2_pi; 0].

clone EPDP as EPDP_Univ_Key with  (* key *)
  type orig <- key, type enc <- univ.

clone EPDP as EPDP_Univ_PortKey with  (* port * key *)
  type orig <- port * key, type enc <- univ.

clone EPDP as EPDP_Univ_PortPortKey with  (* port * port * key *)
  type orig <- port * port * key, type enc <- univ.

(* end theory parameters *)

(* request sent to port index 1 of key exchange functionality: pt1
   wants to exchange a key with pt2 *)

type ke_req1 =
  {ke_req1_func : addr;   (* address of functionality *)
   ke_req1_pt1  : port;   (* port requesting key exchange *)
   (* data: *)
   ke_req1_pt2  : port}.  (* port to exchange key with *)

op ke_req1 (x : ke_req1) : msg =
     (Dir, (x.`ke_req1_func, 1), x.`ke_req1_pt1,
      EPDP_Univ_Port.enc x.`ke_req1_pt2).

op dec_ke_req1 (m : msg) : ke_req1 option =
     let (mod, pt1, pt2, v) = m
     in (mod = Adv \/ pt1.`2 <> 1 \/ ! EPDP_Univ_Port.valid v) ?
        None :
        let pt2' = oget (EPDP_Univ_Port.dec v)
        in Some {|ke_req1_func = pt1.`1; ke_req1_pt1 = pt2;
                  ke_req1_pt2 = pt2'|}.

lemma epdp_ke_req1 : epdp ke_req1 dec_ke_req1.
proof.
apply epdp_intro.
move => m.
rewrite /ke_req1 /dec_ke_req1 /= EPDP_Univ_Port.valid_enc
        /= EPDP_Univ_Port.enc_dec oget_some /#.
move => [mod pt1 pt2 u] v.
rewrite /ke_req1 /dec_ke_req1 /=.
case (mod = Adv \/ pt1.`2 <> 1 \/ ! (EPDP_Univ_Port.valid u)) => //.
rewrite !negb_or /= not_adv => [#] -> pt1_2 val_u.
have [] p : exists (p : port), EPDP_Univ_Port.dec u = Some p.
  exists (oget (EPDP_Univ_Port.dec u)); by rewrite -some_oget.
move => /EPDP_Univ_Port.dec_enc <-.
rewrite EPDP_Univ_Port.enc_dec oget_some /#.
qed.

lemma dest_valid_ke_req1 (m : msg) :
  dec2valid dec_ke_req1 m =>
  m.`2.`1 = (oget (dec_ke_req1 m)).`ke_req1_func /\ m.`2.`2 = 1.
proof.
move => val_m.
have [] x : exists (x : ke_req1), dec_ke_req1 m = Some x.
  exists (oget (dec_ke_req1 m)); by rewrite -some_oget.
case x => x1 x2 x3.
move => /(epdp_dec_enc _ _ _ _ epdp_ke_req1) <-.
by rewrite (epdp_enc_dec _ _ _ epdp_ke_req1).
qed.

lemma source_valid_ke_req1 (m : msg) :
  dec2valid dec_ke_req1 m =>
  m.`3 = (oget (dec_ke_req1 m)).`ke_req1_pt1.
proof.
move => val_m.
have [] x : exists (x : ke_req1), dec_ke_req1 m = Some x.
  exists (oget (dec_ke_req1 m)); by rewrite -some_oget.
case x => x1 x2 x3.
move => /(epdp_dec_enc _ _ _ _ epdp_ke_req1) <-.
by rewrite (epdp_enc_dec _ _ _ epdp_ke_req1).
qed.

(* response sent from port index 2 of key exchange functionality to
   pt2, completing first phase of key exchange initiated by pt1 *)

type ke_rsp1 =
  {ke_rsp1_func : addr;   (* address of functionality *)
   ke_rsp1_pt1  : port;   (* port requesting key exchange *)
   (* data: *)
   ke_rsp1_pt2  : port;   (* port to exchange key with *)
   ke_rsp1_key  : key}.   (* exchanged key *)

op ke_rsp1 (x : ke_rsp1) : msg =
     (Dir, x.`ke_rsp1_pt2, (x.`ke_rsp1_func, 2),
      EPDP_Univ_PortKey.enc (x.`ke_rsp1_pt1, x.`ke_rsp1_key)).

op dec_ke_rsp1 (m : msg) : ke_rsp1 option =
     let (mod, pt1, pt2, v) = m
     in (mod = Adv \/ pt2.`2 <> 2 \/ ! EPDP_Univ_PortKey.valid v) ?
        None :
        let (pt1', k) = oget (EPDP_Univ_PortKey.dec v)
        in Some {|ke_rsp1_func = pt2.`1; ke_rsp1_pt1 = pt1';
                  ke_rsp1_pt2 = pt1; ke_rsp1_key = k|}.

lemma epdp_ke_rsp1 : epdp ke_rsp1 dec_ke_rsp1.
proof.
apply epdp_intro.
move => m.
rewrite /ke_rsp1 /dec_ke_rsp1 /= EPDP_Univ_PortKey.valid_enc
        /= EPDP_Univ_PortKey.enc_dec oget_some /#.
move => [mod pt1 pt2 u] v.
rewrite /ke_rsp1 /dec_ke_rsp1 /=.
case (mod = Adv \/ pt2.`2 <> 2 \/ ! (EPDP_Univ_PortKey.valid u)) => //.
rewrite !negb_or /= not_adv => [#] -> pt2_2 val_u.
have [] p : exists (p : port * key), EPDP_Univ_PortKey.dec u = Some p.
  exists (oget (EPDP_Univ_PortKey.dec u)); by rewrite -some_oget.
move => /EPDP_Univ_PortKey.dec_enc <-.
rewrite EPDP_Univ_PortKey.enc_dec oget_some /#.
qed.

lemma dest_valid_ke_rsp1 (m : msg) :
  dec2valid dec_ke_rsp1 m =>
  m.`2 = (oget (dec_ke_rsp1 m)).`ke_rsp1_pt2.
proof.
move => val_m.
have [] x : exists (x : ke_rsp1), dec_ke_rsp1 m = Some x.
  exists (oget (dec_ke_rsp1 m)); by rewrite -some_oget.
case x => x1 x2 x3 x4.
move => /(epdp_dec_enc _ _ _ _ epdp_ke_rsp1) <-.
by rewrite (epdp_enc_dec _ _ _ epdp_ke_rsp1).
qed.

lemma source_valid_ke_rsp1 (m : msg) :
  dec2valid dec_ke_rsp1 m =>
  m.`3.`1 = (oget (dec_ke_rsp1 m)).`ke_rsp1_func /\ m.`3.`2 = 2.
proof.
move => val_m.
have [] x : exists (x : ke_rsp1), dec_ke_rsp1 m = Some x.
  exists (oget (dec_ke_rsp1 m)); by rewrite -some_oget.
case x => x1 x2 x3 x4.
move => /(epdp_dec_enc _ _ _ _ epdp_ke_rsp1) <-.
by rewrite (epdp_enc_dec _ _ _ epdp_ke_rsp1).
qed.

(* request sent to port index 2 of key exchange functionality by pt2 to
   initiate phase 2 of key exchange with pt1 *)

type ke_req2 =
  {ke_req2_func : addr;  (* address of functionality *)
   ke_req2_pt2  : port   (* port to exchange key with *)
   (* data: (none) *)
  }.

op ke_req2 (x : ke_req2) : msg =
     (Dir, (x.`ke_req2_func, 2), x.`ke_req2_pt2, EPDP_Univ_Unit.enc ()).

op dec_ke_req2 (m : msg) : ke_req2 option =
     let (mod, pt1, pt2, v) = m
     in (mod = Adv \/ pt1.`2 <> 2 \/ ! EPDP_Univ_Unit.valid v) ?
        None :
        Some {|ke_req2_func = pt1.`1; ke_req2_pt2 = pt2|}.

lemma epdp_ke_req2 : epdp ke_req2 dec_ke_req2.
proof.
apply epdp_intro.
move => m.
rewrite /ke_req2 /dec_ke_req2 /= EPDP_Univ_Unit.valid_enc /= /#.
move => [mod pt1 pt2 u] v.
rewrite /ke_req2 /dec_ke_req2 /=.
case (mod = Adv \/ pt1.`2 <> 2 \/ ! (EPDP_Univ_Unit.valid u)) => //.
rewrite !negb_or /= not_adv => [#] -> pt1_2 val_u.
have [] p : exists (p : unit), EPDP_Univ_Unit.dec u = Some p.
  exists (oget (EPDP_Univ_Unit.dec u)); by rewrite -some_oget.
move => /EPDP_Univ_Unit.dec_enc => <- <-.
split; first smt().
split; first smt().
split; first smt().
congr.
qed.

lemma dest_valid_ke_req2 (m : msg) :
  dec2valid dec_ke_req2 m =>
  m.`2.`1 = (oget (dec_ke_req2 m)).`ke_req2_func /\
  m.`2.`2 = 2.
proof.
move => val_m.
have [] x : exists (x : ke_req2), dec_ke_req2 m = Some x.
  exists (oget (dec_ke_req2 m)); by rewrite -some_oget.
case x => x1 x2.
move => /(epdp_dec_enc _ _ _ _ epdp_ke_req2) <-.
by rewrite (epdp_enc_dec _ _ _ epdp_ke_req2).
qed.

lemma source_valid_ke_req2 (m : msg) :
  dec2valid dec_ke_req2 m =>
  m.`3 = (oget (dec_ke_req2 m)).`ke_req2_pt2.
proof.
move => val_m.
have [] x : exists (x : ke_req2), dec_ke_req2 m = Some x.
  exists (oget (dec_ke_req2 m)); by rewrite -some_oget.
case x => x1 x2.
move => /(epdp_dec_enc _ _ _ _ epdp_ke_req2) <-.
by rewrite (epdp_enc_dec _ _ _ epdp_ke_req2).
qed.

(* response sent from port index 1 of key exchange functionality to
   pt1, completing second phase of key exchange with pt2 initiated by
   itself *)

type ke_rsp2 =
  {ke_rsp2_func : addr;   (* address of functionality *)
   ke_rsp2_pt1  : port;   (* port requesting key exchange *)
   (* data: *)
   ke_rsp2_key  : key}.   (* exchanged key *)

op ke_rsp2 (x : ke_rsp2) : msg =
     (Dir, x.`ke_rsp2_pt1, (x.`ke_rsp2_func, 1),
      EPDP_Univ_Key.enc x.`ke_rsp2_key).

op dec_ke_rsp2 (m : msg) : ke_rsp2 option =
     let (mod, pt1, pt2, v) = m
     in (mod = Adv \/ pt2.`2 <> 1 \/ ! EPDP_Univ_Key.valid v) ?
        None :
        let k = oget (EPDP_Univ_Key.dec v)
        in Some {|ke_rsp2_func = pt2.`1; ke_rsp2_pt1 = pt1;
                  ke_rsp2_key = k|}.

lemma epdp_ke_rsp2 : epdp ke_rsp2 dec_ke_rsp2.
proof.
apply epdp_intro.
move => m.
rewrite /ke_rsp2 /dec_ke_rsp2 /= EPDP_Univ_Key.valid_enc
        /= EPDP_Univ_Key.enc_dec oget_some /#.
move => [mod pt1 pt2 u] v.
rewrite /ke_rsp2 /dec_ke_rsp2 /=.
case (mod = Adv \/ pt2.`2 <> 1 \/ ! (EPDP_Univ_Key.valid u)) => //.
rewrite !negb_or /= not_adv => [#] -> pt2_2 val_u.
have [] x : exists (x : key), EPDP_Univ_Key.dec u = Some x.
  exists (oget (EPDP_Univ_Key.dec u)); by rewrite -some_oget.
move => /EPDP_Univ_Key.dec_enc <-.
rewrite EPDP_Univ_Key.enc_dec oget_some /#.
qed.

lemma dest_valid_ke_rsp2 (m : msg) :
  dec2valid dec_ke_rsp2 m =>
  m.`2 = (oget (dec_ke_rsp2 m)).`ke_rsp2_pt1.
proof.
move => val_m.
have [] x : exists (x : ke_rsp2), dec_ke_rsp2 m = Some x.
  exists (oget (dec_ke_rsp2 m)); by rewrite -some_oget.
case x => x1 x2 x3.
move => /(epdp_dec_enc _ _ _ _ epdp_ke_rsp2) <-.
by rewrite (epdp_enc_dec _ _ _ epdp_ke_rsp2).
qed.

lemma source_valid_ke_rsp2 (m : msg) :
  dec2valid dec_ke_rsp2 m =>
  m.`3.`1 = (oget (dec_ke_rsp2 m)).`ke_rsp2_func /\ m.`3.`2 = 1.
proof.
move => val_m.
have [] x : exists (x : ke_rsp2), dec_ke_rsp2 m = Some x.
  exists (oget (dec_ke_rsp2 m)); by rewrite -some_oget.
case x => x1 x2 x3.
move => /(epdp_dec_enc _ _ _ _ epdp_ke_rsp2) <-.
by rewrite (epdp_enc_dec _ _ _ epdp_ke_rsp2).
qed.

(* Real Functionality *)

clone Forward as Fwd1 with
  op adv_pi <- adv_fw1_pi
proof *.
realize fwd_pi_uniq. smt(ke_pi_uniq). qed.

clone Forward as Fwd2 with
  op adv_pi <- adv_fw2_pi
proof *.
realize fwd_pi_uniq. smt(ke_pi_uniq). qed.

(* state for Party 1 *)

type ke_real_p1_state = [
    KERealP1StateWaitReq1
  | KERealP1StateWaitFwd2 of port & exp
  | KERealP1StateFinal
].

(* state for Party 2 *)

type ke_real_p2_state = [
    KERealP2StateWaitFwd1
  | KERealP2StateWaitReq2 of port & exp
  | KERealP2StateFinal
].

module KEReal : FUNC = {
  var self, adv : addr
  var st1 : ke_real_p1_state
  var st2 : ke_real_p2_state

  (* Party 1 (P1) manages ports (self, 1) and (self, 3);
     (self, 1) is external, (self, 3) is internal

     Party 2 (P2) manages ports (self, 2) and (self, 4);
     (self, 2) is external, (self, 4) is internal

     First forwarder (Fwd1) is at address self ++ [1]
     Second forwarder (Fwd2) is at address self ++ [2] *)

  proc init(self_ adv_ : addr) : unit = {
    self <- self_; adv <- adv_;
    Fwd1.Forw.init(self ++ [1], adv); Fwd2.Forw.init(self ++ [2], adv);
    st1 <- KERealP1StateWaitReq1; st2 <- KERealP2StateWaitFwd1;
  }

  proc party1(m : msg) : msg option = {
    var q1 : exp; var k2 : key;
    var r : msg option <- None;
    match st1 with
      KERealP1StateWaitReq1 => {
        match dec_ke_req1 m with
          Some x => {
            (* destination of m is (self, 1) *)
            if (! self <= x.`ke_req1_pt2.`1 /\ ! adv <= x.`ke_req1_pt2.`1) {
              q1 <$ dexp;
              r <-
                Some
                (Fwd1.fw_req
                 {|Fwd1.fw_req_func = (self ++ [1]);
                   Fwd1.fw_req_pt1  = (self, 3);
                   Fwd1.fw_req_pt2  = (self, 4);
                   Fwd1.fw_req_u    =
                     EPDP_Univ_PortPortKey.enc
                     (x.`ke_req1_pt1, x.`ke_req1_pt2, g ^ q1)|});
              st1 <- KERealP1StateWaitFwd2 x.`ke_req1_pt1 q1;
            }
          }
        | None   => { }
        end;
      }
    | KERealP1StateWaitFwd2 pt1 q1 => {
        match Fwd2.dec_fw_rsp m with
          Some x => {
              if (x.`Fwd2.fw_rsp_pt2 = (self, 3)) {
                (* destination of m is (self, 3) *)
                k2 <- oget (EPDP_Univ_Key.dec x.`Fwd2.fw_rsp_u);
                r <-
                  Some
                  (ke_rsp2
                   ({|ke_rsp2_func = self; ke_rsp2_pt1 = pt1;
                      ke_rsp2_key  = (k2 ^ q1)|}));
                st1 <- KERealP1StateFinal;
              }
          }
        | None   => { }
        end;
      }
    | KERealP1StateFinal => { }
    end;
    return r;
  }

  proc party2(m : msg) : msg option = {
    var pt1, pt2 : port; var q2 : exp; var k1 : key;
    var r : msg option <- None;
    match st2 with
      KERealP2StateWaitFwd1 => {
        match Fwd1.dec_fw_rsp m with
          Some x => {
              if (x.`Fwd1.fw_rsp_pt2 = (self, 4)) {
                (* destination of m is (self, 4) *)
                (pt1, pt2, k1) <-
                  oget (EPDP_Univ_PortPortKey.dec x.`Fwd1.fw_rsp_u);
                q2 <$ dexp;
                r <-
                  Some
                  (ke_rsp1
                   ({|ke_rsp1_func = self; ke_rsp1_pt1 = pt1;
                      ke_rsp1_pt2 = pt2; ke_rsp1_key = k1 ^ q2|}));
                st2 <- KERealP2StateWaitReq2 pt2 q2;
              }
          }
        | None   => { }
        end;
      }
    | KERealP2StateWaitReq2 pt2 q2 => {
        match dec_ke_req2 m with
          Some x => {
            (* destination of m is (self, 2) *)
            if (x.`ke_req2_pt2 = pt2) {
              r <-
                Some
                (Fwd2.fw_req
                 {|Fwd2.fw_req_func = (self ++ [2]);
                   Fwd2.fw_req_pt1  = (self, 4);
                   Fwd2.fw_req_pt2  = (self, 3);
                   Fwd2.fw_req_u    = EPDP_Univ_Key.enc (g ^ q2)|});
              st2 <- KERealP2StateFinal;
            }
          }
        | None   => { }
        end;
      }
    | KERealP2StateFinal => { }
    end;
    return r;
  }

  proc loop(m : msg) : msg option = {
    var r : msg option <- None;
    var not_done : bool <- true;

    (* if the parties and sub-functionalities are well-behaved,
       this loop invariant holds:

         not_done =>
         m.`1 = Dir /\ m.`2.`1 = self /\
         (m.`2.`2 = 1 \/ m.`2.`2 = 2 \/ m.`2.`2 = 3 \/ m.`2.`2 = 4) \/
         self ++ [1] <= m.`2.`1 \/
         self ++ [2] <= m.`2.`1

       we guard the calls to the parties and sub-functionalities so
       that we can do some proofs treating them as black boxes *)

    while (not_done) {
      if (m.`2.`1 = self /\ (m.`2.`2 = 1 \/ m.`2.`2 = 3)) {
        r <@ party1(m);
        r <- opt_msg_guard (fun mod _ _ _ _ _ => mod <> Adv) r;
      }
      elif (m.`2.`1 = self /\ (m.`2.`2 = 2 \/ m.`2.`2 = 4)) {
        r <@ party2(m);
        r <- opt_msg_guard (fun mod _ _ _ _ _ => mod <> Adv) r;
      }
      elif (self ++ [1] <= m.`2.`1) {
        r <@ Fwd1.Forw.invoke(m);
        r <-
          opt_msg_guard
          (fun mod _ n1 _ _ _ => mod = Adv => n1 = adv_fw1_pi) r;
      }
      elif (self ++ [2] <= m.`2.`1) {
        r <@ Fwd2.Forw.invoke(m);
        r <-
          opt_msg_guard
          (fun mod _ n1 _ _ _ => mod = Adv => n1 = adv_fw2_pi) r;
      }
      else {
        (* can't happen, assuming parties and sub-functionalities
           are well behaved *)
        r <- None;
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
    var r : msg option <- None;
    (* we can assume m.`3.`1 is not >= self and not >= adv *)
    if ((m.`1 = Dir /\ m.`2.`1 = self /\
         (m.`2.`2 = 1 \/ m.`2.`2 = 2)) \/
        (m.`1 = Adv /\
         (self ++ [1] <= m.`2.`1 \/ self ++ [2] <= m.`2.`1))) {
      r <@ loop(m);
    }
    return r;
  }
}.

lemma ke_real_init :
  equiv
  [KEReal.init ~ KEReal.init :
   ={self_, adv_} ==> ={res, glob KEReal}].
proof.
proc.
swap [5..6] -2.
call Fwd2.init.
call Fwd1.init.
auto.
qed.

(* termination metric and proof for KEReal *)

op ke_real_term_metric_max : int = 8.

op ke_real_p1_term_metric (st : ke_real_p1_state) : int =
     match st with
       KERealP1StateWaitReq1     => 2
     | KERealP1StateWaitFwd2 _ _ => 1
     | KERealP1StateFinal        => 0
     end.

op ke_real_p2_term_metric (st : ke_real_p2_state) : int =
     match st with
       KERealP2StateWaitFwd1     => 2
     | KERealP2StateWaitReq2 _ _ => 1
     | KERealP2StateFinal        => 0
     end.

(* FIXME when better glob type

  print glob KEReal:

  1: KEReal.st2 : ke_real_p2_state
  2: KEReal.st1 : ke_real_p1_state
  3: KEReal.adv : addr
  4: KEReal.self : addr
  5: Fwd2.Forw.st : Fwd2.fw_state
  6: Fwd2.Forw.adv : addr
  7: Fwd2.Forw.self : addr
  8: Fwd1.Forw.st : Fwd1.fw_state
  9: Fwd1.Forw.adv : addr
  10: Fwd1.Forw.self : addr
*)

op ke_real_term_metric (g : glob KEReal) : int =
     ke_real_p1_term_metric g.`2 +
     ke_real_p2_term_metric g.`1 +
     Fwd1.term_metric (g.`8, g.`9, g.`10) +
     Fwd2.term_metric (g.`5, g.`6, g.`7).

lemma ge0_ke_real_term_metric (g : glob KEReal) :
  0 <= ke_real_term_metric g.
proof.
rewrite /ke_real_term_metric.
have p1_ge0 : 0 <= ke_real_p1_term_metric g.`2 by smt().
have p2_ge0 : 0 <= ke_real_p2_term_metric g.`1 by smt().
have fwd1_ge0 := Fwd1.ge0_term_metric (g.`8, g.`9, g.`10).
have fwd2_ge0 := Fwd2.ge0_term_metric (g.`5, g.`6, g.`7).
smt().
qed.

lemma ke_real_term_init :
  equiv
  [KEReal.init ~ KEReal.init :
   ={self_, adv_} ==>
   ={res, glob KEReal} /\
   ke_real_term_metric (glob KEReal){1} = ke_real_term_metric_max].
proof.
proc.
swap [5..6] -2.
call Fwd2.term_init.
call Fwd1.term_init.
auto; smt().
qed.

lemma ke_real_term_party1 (n : int) :
  equiv
  [KEReal.party1 ~ KEReal.party1 :
   ={m, glob KEReal} /\
   ke_real_p1_term_metric KEReal.st1{1} = n ==>
   ={res, glob KEReal} /\
   (res{1} = None \/ ke_real_p1_term_metric KEReal.st1{1} < n)].
proof.
proc.
sp 1 1.
match => //.
match => //.
move => x y.
if; first smt().
auto; smt().
auto.
move => pt1 q1 pt1' q1'.
match => //.
move => x y.
if; first smt().
auto; smt().
auto.
qed.

lemma ke_real_term_party2 (n : int) :
  equiv
  [KEReal.party2 ~ KEReal.party2 :
   ={m, glob KEReal} /\
   ke_real_p2_term_metric KEReal.st2{1} = n ==>
   ={res, glob KEReal} /\
   (res{1} = None \/ ke_real_p2_term_metric KEReal.st2{1} < n)].
proof.
proc.
sp 1 1.
match => //.
match => //.
move => x y.
if; first smt().
auto; smt().
auto.
move => pt2 q2 pt2' q2'.
match => //.
move => x y.
if; first smt().
auto; smt().
auto.
qed.

module KERealLoop = {
  proc loop(m : msg, r : msg option, not_done : bool) : msg option = {
    while (not_done) {
      if (m.`2.`1 = KEReal.self /\ (m.`2.`2 = 1 \/ m.`2.`2 = 3)) {
        r <@ KEReal.party1(m);
        r <- opt_msg_guard (fun mod _ _ _ _ _ => mod <> Adv) r;
      }
      elif (m.`2.`1 = KEReal.self /\ (m.`2.`2 = 2 \/ m.`2.`2 = 4)) {
        r <@ KEReal.party2(m);
        r <- opt_msg_guard (fun mod _ _ _ _ _ => mod <> Adv) r;
      }
      elif (KEReal.self ++ [1] <= m.`2.`1) {
        r <@ Fwd1.Forw.invoke(m);
        r <-
          opt_msg_guard
          (fun mod _ n1 _ _ _ => mod = Adv => n1 = adv_fw1_pi ) r;
      }
      elif (KEReal.self ++ [2] <= m.`2.`1) {
        r <@ Fwd2.Forw.invoke(m);
        r <-
          opt_msg_guard
          (fun mod _ n1 _ _ _ => mod = Adv => n1 = adv_fw2_pi ) r;
      }
      else {
        (* can't happen *)
        r <- None;
      }

      if (r = None \/ ! KEReal.self <= (oget r).`2.`1) {
        not_done <- false;
      }
      else {
        m <- oget r;
      }
    }
    return r;
  }
}.

lemma ke_real_term_loop (n : int) :
  equiv
  [KERealLoop.loop ~ KERealLoop.loop :
   ={m, r, not_done, glob KEReal} /\ not_done{1} /\
   ke_real_term_metric (glob KEReal){1} = n ==>
   ={res, glob KEReal} /\
   (res{1} = None \/ ke_real_term_metric (glob KEReal){1} < n)].
proof.
case (n < 0) => [le0_n | not_le_n].
exfalso; smt(ge0_ke_real_term_metric).
have : 0 <= n by smt().
clear not_le_n.
elim/sintind n => n ge0_n IH.
proc => /=.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
if => //.
(* Party 1 *)
seq 1 1 :
  (={r, glob KEReal} /\ not_done{1} /\ not_done{2} /\
   (r{1} = None \/
    ke_real_term_metric (glob KEReal){1} < n)).
exlim (ke_real_p1_term_metric KEReal.st1{1}) => p1_met.
call (ke_real_term_party1 p1_met).
auto => &1 &2 |> _ _ ? ? [] // lt_p1_met.
right; rewrite /ke_real_term_metric /#.
sp 1 1; elim* => r_R r_L.
if => //.
sp 1 1.
rcondf{1} 1; first auto.
rcondf{2} 1; first auto.
auto; smt().
sp 1 1.
transitivity*{1} { r <@ KERealLoop.loop(m, r, not_done); } => //.
progress.
by exists KEReal.adv{2} KEReal.self{2} KEReal.st1{2} KEReal.st2{2}
          Fwd1.Forw.adv{2} Fwd1.Forw.self{2} Fwd1.Forw.st{2}
          Fwd2.Forw.adv{2} Fwd2.Forw.self{2} Fwd2.Forw.st{2}
          (oget (opt_msg_guard (fun mod _ _ _ _ _ => mod <> Adv) r_R))
          not_done{1}
          (opt_msg_guard (fun mod _ _ _ _ _ => mod <> Adv) r_R).
inline{2} (1) KERealLoop.loop; sp; sim.
transitivity*{2} { r <@ KERealLoop.loop(m, r, not_done); } => //.
progress.
by exists KEReal.adv{2} KEReal.self{2} KEReal.st1{2} KEReal.st2{2}
          Fwd1.Forw.adv{2} Fwd1.Forw.self{2} Fwd1.Forw.st{2}
          Fwd2.Forw.adv{2} Fwd2.Forw.self{2} Fwd2.Forw.st{2}
          (oget (opt_msg_guard (fun mod _ _ _ _ _ => mod <> Adv) r_R))
          not_done{2}
          (opt_msg_guard (fun mod _ _ _ _ _ => mod <> Adv) r_R).
conseq
  (_ :
   ={m, r, glob KEReal} /\ not_done{1} /\ not_done{2} /\
   ke_real_term_metric (glob KEReal){1} < n ==>
   _) => [|> &1 &2 _ _ [] /# |].
exlim (ke_real_term_metric (glob KEReal){1}) => met.
case @[ambient] (0 <= met < n) => met_le_0_lt_n.
have IH_met := IH met met_le_0_lt_n.
call IH_met.
auto; progress; smt().
exfalso; smt(ge0_ke_real_term_metric).
inline{1} KERealLoop.loop; sp; sim.
if => //.
(* Party 2 *)
seq 1 1 :
  (={r, glob KEReal} /\ not_done{1} /\ not_done{2} /\
   (r{1} = None \/
    ke_real_term_metric (glob KEReal){1} < n)).
exlim (ke_real_p2_term_metric KEReal.st2{1}) => p2_met.
call (ke_real_term_party2 p2_met).
auto => &1 &2 |> _ _ _ ? ? [] // lt_p2_met.
right; rewrite /ke_real_term_metric /#.
sp 1 1; elim* => r_R r_L.
if => //.
sp 1 1.
rcondf{1} 1; first auto.
rcondf{2} 1; first auto.
auto; smt().
sp 1 1.
transitivity*{1} { r <@ KERealLoop.loop(m, r, not_done); } => //.
progress.
by exists KEReal.adv{2} KEReal.self{2} KEReal.st1{2} KEReal.st2{2}
          Fwd1.Forw.adv{2} Fwd1.Forw.self{2} Fwd1.Forw.st{2}
          Fwd2.Forw.adv{2} Fwd2.Forw.self{2} Fwd2.Forw.st{2}
          (oget (opt_msg_guard (fun mod _ _ _ _ _ => mod <> Adv) r_R))
          not_done{1}
          (opt_msg_guard (fun mod _ _ _ _ _ => mod <> Adv) r_R).
inline{2} (1) KERealLoop.loop; sp; sim.
transitivity*{2} { r <@ KERealLoop.loop(m, r, not_done); } => //.
progress.
by exists KEReal.adv{2} KEReal.self{2} KEReal.st1{2} KEReal.st2{2}
          Fwd1.Forw.adv{2} Fwd1.Forw.self{2} Fwd1.Forw.st{2}
          Fwd2.Forw.adv{2} Fwd2.Forw.self{2} Fwd2.Forw.st{2}
          (oget (opt_msg_guard (fun mod _ _ _ _ _ => mod <> Adv) r_R))
          not_done{2}
          (opt_msg_guard (fun mod _ _ _ _ _ => mod <> Adv) r_R).
conseq
  (_ :
   ={m, r, glob KEReal} /\ not_done{1} /\ not_done{2} /\
   ke_real_term_metric (glob KEReal){1} < n ==>
   _) => [|> &1 &2 _ _ [] /# |].
exlim (ke_real_term_metric (glob KEReal){1}) => met.
case @[ambient] (0 <= met < n) => met_le_0_lt_n.
have IH_met := IH met met_le_0_lt_n.
call IH_met.
auto; progress; smt().
exfalso; smt(ge0_ke_real_term_metric).
inline{1} KERealLoop.loop; sp; sim.
if => //.
(* Fwd1 *)
seq 1 1 :
  (={r, glob KEReal} /\ not_done{1} /\ not_done{2} /\
   (r{1} = None \/
    ke_real_term_metric (glob KEReal){1} < n)).
exlim (Fwd1.term_metric (glob Fwd1.Forw){1}) => fwd1_met.
call (Fwd1.term_invoke fwd1_met).
auto => &1 &2 |> _ _ _ _ ? ? [] // lt_fwd1_met.
right; rewrite /ke_real_term_metric /#.
sp 1 1; elim* => r_R r_L.
if => //.
sp 1 1.
rcondf{1} 1; first auto.
rcondf{2} 1; first auto.
auto; smt().
sp 1 1.
transitivity*{1} { r <@ KERealLoop.loop(m, r, not_done); } => //.
progress.
by exists KEReal.adv{2} KEReal.self{2} KEReal.st1{2} KEReal.st2{2}
          Fwd1.Forw.adv{2} Fwd1.Forw.self{2} Fwd1.Forw.st{2}
          Fwd2.Forw.adv{2} Fwd2.Forw.self{2} Fwd2.Forw.st{2}
          (oget
           (opt_msg_guard
            (fun mod _ n1 _ _ _ => mod = Adv => n1 = adv_fw1_pi) r_R))
           not_done{1}
          (opt_msg_guard
           (fun mod _ n1 _ _ _ => mod = Adv => n1 = adv_fw1_pi) r_R).
inline{2} (1) KERealLoop.loop; sp; sim.
transitivity*{2} { r <@ KERealLoop.loop(m, r, not_done); } => //.
progress.
by exists KEReal.adv{2} KEReal.self{2} KEReal.st1{2} KEReal.st2{2}
          Fwd1.Forw.adv{2} Fwd1.Forw.self{2} Fwd1.Forw.st{2}
          Fwd2.Forw.adv{2} Fwd2.Forw.self{2} Fwd2.Forw.st{2}
          (oget
           (opt_msg_guard
            (fun mod _ n1 _ _ _ => mod = Adv => n1 = adv_fw1_pi) r_R))
           not_done{2}
          (opt_msg_guard
           (fun mod _ n1 _ _ _ => mod = Adv => n1 = adv_fw1_pi) r_R).
conseq
  (_ :
   ={m, r, glob KEReal} /\ not_done{1} /\ not_done{2} /\
   ke_real_term_metric (glob KEReal){1} < n ==>
   _) => [|> &1 &2 _ _ [] /# |].
exlim (ke_real_term_metric (glob KEReal){1}) => met.
case @[ambient] (0 <= met < n) => met_le_0_lt_n.
have IH_met := IH met met_le_0_lt_n.
call IH_met.
auto; progress; smt().
exfalso; smt(ge0_ke_real_term_metric).
inline{1} KERealLoop.loop; sp; sim.
if => //.
(* Fwd2 *)
seq 1 1 :
  (={r, glob KEReal} /\ not_done{1} /\ not_done{2} /\
   (r{1} = None \/
    ke_real_term_metric (glob KEReal){1} < n)).
exlim (Fwd2.term_metric (glob Fwd2.Forw){1}) => fwd2_met.
call (Fwd2.term_invoke fwd2_met).
auto => &1 &2 |> _ _ _ _ _ ? ? [] // lt_fwd2_met.
right; rewrite /ke_real_term_metric /#.
sp 1 1; elim* => r_R r_L.
if => //.
sp 1 1.
rcondf{1} 1; first auto.
rcondf{2} 1; first auto.
auto; smt().
sp 1 1.
transitivity*{1} { r <@ KERealLoop.loop(m, r, not_done); } => //.
progress.
by exists KEReal.adv{2} KEReal.self{2} KEReal.st1{2} KEReal.st2{2}
          Fwd1.Forw.adv{2} Fwd1.Forw.self{2} Fwd1.Forw.st{2}
          Fwd2.Forw.adv{2} Fwd2.Forw.self{2} Fwd2.Forw.st{2}
          (oget
           (opt_msg_guard
            (fun mod _ n1 _ _ _ => mod = Adv => n1 = adv_fw2_pi) r_R))
           not_done{1}
          (opt_msg_guard
           (fun mod _ n1 _ _ _ => mod = Adv => n1 = adv_fw2_pi) r_R).
inline{2} (1) KERealLoop.loop; sp; sim.
transitivity*{2} { r <@ KERealLoop.loop(m, r, not_done); } => //.
progress.
by exists KEReal.adv{2} KEReal.self{2} KEReal.st1{2} KEReal.st2{2}
          Fwd1.Forw.adv{2} Fwd1.Forw.self{2} Fwd1.Forw.st{2}
          Fwd2.Forw.adv{2} Fwd2.Forw.self{2} Fwd2.Forw.st{2}
          (oget
           (opt_msg_guard
            (fun mod _ n1 _ _ _ => mod = Adv => n1 = adv_fw2_pi) r_R))
           not_done{2}
          (opt_msg_guard
           (fun mod _ n1 _ _ _ => mod = Adv => n1 = adv_fw2_pi) r_R).
conseq
  (_ :
   ={m, r, glob KEReal} /\ not_done{1} /\ not_done{2} /\
   ke_real_term_metric (glob KEReal){1} < n ==>
   _) => [|> &1 &2 _ _ [] /# |].
exlim (ke_real_term_metric (glob KEReal){1}) => met.
case @[ambient] (0 <= met < n) => met_le_0_lt_n.
have IH_met := IH met met_le_0_lt_n.
call IH_met.
auto; progress; smt().
exfalso; smt(ge0_ke_real_term_metric).
inline{1} KERealLoop.loop; sp; sim.
sp 1 1.
rcondt{1} 1; first auto.
rcondt{2} 1; first auto.
sp 1 1.
rcondf{1} 1; first auto.
rcondf{2} 1; first auto.
auto.
qed.

lemma ke_real_term_invoke (n : int) :
  equiv
  [KEReal.invoke ~ KEReal.invoke :
   ={m, glob KEReal} /\
   ke_real_term_metric (glob KEReal){1} = n ==>
   ={res, glob KEReal} /\
   (res{1} = None \/ ke_real_term_metric (glob KEReal){1} < n)].
proof.
proc.
sp 1 1.
if => //.
inline KEReal.loop.
sp 3 3; wp.
transitivity*{1} { r0 <@ KERealLoop.loop(m0, r0, not_done); } => //.
progress.
by exists KEReal.adv{2} KEReal.self{2} KEReal.st1{2} KEReal.st2{2}
          Fwd1.Forw.adv{2} Fwd1.Forw.self{2} Fwd1.Forw.st{2}
          Fwd2.Forw.adv{2} Fwd2.Forw.self{2} Fwd2.Forw.st{2}
          m{2} m{2} true None None.
inline{2} KERealLoop.loop; sp; sim.
transitivity*{2} { r0 <@ KERealLoop.loop(m0, r0, not_done); } => //.
progress.
by exists KEReal.adv{2} KEReal.self{2} KEReal.st1{2} KEReal.st2{2}
          Fwd1.Forw.adv{2} Fwd1.Forw.self{2} Fwd1.Forw.st{2}
          Fwd2.Forw.adv{2} Fwd2.Forw.self{2} Fwd2.Forw.st{2}
          m{2} m{2} true None None.
call (ke_real_term_loop n).
auto.
inline{1} KERealLoop.loop; sp; sim.
qed.

(* Ideal Functionality *)

(* request sent from port index 3 of key exchange ideal functionality
   to port index ke_sim_pi of key exchange simulator, initiating
   first phase of execution of simulator *)

type ke_sim_req1 =
  {ke_sim_req1_ideal : addr;   (* address of ideal functionality *)
   ke_sim_req1_adv   : addr;   (* address of adversary *)
   (* data: *)
   ke_sim_req1_pt1   : port;   (* port requesting key exchange *)
   ke_sim_req1_pt2   : port}.  (* port to exchange key with *)

op ke_sim_req1 (x : ke_sim_req1) : msg =
     (Adv, (x.`ke_sim_req1_adv, ke_sim_pi), (x.`ke_sim_req1_ideal, 3),
      EPDP_Univ_PortPort.enc (x.`ke_sim_req1_pt1, x.`ke_sim_req1_pt2)).

op dec_ke_sim_req1 (m : msg) : ke_sim_req1 option =
     let (mod, pt1, pt2, v) = m
     in (mod = Dir \/ pt1.`2 <> ke_sim_pi \/ pt2.`2 <> 3 \/
         ! EPDP_Univ_PortPort.valid v) ?
        None :
        let (pt1', pt2') = oget (EPDP_Univ_PortPort.dec v)
        in Some {|ke_sim_req1_ideal = pt2.`1; ke_sim_req1_adv = pt1.`1;
                  ke_sim_req1_pt1 = pt1'; ke_sim_req1_pt2 = pt2'|}.

lemma epdp_ke_sim_req1 : epdp ke_sim_req1 dec_ke_sim_req1.
proof.
apply epdp_intro.
move => m.
rewrite /ke_sim_req1 /dec_ke_sim_req1 /= EPDP_Univ_PortPort.valid_enc
        /= EPDP_Univ_PortPort.enc_dec oget_some /#.
move => [mod pt1 pt2 u] v.
rewrite /ke_sim_req1 /dec_ke_sim_req1 /=.
case (mod = Dir \/ pt1.`2 <> ke_sim_pi \/ pt2.`2 <> 3 \/
      ! (EPDP_Univ_PortPort.valid u)) => //.
rewrite !negb_or /= not_dir => [#] -> pt1_2 pt2_2 val_u.
have [] p : exists (p : port * port), EPDP_Univ_PortPort.dec u = Some p.
  exists (oget (EPDP_Univ_PortPort.dec u)); by rewrite -some_oget.
move => /EPDP_Univ_PortPort.dec_enc <-.
rewrite EPDP_Univ_PortPort.enc_dec oget_some /#.
qed.

lemma dest_valid_ke_sim_req1 (m : msg) :
  dec2valid dec_ke_sim_req1 m =>
  m.`2.`1 = (oget (dec_ke_sim_req1 m)).`ke_sim_req1_adv /\
  m.`2.`2 = ke_sim_pi.
proof.
move => val_m.
have [] x : exists (x : ke_sim_req1), dec_ke_sim_req1 m = Some x.
  exists (oget (dec_ke_sim_req1 m)); by rewrite -some_oget.
case x => x1 x2 x3 x4.
move => /(epdp_dec_enc _ _ _ _ epdp_ke_sim_req1) <-.
by rewrite (epdp_enc_dec _ _ _ epdp_ke_sim_req1).
qed.

lemma source_valid_ke_sim_req1 (m : msg) :
  dec2valid dec_ke_sim_req1 m =>
  m.`3.`1 = (oget (dec_ke_sim_req1 m)).`ke_sim_req1_ideal /\
  m.`3.`2 = 3.
proof.
move => val_m.
have [] x : exists (x : ke_sim_req1), dec_ke_sim_req1 m = Some x.
  exists (oget (dec_ke_sim_req1 m)); by rewrite -some_oget.
case x => x1 x2 x3 x4.
move => /(epdp_dec_enc _ _ _ _ epdp_ke_sim_req1) <-.
by rewrite (epdp_enc_dec _ _ _ epdp_ke_sim_req1).
qed.

(* response sent from port ke_sim_pi of key exchange simulator to
   port 3 of key exchange ideal functionality, completing first or
   second phase of simulator execution *)

type ke_sim_rsp =
  {ke_sim_rsp_ideal : addr;   (* address of ideal functionality *)
   ke_sim_rsp_adv   : addr;   (* address of adversary *)
   (* data: (none) *)
  }.

op ke_sim_rsp (x : ke_sim_rsp) : msg =
     (Adv, (x.`ke_sim_rsp_ideal, 3), (x.`ke_sim_rsp_adv, ke_sim_pi),
      EPDP_Univ_Unit.enc ()).

op dec_ke_sim_rsp (m : msg) : ke_sim_rsp option =
     let (mod, pt1, pt2, v) = m
     in (mod = Dir \/ pt1.`2 <> 3 \/ pt2.`2 <> ke_sim_pi \/
         ! EPDP_Univ_Unit.valid v) ?
        None :
        Some {|ke_sim_rsp_ideal = pt1.`1; ke_sim_rsp_adv = pt2.`1|}.

lemma epdp_ke_sim_rsp : epdp ke_sim_rsp dec_ke_sim_rsp.
proof.
apply epdp_intro.
move => m.
rewrite /ke_sim_rsp /dec_ke_sim_rsp /= EPDP_Univ_Unit.valid_enc /= /#.
move => [mod pt1 pt2 u] v.
rewrite /ke_sim_rsp /dec_ke_sim_rsp /=.
case (mod = Dir \/ pt1.`2 <> 3 \/ pt2.`2 <> ke_sim_pi \/
      ! (EPDP_Univ_Unit.valid u)) => //.
rewrite !negb_or /= not_dir => [#] -> pt1_2 pt2_2 val_u.
have [] p : exists (p : unit), EPDP_Univ_Unit.dec u = Some p.
  exists (oget (EPDP_Univ_Unit.dec u)); by rewrite -some_oget.
move => /EPDP_Univ_Unit.dec_enc <- <- /=.
split; first auto; smt().
split; first auto; smt().
congr.
qed.

lemma dest_valid_ke_sim_rsp (m : msg) :
  dec2valid dec_ke_sim_rsp m =>
  m.`2.`1 = (oget (dec_ke_sim_rsp m)).`ke_sim_rsp_ideal /\
  m.`2.`2 = 3.
proof.
move => val_m.
have [] x : exists (x : ke_sim_rsp), dec_ke_sim_rsp m = Some x.
  exists (oget (dec_ke_sim_rsp m)); by rewrite -some_oget.
case x => x1 x2.
move => /(epdp_dec_enc _ _ _ _ epdp_ke_sim_rsp) <-.
by rewrite (epdp_enc_dec _ _ _ epdp_ke_sim_rsp).
qed.

lemma source_valid_ke_sim_rsp (m : msg) :
  dec2valid dec_ke_sim_rsp m =>
  m.`3.`1 = (oget (dec_ke_sim_rsp m)).`ke_sim_rsp_adv /\
  m.`3.`2 = ke_sim_pi.
proof.
move => val_m.
have [] x : exists (x : ke_sim_rsp), dec_ke_sim_rsp m = Some x.
  exists (oget (dec_ke_sim_rsp m)); by rewrite -some_oget.
case x => x1 x2.
move => /(epdp_dec_enc _ _ _ _ epdp_ke_sim_rsp) <-.
by rewrite (epdp_enc_dec _ _ _ epdp_ke_sim_rsp).
qed.

(* request sent from port 3 of key exchange ideal functionality to
   port ke_sim_pi of key exchange simulator, initiating second phase
   of execution of simulator *)

type ke_sim_req2 =
  {ke_sim_req2_ideal : addr;   (* address of ideal functionality *)
   ke_sim_req2_adv   : addr;   (* address of adversary *)
   (* data: (none) *)
  }.

op ke_sim_req2 (x : ke_sim_req2) : msg =
     (Adv, (x.`ke_sim_req2_adv, ke_sim_pi), (x.`ke_sim_req2_ideal, 3),
      EPDP_Univ_Unit.enc ()).

op dec_ke_sim_req2 (m : msg) : ke_sim_req2 option =
     let (mod, pt1, pt2, v) = m
     in (mod = Dir \/ pt1.`2 <> ke_sim_pi \/ pt2.`2 <> 3 \/
         ! EPDP_Univ_Unit.valid v) ?
        None :
        Some {|ke_sim_req2_ideal = pt2.`1; ke_sim_req2_adv = pt1.`1|}.

lemma epdp_ke_sim_req2 : epdp ke_sim_req2 dec_ke_sim_req2.
proof.
apply epdp_intro.
move => m.
rewrite /ke_sim_req2 /dec_ke_sim_req2 /= EPDP_Univ_Unit.valid_enc /= /#.
move => [mod pt1 pt2 u] v.
rewrite /ke_sim_req2 /dec_ke_sim_req2 /=.
case (mod = Dir \/ pt1.`2 <> ke_sim_pi \/ pt2.`2 <> 3 \/
      ! (EPDP_Univ_Unit.valid u)) => //.
rewrite !negb_or /= not_dir => [#] -> pt1_2 pt2_2 val_u.
have [] p : exists (p : unit), EPDP_Univ_Unit.dec u = Some p.
  exists (oget (EPDP_Univ_Unit.dec u)); by rewrite -some_oget.
move => /EPDP_Univ_Unit.dec_enc <- <- /=.
split; first auto; smt().
split; first auto; smt().
congr.
qed.

lemma dest_valid_ke_sim_req2 (m : msg) :
  dec2valid dec_ke_sim_req2 m =>
  m.`2.`1 = (oget (dec_ke_sim_req2 m)).`ke_sim_req2_adv /\
  m.`2.`2 = ke_sim_pi.
proof.
move => val_m.
have [] x : exists (x : ke_sim_req2), dec_ke_sim_req2 m = Some x.
  exists (oget (dec_ke_sim_req2 m)); by rewrite -some_oget.
case x => x1 x2.
move => /(epdp_dec_enc _ _ _ _ epdp_ke_sim_req2) <-.
by rewrite (epdp_enc_dec _ _ _ epdp_ke_sim_req2).
qed.

lemma source_valid_ke_sim_req2 (m : msg) :
  dec2valid dec_ke_sim_req2 m =>
  m.`3.`1 = (oget (dec_ke_sim_req2 m)).`ke_sim_req2_ideal /\
  m.`3.`2 = 3.
proof.
move => val_m.
have [] x : exists (x : ke_sim_req2), dec_ke_sim_req2 m = Some x.
  exists (oget (dec_ke_sim_req2 m)); by rewrite -some_oget.
case x => x1 x2.
move => /(epdp_dec_enc _ _ _ _ epdp_ke_sim_req2) <-.
by rewrite (epdp_enc_dec _ _ _ epdp_ke_sim_req2).
qed.

type ke_ideal_state = [
    KEIdealStateWaitReq1
  | KEIdealStateWaitSim1 of port & port
  | KEIdealStateWaitReq2 of port & port & exp
  | KEIdealStateWaitSim2 of port & exp
  | KEIdealStateFinal
].

module KEIdeal : FUNC = {
  var self, adv : addr
  var st : ke_ideal_state

  proc init(self_ adv_ : addr) : unit = {
    self <- self_; adv <- adv_;
    st <- KEIdealStateWaitReq1;
  }

  proc parties(m : msg) : msg option = {
    var q : exp; var r : msg option <- None;
    match st with
      KEIdealStateWaitReq1 => {
        match dec_ke_req1 m with
          Some x => {
            (* destination of m is (self, 1), mode of m is Dir *)
            if (! self <= x.`ke_req1_pt2.`1 /\ ! adv <= x.`ke_req1_pt2.`1) {
              r <-
                Some
                (ke_sim_req1
                 {|ke_sim_req1_ideal = self;
                   ke_sim_req1_adv   = adv;
                   ke_sim_req1_pt1   = x.`ke_req1_pt1;
                   ke_sim_req1_pt2   = x.`ke_req1_pt2|});
              st <- KEIdealStateWaitSim1 x.`ke_req1_pt1 x.`ke_req1_pt2;
            }
          }
        | None   => { }
        end;
      }
    | KEIdealStateWaitSim1 pt1 pt2 => {
        if (dec2valid dec_ke_sim_rsp m) {
          (* destination of m is (self, 3), mode of m is Adv *)
          q <$ dexp;
          r <-
            Some
            (ke_rsp1
             {|ke_rsp1_func = self; ke_rsp1_pt1 = pt1;
               ke_rsp1_pt2 = pt2; ke_rsp1_key = g ^ q|});
          st <- KEIdealStateWaitReq2 pt1 pt2 q;
        }
      }
    | KEIdealStateWaitReq2 pt1 pt2 q => {
        match dec_ke_req2 m with
          Some x => {
            (* destination of m is (self, 2), mode of m is Dir *)
            if (x.`ke_req2_pt2 = pt2) {
              r <-
                Some
                (ke_sim_req2
                 {|ke_sim_req2_ideal = self; ke_sim_req2_adv = adv|});
              st <- KEIdealStateWaitSim2 pt1 q;
            }
          }
        | None   => { }
        end;
      }
    | KEIdealStateWaitSim2 pt1 q => {
        if (dec2valid dec_ke_sim_rsp m) {
          (* destination of m is (self, 3), mode of m is Adv *)
          r <-
            Some
            (ke_rsp2
             {|ke_rsp2_func = self; ke_rsp2_pt1 = pt1; ke_rsp2_key = g ^ q|});
          st <- KEIdealStateFinal;
        }
      }
    | KEIdealStateFinal => { }
    end;
    return r;
  }

  proc invoke(m : msg) : msg option = {
    var r : msg option <- None;
    (* we can assume m.`3.`1 is not >= self and not >= adv *)
    if ((m.`1 = Dir /\ m.`2.`1 = self /\ (m.`2.`2 = 1 \/ m.`2.`2 = 2)) \/
        (m.`1 = Adv /\ m.`2.`1 = self /\ m.`2.`2 = 3)) {
      r <@ parties(m);
    }
    return r;
  }
}.

lemma ke_ideal_init :
  equiv
  [KEIdeal.init ~ KEIdeal.init :
   ={self_, adv_} ==> ={res, glob KEIdeal}].
proof. proc; auto. qed.

(* termination metric and proof for KEIdeal *)

op ke_ideal_term_metric_max : int = 4.

op ke_ideal_term_metric (x : glob KEIdeal) : int =
     match x.`1 with
       KEIdealStateWaitReq1       => 4
     | KEIdealStateWaitSim1 _ _   => 3
     | KEIdealStateWaitReq2 _ _ _ => 2
     | KEIdealStateWaitSim2 _ _   => 1
     | KEIdealStateFinal          => 0
     end.

lemma ke_ideal_term_init :
  equiv
  [KEIdeal.init ~ KEIdeal.init :
   ={self_, adv_} ==>
   ={res, glob KEIdeal} /\
   ke_ideal_term_metric (glob KEIdeal){1} = ke_ideal_term_metric_max].
proof. proc; auto. qed.

lemma ke_ideal_term_invoke (n : int) :
  equiv
  [KEIdeal.invoke ~ KEIdeal.invoke :
   ={m, glob KEIdeal} /\
   ke_ideal_term_metric (glob KEIdeal){1} = n ==>
   ={res, glob KEIdeal} /\
   (res{1} = None \/ ke_ideal_term_metric (glob KEIdeal){1} < n)].
proof.
proc; sp 1 1.
if => //.
inline KEIdeal.parties.
sp 2 2.
match; first 5 smt().
match => //.
auto.
move => x y.
if; first smt().
auto; smt().
auto.
move => pt1 pt2 pt1' pt2'.
if => //; auto.
move => pt1 pt2 q pt1' pt2' q'.
match; first 2 smt().
auto.
move => x y.
if; [smt() | auto | auto].
move => pt1 q pt1' q'.
if => //; auto.
auto.
qed.

(* Simulator *)

type ke_sim_state = [
    KESimStateWaitReq1
  | KESimStateWaitAdv1 of addr
  | KESimStateWaitReq2 of addr & exp
  | KESimStateWaitAdv2 of addr
  | KESimStateFinal    of addr
].

module KESim (Adv : FUNC) = {
  var self, adv : addr
  var st : ke_sim_state

  proc init(self_ adv_ : addr) : unit = {
    self <- self_; adv <- adv_;
    Adv.init(self, adv);
    st <- KESimStateWaitReq1;
  }

  proc loop(m : msg) : msg option = {
    var q1, q2 : exp;
    var r : msg option <- None;
    var not_done : bool <- true;
    while (not_done) {
      (* m.`1 = Adv /\ m.`2.`1 = self *)
      if (m.`2.`2 = ke_sim_pi) {
        (* simulator, responding to ideal functionality *)
        r <- None;
        match st with
          KESimStateWaitReq1 => {
            match dec_ke_sim_req1 m with
              Some x => {
                q1 <$ dexp;
                r <-
                  Some
                  (Fwd1.fw_obs
                   {|Fwd1.fw_obs_func = x.`ke_sim_req1_ideal ++ [1];
                     Fwd1.fw_obs_adv  = self;
                     Fwd1.fw_obs_pt1  = (x.`ke_sim_req1_ideal, 3);
                     Fwd1.fw_obs_pt2  = (x.`ke_sim_req1_ideal, 4);
                     Fwd1.fw_obs_u    =
                       EPDP_Univ_PortPortKey.enc
                       (x.`ke_sim_req1_pt1, x.`ke_sim_req1_pt2, g ^ q1)|});
                st <- KESimStateWaitAdv1 x.`ke_sim_req1_ideal;
               }
            | None   => { }
            end;
          }
        | KESimStateWaitAdv1 _ => { }
        | KESimStateWaitReq2 func q2 => {
            if (dec2valid dec_ke_sim_req2 m) {
              r <-
                Some
                (Fwd2.fw_obs
                 {|Fwd2.fw_obs_func = func ++ [2];
                   Fwd2.fw_obs_adv  = self;
                   Fwd2.fw_obs_pt1  = (func, 4);
                   Fwd2.fw_obs_pt2  = (func, 3);
                   Fwd2.fw_obs_u    = EPDP_Univ_Key.enc (g ^ q2)|});
              st <- KESimStateWaitAdv2 func;
            }
          }
        | KESimStateWaitAdv2 _ => { }
        | KESimStateFinal _ => { }
        end;
        if (r = None) {  (* should not happen *)
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
          m <- oget r;
          if (m.`1 = Dir \/ self <= m.`2.`1) {
            r <- None; not_done <- false;
          }
          else {
            match st with
              KESimStateWaitReq1 => {
                not_done <- false;
                (* r may go to ideal functionality, which
                   simulator doesn't yet know address of! *)
              }
            | KESimStateWaitAdv1 func => {
                not_done <- false;
                if (func <= m.`2.`1) {
                  r <- None; 
                  match Fwd1.dec_fw_ok m with
                    Some x => {
                      if (x.`Fwd1.fw_ok_func = func ++ [1]) {
                        q2 <$ dexp;
                        r <-
                          Some
                          (ke_sim_rsp
                           {|ke_sim_rsp_ideal = func;
                             ke_sim_rsp_adv   = self|});
                        st <- KESimStateWaitReq2 func q2;
                      }
                    }
                  | None   => { }
                  end;
                }
              }
            | KESimStateWaitReq2 func _ => {
                not_done <- false;
                if (func <= m.`2.`1) {
                  r <- None;
                }
              }
            | KESimStateWaitAdv2 func => {
                not_done <- false;
                if (func <= m.`2.`1) {
                  r <- None;
                  match Fwd2.dec_fw_ok m with
                    Some x => {
                      if (x.`Fwd2.fw_ok_func = func ++ [2]) {
                        r <-
                          Some
                          (ke_sim_rsp
                           {|ke_sim_rsp_ideal = func;
                             ke_sim_rsp_adv   = self|});
                        st <- KESimStateFinal func;
                      }
                    }
                  | None   => { }
                  end;
                }
              }
            | KESimStateFinal func => {
                not_done <- false;
                if (func <= m.`2.`1) {
                  r <- None;
                }
              }
            end;
          }
        }
      }
    }
    return r;
  }

  proc invoke(m : msg) : msg option = {
    var mod : mode; var pt1, pt2 : port; var u : univ;
    var r : msg option <- None;
    if (m.`1 = Adv /\ m.`2.`1 = self) {
      r <@ loop(m);
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
      r <@ parties(m);
    }
    return r;
  }
}.

lemma ke_real_simp_init :
  equiv
  [KERealSimp.init ~ KERealSimp.init :
   ={self_, adv_} ==> ={glob KERealSimp}].
proof.
proc; auto.
qed.

(* termination metric and proof for KERealSimp *)

op ke_real_simp_term_metric_max : int = 4.

op ke_real_simp_term_metric (st : ke_real_simp_state) : int =
     with st = KERealSimpStateWaitReq1   => 4
     with st = KERealSimpStateWaitAdv1 _ => 3
     with st = KERealSimpStateWaitReq2 _ => 2
     with st = KERealSimpStateWaitAdv2 _ => 1
     with st = KERealSimpStateFinal _    => 0.

lemma ge0_ke_real_simp_term_metric (st : ke_real_simp_state) :
  0 <= ke_real_simp_term_metric st.
proof. by case st. qed.

lemma ke_real_simp_term_metric_is_ke_real_simp_state_wait_adv1
      (st : ke_real_simp_state) :
  is_ke_real_simp_state_wait_adv1 st => ke_real_simp_term_metric st = 3.
proof. by case st. qed.

lemma ke_real_simp_term_metric_is_ke_real_simp_state_wait_req2
      (st : ke_real_simp_state) :
  is_ke_real_simp_state_wait_req2 st => ke_real_simp_term_metric st = 2.
proof. by case st. qed.

lemma ke_real_simp_term_metric_is_ke_real_simp_state_wait_adv2
      (st : ke_real_simp_state) :
  is_ke_real_simp_state_wait_adv2 st => ke_real_simp_term_metric st = 1.
proof. by case st. qed.

lemma ke_real_simp_term_init :
  equiv
  [KERealSimp.init ~ KERealSimp.init :
   ={self_, adv_} ==>
   ={res, glob KERealSimp} /\
   ke_real_simp_term_metric KERealSimp.st{1} = ke_real_simp_term_metric_max].
proof. proc; auto. qed.

lemma ke_real_simp_term_invoke (n : int) :
  equiv
  [KERealSimp.invoke ~ KERealSimp.invoke :
   ={m, glob KERealSimp} /\
   ke_real_simp_term_metric KERealSimp.st{1} = n ==>
   ={res, KERealSimp.st} /\
   (res{1} = None \/ ke_real_simp_term_metric KERealSimp.st{1} = n - 1)].
proof.
proc; sp 3 3.
if => //.
inline KERealSimp.parties.
sp 2 2.
if => //.
if => //.
sp 1 1.
if; first smt().
auto =>
  &1 &2 [#] oget_req1_2 oget_req1_1 ->> _ ->> _ _ _ _ _ _ _
  ->>.
rewrite -oget_req1_2 /= in oget_req1_1.
by elim oget_req1_1 => _ [#] -> ->.
auto.
auto.
if => //.
sp 1 1.
if => //.
sp 1 1.
if; first smt().
auto.
auto => &1 &2 |> _ _ <- [#] -> -> ->.
progress.
smt(ke_real_simp_term_metric_is_ke_real_simp_state_wait_adv1).
auto.
auto.
if => //.
sp 1 1.
if => //.
sp 1 1.
if; first smt().
auto => |> &1 &2 _ _ <- [#] -> -> -> ->.
progress.
smt(ke_real_simp_term_metric_is_ke_real_simp_state_wait_req2).
auto.
auto.
if => //.
sp 1 1.
if => //.
sp 1 1.
if; first smt().
auto => |> &1 &2 _ _ <- [#] -> -> -> ->.
progress.
smt(ke_real_simp_term_metric_is_ke_real_simp_state_wait_adv2).
auto.
auto.
auto.
qed.

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

lemma KEReal_KERealSimp_init (func adv : addr) :
  equiv
  [KEReal.init ~ KERealSimp.init :  
   ={self_, adv_} /\ self_{1} = func /\ adv_{1} = adv ==>
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
     real_simp_rel_st_rss  = KERealSimp.st{2}|}].
proof.
proc; inline*; auto; progress.
apply RealSimpRel0; smt().
qed.

lemma KEReal_KERealSimp_invoke (func adv : addr) :
  equiv
  [KEReal.invoke ~ KERealSimp.invoke :
   inc func adv /\ ={m} /\
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
if; first smt().
seq 1 1 :
  (inc KEReal.self{1} KEReal.adv{1} /\
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
auto; smt().
rcondf{1} 4; first auto; progress; rewrite oget_some; smt(le_ext_r).
sp.
rcondt{1} 1; first auto.
rcondf{1} 1.
progress; auto; progress; rewrite oget_some; smt(ne_cat_nonnil_r).
rcondf{1} 1.
progress; auto; progress; rewrite oget_some; smt(ne_cat_nonnil_r).
rcondt{1} 1.
progress; auto; progress; rewrite oget_some; smt(le_refl).
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
rewrite oget_some Fwd1.enc_dec_fw_req oget_some /=.
by rewrite inc_nle_r.
rewrite oget_some Fwd1.enc_dec_fw_req oget_some /=.
by rewrite inc_nle_r.
rcondt{1} 7; first auto; progress.
by rewrite oget_some /Fwd1.fw_obs /= inc_nle_l.
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
rcondf{1} 3; first auto; smt(Fwd1.not_is_fw_req_suff).
auto.
inline Fwd2.Forw.invoke.
rcondt{1} 3; first auto; smt().
rcondf{1} 3; first auto; smt(Fwd1.not_is_fw_req_suff).
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
rewrite oget_some /= oget_some /=; smt(Fwd1.dest_good_fw_ok le_refl).
rcondt{1} 9; first auto.
rcondf{1} 9; first auto.
auto => |> &hr _ _ _ @/real_simp_rel1 /= [#] _ _ _ _ -> _ _ _ _ _.
rewrite oget_some /= oget_some /#.
rcondt{1} 9.
auto => |> &hr _ _ _ @/real_simp_rel1 /= [#] _ _ _ _ -> _ _ _ _ _.
rewrite oget_some /= oget_some /#.
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
rcondf{1} 4; first auto; progress.
rewrite oget_some /=; smt(le_ext_r).
sp.
rcondt{1} 1; first auto.
rcondf{1} 1; first auto; progress.
rewrite oget_some /=; smt(ne_cat_nonnil_r).
rcondf{1} 1; first auto.
rcondf{1} 1; first auto; progress.
rewrite oget_some /=; smt(le_ext_comm sing_not_le).
inline{1} (1) Fwd2.Forw.invoke.
rcondt{1} 3; first auto; smt().
rcondt{1} 3; first auto.
sp 3 0.
rcondt{1} 1; first auto => /> &hr.
rewrite oget_some Fwd2.enc_dec_fw_req oget_some /=.
progress.
by rewrite not_le_ext_nonnil_l.
by rewrite not_le_ext_nonnil_l.
by rewrite inc_nle_r.
by rewrite inc_nle_r.
rcondt{1} 4; auto; progress.
by rewrite oget_some /Fwd2.fw_obs /= inc_nle_l.
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
rcondf{1} 3; first auto; smt(Fwd1.not_is_fw_req_suff).
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
rewrite oget_some /= oget_some /=; smt(le_refl).
rcondt{1} 9; first auto.
rcondt{1} 9.
auto => |> &hr _ _ _ _ _ @/real_simp_rel3 /= [#] _ _ _ _ _ -> _ _ _ _.
rewrite oget_some /= oget_some /#.
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
      (Adv <: FUNC{MI, KEReal, KERealSimp})
      (Env <: ENV{MI, KEReal, KERealSimp, Adv})
      (func' adv' : addr) (in_guard' : int fset) &m :
  inc func' adv' =>
  Pr[Exper(MI(KEReal, Adv), Env).main
       (func', adv', in_guard') @ &m : res] =
  Pr[Exper(MI(KERealSimp, Adv), Env).main
       (func', adv', in_guard') @ &m : res].
proof.
move => pre.
byequiv => //; proc; inline*.
seq 23 12 :
  (inc func' adv' /\ ={func, adv, in_guard, glob Env, glob Adv, glob MI} /\
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
   inc func' adv' /\ ={glob Adv, glob MI} /\
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
   inc func' adv' /\ ={glob Adv, glob MI} /\
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
  var in_guard : int fset
  var k1, k2, k3 : key

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
                          (UnivBase (BaseKey k1));
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
            r <- Some (ke_rsp1 self pt1 pt2 k3);
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
            u <- UnivBase (BaseKey k2);
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
            r <- Some (ke_rsp2 self pt1 k3);
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
        r <@ parties(m);
      }
      return r;
    }
  }

  proc main(k1_ k2_ k3_ : key) : bool = {
    var b : bool;
    k1 <- k1_; k2 <- k2_; k3 <- k3_;
    b <@ Exper(MI(KEDDH, Adv), Env).main(func, adv, in_guard);
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
        r <@ parties(m);
      }
      return r;
    }
  }

  proc main() : bool = {
    var b : bool;
    Hash.rhash(exp1); Hash.rhash(exp2);
    b <@ Exper(MI(KERealSimpHash, Adv), Env).main
           (DDH_Adv.func, DDH_Adv.adv, DDH_Adv.in_guard);
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
if; first smt().
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
            (func' adv' : addr, in_guard' : int fset) &m :
  DDH_Adv.func{m} = func' => DDH_Adv.adv{m} = adv' =>
  DDH_Adv.in_guard{m} = in_guard' =>
  Pr[Exper(MI(KERealSimp, Adv), Env).main
       (func', adv', in_guard') @ &m : res] =
  Pr[RH.GOptHashing(KERealSimpHashingAdv).main() @ &m : res].
proof.
move => func'_eq adv'_eq in_guard'_eq.
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
   func{1} = MI.func{1} /\ KERealSimp.self{1} = func{1} /\
   adv{1} = MI.adv{1} /\ KERealSimp.adv{1} = adv{1} /\
   in_guard_{1} = MI.in_guard{1} /\
   KERealSimp.st{1} = KERealSimpStateWaitReq1 /\
   RH.OptHashing.mp{2} = empty /\
   ={glob Adv, glob Env}).
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
  real_simp_hash_ddh1_rel_st_k1  : key;
  real_simp_hash_ddh1_rel_st_k2  : key;
  real_simp_hash_ddh1_rel_st_rss : ke_real_simp_state;
  real_simp_hash_ddh1_rel_st_hs  : ke_ddh_state;
}.

pred real_simp_hash_ddh1_rel0 (st : real_simp_hash_ddh1_rel_st) =
  st.`real_simp_hash_ddh1_rel_st_rss = KERealSimpStateWaitReq1 /\
  st.`real_simp_hash_ddh1_rel_st_hs = KEDDHStateWaitReq1.

pred real_simp_hash_ddh1_rel1
     (st : real_simp_hash_ddh1_rel_st, pt1 pt2 : port) =
  st.`real_simp_hash_ddh1_rel_st_rss =
  KERealSimpStateWaitAdv1 (pt1, pt2, log st.`real_simp_hash_ddh1_rel_st_k1) /\
  st.`real_simp_hash_ddh1_rel_st_hs =
  KEDDHStateWaitAdv1 (pt1, pt2).

pred real_simp_hash_ddh1_rel2
     (st : real_simp_hash_ddh1_rel_st, pt1 pt2 : port) =
  st.`real_simp_hash_ddh1_rel_st_rss =
  KERealSimpStateWaitReq2
  (pt1, pt2,
   log st.`real_simp_hash_ddh1_rel_st_k1,
   log st.`real_simp_hash_ddh1_rel_st_k2) /\
  st.`real_simp_hash_ddh1_rel_st_hs =
  KEDDHStateWaitReq2 (pt1, pt2).

pred real_simp_hash_ddh1_rel3
     (st : real_simp_hash_ddh1_rel_st, pt1 pt2 : port) =
  st.`real_simp_hash_ddh1_rel_st_rss =
  KERealSimpStateWaitAdv2
  (pt1, pt2,
   log st.`real_simp_hash_ddh1_rel_st_k1,
   log st.`real_simp_hash_ddh1_rel_st_k2) /\
  st.`real_simp_hash_ddh1_rel_st_hs =
  KEDDHStateWaitAdv2 (pt1, pt2).

pred real_simp_hash_ddh1_rel4
     (st : real_simp_hash_ddh1_rel_st, pt1 pt2 : port) =
  st.`real_simp_hash_ddh1_rel_st_rss =
  KERealSimpStateFinal
  (pt1, pt2,
   log st.`real_simp_hash_ddh1_rel_st_k1,
   log st.`real_simp_hash_ddh1_rel_st_k2) /\
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
   RH.NonOptHashing.mp{1}.[exp1] = Some (log DDH_Adv.k1{2}) /\
   RH.NonOptHashing.mp{1}.[exp2] = Some (log DDH_Adv.k2{2}) /\
   DDH_Adv.k3{2} = g ^ (log DDH_Adv.k1{2} * log DDH_Adv.k2{2}) /\
   ={MI.func, MI.adv, MI.in_guard} /\
   ={self, adv}(KERealSimpHashingAdv.KERealSimpHash, DDH_Adv.KEDDH) /\
   DDH_Adv.KEDDH.self{2} = MI.func{1} /\
   DDH_Adv.KEDDH.adv{2} = MI.adv{1} /\
   ={glob Adv} /\
   real_simp_hash_ddh1_rel
   {|real_simp_hash_ddh1_rel_st_k1 = DDH_Adv.k1{2};
     real_simp_hash_ddh1_rel_st_k2 = DDH_Adv.k2{2};
     real_simp_hash_ddh1_rel_st_rss =
     KERealSimpHashingAdv.KERealSimpHash.st{1};
     real_simp_hash_ddh1_rel_st_hs = DDH_Adv.KEDDH.st{2}|} ==>
   ={res} /\
   RH.NonOptHashing.mp{1}.[exp1] = Some (log DDH_Adv.k1{2}) /\
   RH.NonOptHashing.mp{1}.[exp2] = Some (log DDH_Adv.k2{2}) /\
   DDH_Adv.k3{2} = g ^ (log DDH_Adv.k1{2} * log DDH_Adv.k2{2}) /\
   ={MI.func, MI.adv, MI.in_guard} /\
   ={self, adv}(KERealSimpHashingAdv.KERealSimpHash, DDH_Adv.KEDDH) /\
   DDH_Adv.KEDDH.self{2} = MI.func{1} /\
   DDH_Adv.KEDDH.adv{2} = MI.adv{1} /\
   ={glob Adv} /\
   real_simp_hash_ddh1_rel
   {|real_simp_hash_ddh1_rel_st_k1 = DDH_Adv.k1{2};
     real_simp_hash_ddh1_rel_st_k2 = DDH_Adv.k2{2};
     real_simp_hash_ddh1_rel_st_rss =
     KERealSimpHashingAdv.KERealSimpHash.st{1};
     real_simp_hash_ddh1_rel_st_hs = DDH_Adv.KEDDH.st{2}|}].
proof.
proc.
case
  (real_simp_hash_ddh1_rel0
   {|real_simp_hash_ddh1_rel_st_k1 = DDH_Adv.k1{2};
     real_simp_hash_ddh1_rel_st_k2 = DDH_Adv.k2{2};
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
clear H8 H7 H6 H5; smt(log_gen).
by rewrite (RealSimpHashDDH1Rel1 _ pt10{2} pt20{2})
           /real_simp_hash_ddh1_rel1 /= H oget_some.
auto.
auto.
case
  (exists (pt1 pt2 : port),
   real_simp_hash_ddh1_rel1
   {|real_simp_hash_ddh1_rel_st_k1 = DDH_Adv.k1{2};
     real_simp_hash_ddh1_rel_st_k2 = DDH_Adv.k2{2};
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
if; first smt().
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
   {|real_simp_hash_ddh1_rel_st_k1 = DDH_Adv.k1{2};
     real_simp_hash_ddh1_rel_st_k2 = DDH_Adv.k2{2};
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
smt(log_gen).
by rewrite (RealSimpHashDDH1Rel3 _ pt1 pt2) /real_simp_hash_ddh1_rel3.
auto.
auto.
case
  (exists (pt1 pt2 : port),
   real_simp_hash_ddh1_rel3
   {|real_simp_hash_ddh1_rel_st_k1 = DDH_Adv.k1{2};
     real_simp_hash_ddh1_rel_st_k2 = DDH_Adv.k2{2};
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
if; first smt().
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
   {|real_simp_hash_ddh1_rel_st_k1 = DDH_Adv.k1{2};
     real_simp_hash_ddh1_rel_st_k2 = DDH_Adv.k2{2};
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
            (func' adv' : addr, in_guard' : int fset) &m :
  DDH_Adv.func{m} = func' => DDH_Adv.adv{m} = adv' =>
  DDH_Adv.in_guard{m} = in_guard' =>
  Pr[RH.GNonOptHashing(KERealSimpHashingAdv).main() @ &m : res] =
  Pr[DDH1(DDH_Adv(Env, Adv)).main() @ &m : res].
proof.
move => func'_eq adv'_eq in_guard'_eq.
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
  (={DDH_Adv.func, DDH_Adv.adv, DDH_Adv.in_guard, glob Adv, glob Env} /\
   DDH_Adv.func{1} = func' /\ DDH_Adv.adv{1} = adv' /\
   RH.NonOptHashing.mp{1}.[exp1] = Some q1{2} /\
   RH.NonOptHashing.mp{1}.[exp2] = Some q2{2} /\
   DDH_Adv.k1{2} = g ^ q1{2} /\
   DDH_Adv.k2{2} = g ^ q2{2} /\
   DDH_Adv.k3{2} = g ^ (q1{2} * q2{2})).
auto; progress.
by rewrite get_setE /= get_setE /=.
by rewrite get_setE /=.
seq 15 15 :
  (RH.NonOptHashing.mp{1}.[exp1] = Some q1{2} /\
   RH.NonOptHashing.mp{1}.[exp2] = Some q2{2} /\
   DDH_Adv.k1{2} = g ^ q1{2} /\
   DDH_Adv.k2{2} = g ^ q2{2} /\
   DDH_Adv.k3{2} = g ^ (q1{2} * q2{2}) /\
   ={func, adv, in_guard, MI.func, MI.adv, MI.in_guard} /\
   ={self, adv}(KERealSimpHashingAdv.KERealSimpHash, DDH_Adv.KEDDH) /\
   DDH_Adv.KEDDH.self{2} = MI.func{1} /\
   DDH_Adv.KEDDH.adv{2} = MI.adv{1} /\
   ={glob Adv, glob Env} /\
   KERealSimpHashingAdv.KERealSimpHash.st{1} = KERealSimpStateWaitReq1 /\
   DDH_Adv.KEDDH.st{2} = KEDDHStateWaitReq1).
call (_ : true).
auto.
call
  (_ :
   RH.NonOptHashing.mp{1}.[exp1] = Some (log DDH_Adv.k1{2}) /\
   RH.NonOptHashing.mp{1}.[exp2] = Some (log DDH_Adv.k2{2}) /\
   DDH_Adv.k3{2} = g ^ (log DDH_Adv.k1{2} * log DDH_Adv.k2{2}) /\
   ={MI.func, MI.adv, MI.in_guard} /\
   ={self, adv}(KERealSimpHashingAdv.KERealSimpHash, DDH_Adv.KEDDH) /\
   DDH_Adv.KEDDH.self{2} = MI.func{1} /\
   DDH_Adv.KEDDH.adv{2} = MI.adv{1} /\
   ={glob Adv} /\
   real_simp_hash_ddh1_rel
   {|real_simp_hash_ddh1_rel_st_k1 = DDH_Adv.k1{2};
     real_simp_hash_ddh1_rel_st_k2 = DDH_Adv.k2{2};
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
   RH.NonOptHashing.mp{1}.[exp1] = Some (log DDH_Adv.k1{2}) /\
   RH.NonOptHashing.mp{1}.[exp2] = Some (log DDH_Adv.k2{2}) /\
   DDH_Adv.k3{2} = g ^ (log DDH_Adv.k1{2} * log DDH_Adv.k2{2}) /\
   ={MI.func, MI.adv, MI.in_guard} /\
   ={self, adv}(KERealSimpHashingAdv.KERealSimpHash, DDH_Adv.KEDDH) /\
   DDH_Adv.KEDDH.self{2} = MI.func{1} /\
   DDH_Adv.KEDDH.adv{2} = MI.adv{1} /\
   ={glob Adv} /\
   real_simp_hash_ddh1_rel
   {|real_simp_hash_ddh1_rel_st_k1 = DDH_Adv.k1{2};
     real_simp_hash_ddh1_rel_st_k2 = DDH_Adv.k2{2};
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
by rewrite gen_log.
by rewrite gen_log.
by rewrite 2!gen_log.
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
      r <@ parties(m);
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
        r <@ parties(m);
      }
      return r;
    }
  }

  proc main() : bool = {
    var b : bool;
    Hash.rhash(exp1); Hash.rhash(exp2); Hash.rhash(exp3);
    b <@ Exper(MI(KEHybridHash, Adv), Env).main
           (DDH_Adv.func, DDH_Adv.adv, DDH_Adv.in_guard);
    return b;
  }
}.

(* relation supporting transition from
   RH.GNonOptHashing(KEHybridHashingAdv) to
   DDH2(DDH_Adv(Env, Adv)) *)

type hybrid_hash_ddh2_rel_st = {
  hybrid_hash_ddh2_rel_st_k1  : key;
  hybrid_hash_ddh2_rel_st_k2  : key;
  hybrid_hash_ddh2_rel_st_k3  : key;
  hybrid_hash_ddh2_rel_st_rss : ke_hybrid_state;
  hybrid_hash_ddh2_rel_st_hs  : ke_ddh_state;
}.

pred hybrid_hash_ddh2_rel0 (st : hybrid_hash_ddh2_rel_st) =
  st.`hybrid_hash_ddh2_rel_st_rss = KEHybridStateWaitReq1 /\
  st.`hybrid_hash_ddh2_rel_st_hs = KEDDHStateWaitReq1.

pred hybrid_hash_ddh2_rel1
     (st : hybrid_hash_ddh2_rel_st, pt1 pt2 : port) =
  st.`hybrid_hash_ddh2_rel_st_rss =
  KEHybridStateWaitAdv1 (pt1, pt2, log st.`hybrid_hash_ddh2_rel_st_k1) /\
  st.`hybrid_hash_ddh2_rel_st_hs =
  KEDDHStateWaitAdv1 (pt1, pt2).

pred hybrid_hash_ddh2_rel2
     (st : hybrid_hash_ddh2_rel_st, pt1 pt2 : port) =
  st.`hybrid_hash_ddh2_rel_st_rss =
  KEHybridStateWaitReq2
  (pt1, pt2,
   log st.`hybrid_hash_ddh2_rel_st_k1,
   log st.`hybrid_hash_ddh2_rel_st_k2,
   log st.`hybrid_hash_ddh2_rel_st_k3) /\
  st.`hybrid_hash_ddh2_rel_st_hs =
  KEDDHStateWaitReq2 (pt1, pt2).

pred hybrid_hash_ddh2_rel3
     (st : hybrid_hash_ddh2_rel_st, pt1 pt2 : port) =
  st.`hybrid_hash_ddh2_rel_st_rss =
  KEHybridStateWaitAdv2
  (pt1, pt2,
   log st.`hybrid_hash_ddh2_rel_st_k1,
   log st.`hybrid_hash_ddh2_rel_st_k2,
   log st.`hybrid_hash_ddh2_rel_st_k3) /\
  st.`hybrid_hash_ddh2_rel_st_hs =
  KEDDHStateWaitAdv2 (pt1, pt2).

pred hybrid_hash_ddh2_rel4
     (st : hybrid_hash_ddh2_rel_st, pt1 pt2 : port) =
  st.`hybrid_hash_ddh2_rel_st_rss =
  KEHybridStateFinal
  (pt1, pt2,
   log st.`hybrid_hash_ddh2_rel_st_k1,
   log st.`hybrid_hash_ddh2_rel_st_k2,
   log st.`hybrid_hash_ddh2_rel_st_k3) /\
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
   RH.NonOptHashing.mp{1}.[exp1] = Some (log DDH_Adv.k1{2}) /\
   RH.NonOptHashing.mp{1}.[exp2] = Some (log DDH_Adv.k2{2}) /\
   RH.NonOptHashing.mp{1}.[exp3] = Some (log DDH_Adv.k3{2}) /\
   ={MI.func, MI.adv, MI.in_guard} /\
   ={self, adv}(KEHybridHashingAdv.KEHybridHash, DDH_Adv.KEDDH) /\
   DDH_Adv.KEDDH.self{2} = MI.func{1} /\
   DDH_Adv.KEDDH.adv{2} = MI.adv{1} /\
   ={glob Adv} /\
   hybrid_hash_ddh2_rel
   {|hybrid_hash_ddh2_rel_st_k1 = DDH_Adv.k1{2};
     hybrid_hash_ddh2_rel_st_k2 = DDH_Adv.k2{2};
     hybrid_hash_ddh2_rel_st_k3 = DDH_Adv.k3{2};
     hybrid_hash_ddh2_rel_st_rss =
     KEHybridHashingAdv.KEHybridHash.st{1};
     hybrid_hash_ddh2_rel_st_hs = DDH_Adv.KEDDH.st{2}|} ==>
   ={res} /\
   RH.NonOptHashing.mp{1}.[exp1] = Some (log DDH_Adv.k1{2}) /\
   RH.NonOptHashing.mp{1}.[exp2] = Some (log DDH_Adv.k2{2}) /\
   RH.NonOptHashing.mp{1}.[exp3] = Some (log DDH_Adv.k3{2}) /\
   ={MI.func, MI.adv, MI.in_guard} /\
   ={self, adv}(KEHybridHashingAdv.KEHybridHash, DDH_Adv.KEDDH) /\
   DDH_Adv.KEDDH.self{2} = MI.func{1} /\
   DDH_Adv.KEDDH.adv{2} = MI.adv{1} /\
   ={glob Adv} /\
   hybrid_hash_ddh2_rel
   {|hybrid_hash_ddh2_rel_st_k1 = DDH_Adv.k1{2};
     hybrid_hash_ddh2_rel_st_k2 = DDH_Adv.k2{2};
     hybrid_hash_ddh2_rel_st_k3 = DDH_Adv.k3{2};
     hybrid_hash_ddh2_rel_st_rss =
     KEHybridHashingAdv.KEHybridHash.st{1};
     hybrid_hash_ddh2_rel_st_hs = DDH_Adv.KEDDH.st{2}|}].
proof.
proc.
case
  (hybrid_hash_ddh2_rel0
   {|hybrid_hash_ddh2_rel_st_k1 = DDH_Adv.k1{2};
     hybrid_hash_ddh2_rel_st_k2 = DDH_Adv.k2{2};
     hybrid_hash_ddh2_rel_st_k3 = DDH_Adv.k3{2};
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
if; first smt().
inline{1} (1) RH.NonOptHashing.hash.
rcondf{1} 2; first auto; smt().
auto => &1 &2 |> <-.
progress.
smt(log_gen).
by rewrite (HybridHashDDH2Rel1 _ pt10{2} pt20{2})
           /hybrid_hash_ddh2_rel1 /= H oget_some.
auto.
auto.
case
  (exists (pt1 pt2 : port),
   hybrid_hash_ddh2_rel1
   {|hybrid_hash_ddh2_rel_st_k1 = DDH_Adv.k1{2};
     hybrid_hash_ddh2_rel_st_k2 = DDH_Adv.k2{2};
     hybrid_hash_ddh2_rel_st_k3 = DDH_Adv.k3{2};
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
if; first smt().
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
by rewrite mp_exp3_eq oget_some; smt(log_gen).
by rewrite (HybridHashDDH2Rel2 _ pt1 pt2)
           /hybrid_hash_ddh2_rel2 /=
           mp_exp2_eq oget_some mp_exp3_eq oget_some.
auto.
auto.
case
  (exists (pt1 pt2 : port),
   hybrid_hash_ddh2_rel2
   {|hybrid_hash_ddh2_rel_st_k1 = DDH_Adv.k1{2};
     hybrid_hash_ddh2_rel_st_k2 = DDH_Adv.k2{2};
     hybrid_hash_ddh2_rel_st_k3 = DDH_Adv.k3{2};
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
smt(log_gen).
by rewrite (HybridHashDDH2Rel3 _ pt1 pt2) /hybrid_hash_ddh2_rel3.
auto.
auto.
case
  (exists (pt1 pt2 : port),
   hybrid_hash_ddh2_rel3
   {|hybrid_hash_ddh2_rel_st_k1 = DDH_Adv.k1{2};
     hybrid_hash_ddh2_rel_st_k2 = DDH_Adv.k2{2};
     hybrid_hash_ddh2_rel_st_k3 = DDH_Adv.k3{2};
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
if; first smt().
auto => &1 &2 |> <- /= [#] -> _ dec_wait2 dec_wait1
        mp_exp1_eq mp_exp2_eq _ _ _ _ _
        @/hybrid_hash_ddh2_rel3 /= [#] ->> ->>.
rewrite /= oget_some /= in dec_wait1.
elim dec_wait1 => ->> [#] ->> ->> ->>.
rewrite /= oget_some /= in dec_wait2.
elim dec_wait2 => ->> ->>.
progress.
smt(log_gen).
rewrite (HybridHashDDH2Rel4 _ pt1 pt2) /#.
auto.
auto.
case
  (exists (pt1 pt2 : port),
   hybrid_hash_ddh2_rel4
   {|hybrid_hash_ddh2_rel_st_k1 = DDH_Adv.k1{2};
     hybrid_hash_ddh2_rel_st_k2 = DDH_Adv.k2{2};
     hybrid_hash_ddh2_rel_st_k3 = DDH_Adv.k3{2};
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
            (func' adv' : addr, in_guard' : int fset) &m :
  DDH_Adv.func{m} = func' => DDH_Adv.adv{m} = adv' =>
  DDH_Adv.in_guard{m} = in_guard' =>
  Pr[RH.GNonOptHashing(KEHybridHashingAdv).main() @ &m : res] =
  Pr[DDH2(DDH_Adv(Env, Adv)).main() @ &m : res].
proof.
move => func'_eq adv'_eq in_guard'_eq.
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
  (={DDH_Adv.func, DDH_Adv.adv, DDH_Adv.in_guard, glob Adv, glob Env} /\
   RH.NonOptHashing.mp{1}.[exp1] = Some q1{2} /\
   RH.NonOptHashing.mp{1}.[exp2] = Some q2{2} /\
   RH.NonOptHashing.mp{1}.[exp3] = Some q3{2} /\
   DDH_Adv.k1{2} = g ^ q1{2} /\
   DDH_Adv.k2{2} = g ^ q2{2} /\
   DDH_Adv.k3{2} = g ^ q3{2}).
auto; progress.
by rewrite get_setE /= get_setE /= get_setE.
by rewrite get_setE /= get_setE.
by rewrite get_setE.
seq 15 15 :
  (RH.NonOptHashing.mp{1}.[exp1] = Some q1{2} /\
   RH.NonOptHashing.mp{1}.[exp2] = Some q2{2} /\
   RH.NonOptHashing.mp{1}.[exp3] = Some q3{2} /\
   DDH_Adv.k1{2} = g ^ q1{2} /\
   DDH_Adv.k2{2} = g ^ q2{2} /\
   DDH_Adv.k3{2} = g ^ q3{2} /\
   ={func, adv, in_guard, MI.func, MI.adv, MI.in_guard,
     DDH_Adv.func, DDH_Adv.adv} /\
   ={self, adv}(KEHybridHashingAdv.KEHybridHash, DDH_Adv.KEDDH) /\
   DDH_Adv.KEDDH.self{2} = MI.func{1} /\
   DDH_Adv.KEDDH.adv{2} = MI.adv{1} /\
   ={glob Adv, glob Env} /\
   KEHybridHashingAdv.KEHybridHash.st{1} = KEHybridStateWaitReq1 /\
   DDH_Adv.KEDDH.st{2} = KEDDHStateWaitReq1).
call (_ : true).
auto.
call
  (_ :
   RH.NonOptHashing.mp{1}.[exp1] = Some (log DDH_Adv.k1{2}) /\
   RH.NonOptHashing.mp{1}.[exp2] = Some (log DDH_Adv.k2{2}) /\
   RH.NonOptHashing.mp{1}.[exp3] = Some (log DDH_Adv.k3{2}) /\
   ={MI.func, MI.adv, MI.in_guard} /\
   ={self, adv}(KEHybridHashingAdv.KEHybridHash, DDH_Adv.KEDDH) /\
   DDH_Adv.KEDDH.self{2} = MI.func{1} /\
   DDH_Adv.KEDDH.adv{2} = MI.adv{1} /\
   ={glob Adv} /\
   hybrid_hash_ddh2_rel
   {|hybrid_hash_ddh2_rel_st_k1 = DDH_Adv.k1{2};
     hybrid_hash_ddh2_rel_st_k2 = DDH_Adv.k2{2};
     hybrid_hash_ddh2_rel_st_k3 = DDH_Adv.k3{2};
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
   RH.NonOptHashing.mp{1}.[exp1] = Some (log DDH_Adv.k1{2}) /\
   RH.NonOptHashing.mp{1}.[exp2] = Some (log DDH_Adv.k2{2}) /\
   RH.NonOptHashing.mp{1}.[exp3] = Some (log DDH_Adv.k3{2}) /\
   ={MI.func, MI.adv, MI.in_guard} /\
   ={self, adv}(KEHybridHashingAdv.KEHybridHash, DDH_Adv.KEDDH) /\
   DDH_Adv.KEDDH.self{2} = MI.func{1} /\
   DDH_Adv.KEDDH.adv{2} = MI.adv{1} /\
   ={glob Adv} /\
   hybrid_hash_ddh2_rel
   {|hybrid_hash_ddh2_rel_st_k1 = DDH_Adv.k1{2};
     hybrid_hash_ddh2_rel_st_k2 = DDH_Adv.k2{2};
     hybrid_hash_ddh2_rel_st_k3 = DDH_Adv.k3{2};
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
by rewrite gen_log.
by rewrite gen_log.
by rewrite gen_log.
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
if; first smt().
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
if; first smt().
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
            (func' adv' : addr, in_guard' : int fset) &m :
  DDH_Adv.func{m} = func' => DDH_Adv.adv{m} = adv' =>
  DDH_Adv.in_guard{m} = in_guard' =>
  Pr[Exper(MI(KEHybrid, Adv), Env).main
       (func', adv', in_guard') @ &m : res] =
  Pr[RH.GOptHashing(KEHybridHashingAdv).main() @ &m : res].
proof.
move => func'_eq adv'_eq in_guard'_eq.
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
   func{1} = MI.func{1} /\ KEHybrid.self{1} = func{1} /\
   adv{1} = MI.adv{1} /\ KEHybrid.adv{1} = adv{1} /\
   KEHybrid.st{1} = KEHybridStateWaitReq1 /\
   RH.OptHashing.mp{2} = empty /\
   ={glob Adv, glob Env}).
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
   exper_pre MI.func{1} MI.adv{1} /\
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
rcondt{1} 5; first auto; smt(Fwd1.dest_good_fw_ok).
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
smt(Fwd1.dest_good_fw_ok).
rcondf{2} 5; first auto.
rcondf{2} 8; first auto.
move => |> &hr dec_sim_wait_eq <- /= [#] -> -> _ _ _ _
        pre [] /= _ [#] _ _ _ _ _ ->>.
rewrite /= oget_some /= in dec_sim_wait_eq.
elim dec_sim_wait_eq => -> _ /negb_or [#].
rewrite not_dir.
progress.
rewrite oget_some /=.
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
   exper_pre MI.func{1} MI.adv{1} /\
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
rcondf{1} 2; first auto; smt(Fwd1.dest_good_fw_ok).
auto; progress; smt().
auto; progress; smt().
auto; progress; smt().
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
if{2}.
rcondf{2} 2; first auto; smt(Fwd1.dest_good_fw_ok).
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
rcondt{2} 4; first auto; smt().
rcondf{2} 5; first auto.
auto; progress; by apply (KEHybridIdealSimRel1 _ pt1' pt2' q1').
qed.

local lemma MI_KEHybrid_KEIdeal_KESim_after_adv_2
            (pt1' pt2' : port, q1' q2' q3' : exp) :
  equiv
  [MI_KEHybrid_AfterAdv.after_adv ~
   MI_KEIdeal_KESim_AfterAdv.after_adv :
   ={r} /\ r{1} <> None /\ ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} /\
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
rcondt{1} 5; first auto; smt(Fwd2.dest_good_fw_ok).
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
smt(Fwd2.dest_good_fw_ok).
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
   exper_pre MI.func{1} MI.adv{1} /\
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
rcondf{1} 2; first auto; smt(Fwd2.dest_good_fw_ok).
auto; progress; smt().
auto; progress; smt().
auto; progress; smt().
rcondt{1} 1; first auto.
rcondf{1} 2; first auto.
if{2}.
rcondf{2} 2; first auto; smt(Fwd2.dest_good_fw_ok).
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
   exper_pre MI.func{1} MI.adv{1} /\
   ! mem MI.in_guard{1} ke_sim_pi /\
   KEHybrid.self{1} = MI.func{1} /\
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
if; first smt().
rcondf{2} 5; first auto.
rcondf{2} 8; first auto.
move => &hr |> <- /= [#] _ -> ->.
rewrite oget_some /=; smt().
rcondf{2} 8; first auto.
rcondf{2} 8; first auto.
move => &hr |> <- /= [#] _ -> ->.
rewrite oget_some /ke_sim_req1 /=; smt(ke_pi_uniq).
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
rcondf{1} 10; first auto; progress; rewrite oget_some /#.
rcondf{1} 10; first auto.
rcondf{1} 10; first auto; progress.
rewrite oget_some /Fwd1.fw_obs /=; smt(ke_pi_uniq).
rcondt{1} 10; first auto.
rcondf{1} 12; first auto; progress; rewrite oget_some /Fwd1.fw_obs /= /#.
rcondf{2} 4; first auto.
rcondt{2} 5; first auto.
rcondf{2} 5; first auto; progress; rewrite oget_some /Fwd1.fw_obs /=.
smt(ke_pi_uniq).
seq 11 4 :
  (not_done{1} /\ not_done{2} /\ not_done0{2} /\
   m0{1} = m4{2} /\
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} /\
   ! mem MI.in_guard{1} ke_sim_pi /\
   KEHybrid.self{1} = MI.func{1} /\
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
   exper_pre MI.func{1} MI.adv{1} /\
   ! mem MI.in_guard{1} ke_sim_pi /\
   KEHybrid.self{1} = MI.func{1} /\
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
   exper_pre MI.func{1} MI.adv{1} /\
   ! mem MI.in_guard{1} ke_sim_pi /\
   KEHybrid.self{1} = MI.func{1} /\
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
          MI.adv{2} MI.func{2} MI.in_guard{2}
          not_done{1} pt12{1} pt22{1} q1{1} r4{2}.
inline MI_KEHybrid_AfterAdv.after_adv.
sim; auto => |>.
transitivity{2}
  {r <- MI_KEIdeal_KESim_AfterAdv.after_adv(r0);}
  (={r0, MI.func, MI.adv, MI.in_guard} /\ r0{1} <> None /\
   exper_pre MI.func{1} MI.adv{1} /\
   ! mem MI.in_guard{1} ke_sim_pi /\
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
          MI.in_guard{2} r4{2}.
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
have /= := ke_pi_uniq; smt().
sp 0 6.
seq 1 1 :
  (not_done{1} /\ not_done{2} /\ r0{1} = r2{2} /\
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} /\
   ! mem MI.in_guard{1} ke_sim_pi /\
   KEHybrid.self{1} = MI.func{1} /\
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
if; first smt().
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
   exper_pre MI.func{1} MI.adv{1} /\
   ! mem MI.in_guard{1} ke_sim_pi /\
   KEHybrid.self{1} = MI.func{1} /\
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
auto => |> &1 &2 <- [#] <- _ _ _ /= _ [#] -> _ _ _ _ _ _ _ _ _ _
        /negb_or [#] _ /not_dir -> _ _ /#.
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
   exper_pre MI.func{1} MI.adv{1} /\
   ! (ke_sim_pi \in MI.in_guard{1}) /\
   KEHybrid.self{1} = MI.func{1} /\
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
have /= := ke_pi_uniq; smt().
sp 0 6.
seq 1 1 :
   (r0{1} = r2{2} /\ not_done{1} /\ not_done{2} /\ not_done0{2} /\
    ={MI.func, MI.adv, MI.in_guard} /\
    exper_pre MI.func{1} MI.adv{1} /\
    ! (ke_sim_pi \in MI.in_guard{1}) /\
    KEHybrid.self{1} = MI.func{1} /\
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
   exper_pre MI.func{1} MI.adv{1} /\
   ! (ke_sim_pi \in MI.in_guard{1}) /\
   KEHybrid.self{1} = MI.func{1} /\
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
          MI.adv{2} MI.func{2} MI.in_guard{2}
          not_done{1} r2{2}.
inline MI_KEHybrid_AfterAdv.after_adv.
sim; auto => |>.
transitivity{2}
  {r <- MI_KEIdeal_KESim_AfterAdv.after_adv(r2);}
  (r0{1} = r2{2} /\ r0{1} <> None /\
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} /\
   ! (ke_sim_pi \in MI.in_guard{1}) /\
   KEHybrid.self{1} = MI.func{1} /\
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
          MI.in_guard{2} r2{2}.
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
rewrite oget_some /= /Fwd2.fw_obs /=; smt(ke_pi_uniq).
sp 0 12.
rcondf{1} 6; first auto.
rcondf{1} 9; first auto; progress; rewrite oget_some /Fwd2.fw_obs /= /#.
rcondf{1} 9; first auto.
rcondf{1} 9; first auto; progress.
rewrite oget_some /Fwd2.fw_obs /=; smt(ke_pi_uniq).
rcondt{1} 9; first auto.
rcondf{1} 11; first auto; progress; rewrite oget_some /Fwd2.fw_obs /= /#.
sp 10 0.
conseq
  (_ :
   m0{1} = m4{2} /\ not_done{1} /\ not_done{2} /\
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} /\
   ! (ke_sim_pi \in MI.in_guard{1}) /\
   KEHybrid.self{1} = MI.func{1} /\
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
move => ^H <- [#] <<- <<- <<- <<- st_R; move : H.
rewrite /Fwd2.fw_obs /=.
move => [#] -> -> -> -> -> dec_sim_wait_eq _ st_R0
        _ _ _ dec_ideal_wait_eq dec_ke_req_eq pre _ _ _ _
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
   exper_pre MI.func{1} MI.adv{1} /\
   ! (ke_sim_pi \in MI.in_guard{1}) /\
   KEHybrid.self{1} = MI.func{1} /\
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
   exper_pre MI.func{1} MI.adv{1} /\
   ! (ke_sim_pi \in MI.in_guard{1}) /\
   KEHybrid.self{1} = MI.func{1} /\
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
          MI.adv{2} MI.func{2} MI.in_guard{2}
          not_done{1} r4{2}.
inline MI_KEHybrid_AfterAdv.after_adv.
sim; auto => |>.
transitivity{2}
  {r <- MI_KEIdeal_KESim_AfterAdv.after_adv(r0);}
  (={r0, MI.func, MI.adv, MI.in_guard} /\ r0{1} <> None /\
   exper_pre MI.func{1} MI.adv{1} /\
   ! (ke_sim_pi \in MI.in_guard{1}) /\
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
          MI.in_guard{2} r4{2}.
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
   exper_pre MI.func{1} MI.adv{1} /\
   ! (ke_sim_pi \in MI.in_guard{1}) /\
   KEHybrid.self{1} = MI.func{1} /\
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
if; first smt().
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
move => |> &hr <- /= [#] -> -> _ _ _ _ _ _ _ _ _
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
        _ _ [] /= _ [#] _ _ _ _ _ -> /=.
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
   exper_pre MI.func{1} MI.adv{1} /\
   ! (ke_sim_pi \in MI.in_guard{1}) /\
   KEHybrid.self{1} = MI.func{1} /\
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
    exper_pre MI.func{1} MI.adv{1} /\
   ! (ke_sim_pi \in MI.in_guard{1}) /\
   KEHybrid.self{1} = MI.func{1} /\
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
   exper_pre MI.func{1} MI.adv{1} /\
   ! (ke_sim_pi \in MI.in_guard{1}) /\
   KEHybrid.self{1} = MI.func{1} /\
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
          MI.adv{2} MI.func{2} MI.in_guard{2}
          not_done{1} r2{2}.
inline MI_KEHybrid_AfterAdv.after_adv.
sim; auto => |>.
transitivity{2}
  {r <- MI_KEIdeal_KESim_AfterAdv.after_adv(r2);}
  (r0{1} = r2{2} /\ r0{1} <> None /\
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} /\
   ! (ke_sim_pi \in MI.in_guard{1}) /\
   KEHybrid.self{1} = MI.func{1} /\
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
          MI.in_guard{2} r2{2}.
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
   exper_pre MI.func{1} MI.adv{1} /\
   ! (ke_sim_pi \in MI.in_guard{1}) /\
   KEHybrid.self{1} = MI.func{1} /\
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
   exper_pre MI.func{1} MI.adv{1} /\
   ={MI.func, MI.adv, MI.in_guard} /\
   ! (ke_sim_pi \in MI.in_guard{1}) /\
   KEHybrid.self{1} = MI.func{1} /\
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
if; first smt().
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
if; first smt().
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
   exper_pre MI.func{1} MI.adv{1} /\
   ={MI.func, MI.adv, MI.in_guard} /\
   ! (ke_sim_pi \in MI.in_guard{1}) /\
   KEHybrid.self{1} = MI.func{1} /\
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

local lemma Exper_KEHybrid_KEIdeal_KESim
            (func' adv' : addr, in_guard' : int fset) &m :
  exper_pre func' adv' => ! (ke_sim_pi \in in_guard') =>
  Pr[Exper(MI(KEHybrid, Adv), Env).main
       (func', adv', in_guard') @ &m : res] =
  Pr[Exper(MI(KEIdeal, KESim(Adv)), Env).main
       (func', adv', in_guard') @ &m : res].
proof.
move => pre not_in_guard'.
byequiv => //.
proc.
inline MI(KEHybrid, Adv).init MI(KEIdeal, KESim(Adv)).init
       KEHybrid.init KEIdeal.init KESim(Adv).init.
seq 12 17 :
  (={func, adv, in_guard, MI.func, MI.adv, MI.in_guard} /\
   func{1} = MI.func{1} /\ adv{1} = MI.adv{1} /\
   in_guard{1} = MI.in_guard{1} /\
   exper_pre MI.func{1} MI.adv{1} /\
   ! (ke_sim_pi \in MI.in_guard{1}) /\
   KEHybrid.self{1} = MI.func{1} /\ KEHybrid.adv{1} = MI.adv{1} /\
   KEIdeal.self{2} = MI.func{1} /\ KEIdeal.adv{2} = MI.adv{1} /\
   KESim.self{2} = MI.adv{1} /\ KESim.adv{2} = [] /\
   ={glob Adv, glob Env} /\
   KEHybrid.st{1} = KEHybridStateWaitReq1 /\
   KEIdeal.st{2} = KEIdealStateWaitReq1 /\
   KESim.st{2} = KESimStateWaitReq1).
swap{2} 16 1.
call (_ : true).
auto.
call
  (_ :
   ={MI.func, MI.adv, MI.in_guard} /\
   exper_pre MI.func{1} MI.adv{1} /\
   ! (ke_sim_pi \in MI.in_guard{1}) /\
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

lemma ke_sec (func' adv' : addr, in_guard' : int fset) &m :
  exper_pre func' adv' => ! (ke_sim_pi \in in_guard') =>
  DDH_Adv.func{m} = func' => DDH_Adv.adv{m} = adv' =>
  DDH_Adv.in_guard{m} = in_guard' =>
  `|Pr[Exper(MI(KEReal, Adv), Env).main
         (func', adv', in_guard') @ &m : res] -
    Pr[Exper(MI(KEIdeal, KESim(Adv)), Env).main
         (func', adv', in_guard') @ &m : res]| <=
  `|Pr[DDH1(DDH_Adv(Env, Adv)).main() @ &m : res] -
    Pr[DDH2(DDH_Adv(Env, Adv)).main() @ &m : res]|.
proof.
move => pre not_in_guard' func'_eq adv'_eq in_guard'_eq.
by rewrite (Exper_KEReal_KERealSimp Adv Env func' adv' in_guard' &m) 1:/#
           (Exper_KERealSimp_GOptHashing_KERealSimpHashingAdv
            func' adv' in_guard' &m) //
           -(RH.GNonOptHashing_GOptHashing KERealSimpHashingAdv &m)
           (KERealSimpHashingAdv_NonOptHashing_DDH1_DDH_Adv
            func' adv' in_guard' &m) //
           -(Exper_KEHybrid_KEIdeal_KESim func' adv' in_guard' &m) //
           (Exper_KEHybrid_KEHybridHashingAdv_OptHashing func' adv' in_guard'
            &m) //
           -(RH.GNonOptHashing_GOptHashing KEHybridHashingAdv &m) //
           -(KEHybridHashingAdv_NonOptHashing_DDH2_DDH_Adv
             func' adv' in_guard' &m).
qed.

end section.

lemma ke_security
      (Adv <: FUNC{MI, KEReal, KEIdeal, KESim, DDH_Adv})
      (Env <: ENV{Adv, MI, KEReal, KEIdeal, KESim, DDH_Adv})
      (func' adv' : addr, in_guard' : int fset) &m :
  exper_pre func' adv' => ! (ke_sim_pi \in in_guard') =>
  (* parameters for modules in upper bound: *)
  DDH_Adv.func{m} = func' => DDH_Adv.adv{m} = adv' =>
  DDH_Adv.in_guard{m} = in_guard' =>
  (* end of parameters for modules in upper bound *)
  `|Pr[Exper(MI(KEReal, Adv), Env).main
         (func', adv', in_guard') @ &m : res] -
    Pr[Exper(MI(KEIdeal, KESim(Adv)), Env).main
         (func', adv', in_guard') @ &m : res]| <=
  `|Pr[DDH1(DDH_Adv(Env, Adv)).main() @ &m : res] -
    Pr[DDH2(DDH_Adv(Env, Adv)).main() @ &m : res]|.
proof.
move => pre func'_eq adv'_eq in_guard'_eq.
by apply (ke_sec Adv Env func' adv' in_guard' &m).
qed.
