(* SMC.ec *)

prover ["!"].  (* no provers *)

require import AllCore List FSet Distr ListPO.
require DDH UCCore.

(************************** Bitstrings and Exponents **************************)

(* we minimally axiomatize two types and related operators

   a type bits of bitstrings of length n, equipped with an all zero
   element (zero), a bitwise exclusive or operator (^^) satisfying
   the usual axioms, and a generator g (see below)

   a type exp of exponents equipped with an element e (about which
   nothing is assumed), a commutative multiplication operator ( * ),
   and a lossless distribution dexp in which every exponent's value is
   1%r / (2 ^ n)%r (so the size of exp is 2 ^ n)

   bits and exp are connected via an exponentiation operator (^) of
   type bits -> exp -> bits with the property that every element of
   bits is uniquely generated using exponentiation from g

   consequently there is a bijection between bits and exp: from exp
   to bits the function is (fun q => g ^ q); from bits to exp, the
   function is the discrete logarithm *)

op n : {int | 0 <= n} as ge0_n.  (* length of bitstrings *)

type bits.  (* bitstrings *)

op zero : bits.  (* the all zero bitstring *)

op (^^) : bits -> bits -> bits.  (* pointwise exclusive or *)

axiom xorC (x y : bits) : x ^^ y = y ^^ x.

axiom xorA (x y z : bits) : x ^^ y ^^ z = x ^^ (y ^^ z).

axiom xor0_ (x : bits) : zero ^^ x = x.

axiom xor_0 (x : bits) : x ^^ zero = x.

axiom xorK (x : bits) : x ^^ x = zero.

type exp.  (* exponents *)

op e : exp.  (* some exponent *)

op ( * ) : exp -> exp -> exp.  (* exponent multiplication *)

axiom mulC (q r : exp) : q * r = r * q.

(* distribution over exp *)

op dexp : exp distr.

(* every exponent q has the same value in dexp: 1%r / (2 ^ n)%r;
   consequently, dexp's support is all of exp, i.e., dexp is
   full as well as uniform *)

axiom dexp1E (q : exp) : mu1 dexp q = 1%r / (2 ^ n)%r.

(* because dexp is also lossless (the sum of the values in dexp of all
   exponents is 1%r), this tells us that the size of exp is 2 ^ n *)

axiom dexp_ll : is_lossless dexp.

op g : bits.  (* generator *)

op (^) : bits -> exp -> bits.  (* exponentiation *)

(* the following axioms say that each bits is uniquely generated from g
   by exponentiation *)

axiom gen_surj (x : bits) : exists (q : exp), x = g ^ q.

axiom gen_inj (q r : exp) : g ^ q = g ^ r => q = r.

(* consequences of axioms *)

(* dexp is indeed full and uniform *)

lemma dexp_uni : is_uniform dexp.
proof.
move => x y _ _; by rewrite 2!dexp1E.
qed.

lemma dexp_fu : is_full dexp.
proof.
move => x.
rewrite /support dexp1E.
by rewrite StdRing.RField.div1r StdOrder.RealOrder.invr_gt0
           lt_fromint powPos.
qed.

(* we can define a bijection between exp and bits *)

op gen (q : exp) : bits = g ^ q.

op gen_rel (x : bits) (q : exp) : bool = x = g ^ q.

op log (x : bits) : exp = choiceb (gen_rel x) e.

lemma log_gen (q : exp) : log (gen q) = q.
proof.
rewrite /gen /log.
have choice_g2q := choicebP (gen_rel (g ^ q)) e.
have /choice_g2q @/gen_rel /gen_inj {2}-> // :
  exists (q' : exp), gen_rel (g ^ q) q'
  by rewrite /gen_rel; by exists q.
qed.

lemma gen_log (x : bits) : gen (log x) = x.
proof.
rewrite /gen /log.
have @/gen_rel <- // := choicebP (gen_rel x) e.
rewrite gen_surj.
qed.

(******************** Decisional Diffie-Hellman Assumption ********************)

clone import DDH as DDH' with
  type exp <- exp,
  op e <- e,
  op ( * ) <- ( * ),
  type key <- bits,
  op g <- g,
  op (^) <- (^),
  op dexp <- dexp
proof *.
realize mulC. apply mulC. qed.
realize dexp_fu. apply dexp_fu. qed.
realize dexp_uni. apply dexp_uni. qed.
realize dexp_ll. apply dexp_ll. qed.
realize gen_surj. apply gen_surj. qed.
realize gen_inj. apply gen_inj. qed.

(********************* Clone UCCore with Needed Base Type *********************)

type base = [
    BaseExp of exp
  | BaseBits of bits
].

op dec_base_exp (bse : base) : exp option =
     with bse = BaseExp q  => Some q
     with bse = BaseBits _ => None.

lemma enc_dec_base_exp (q : exp) :
  dec_base_exp (BaseExp q) = Some q.
proof. done. qed.

op is_base_exp (bse : base) : bool =
     dec_base_exp bse <> None.

lemma is_base_exp (q : exp) :
  is_base_exp (BaseExp q).
proof. done. qed.

op dec_base_bits (bse : base) : bits option =
     with bse = BaseExp _  => None
     with bse = BaseBits x => Some x.

lemma enc_dec_base_bits (x : bits) :
  dec_base_bits (BaseBits x) = Some x.
proof. done. qed.

op is_base_bits (bse : base) : bool =
     dec_base_bits bse <> None.

lemma is_base_bits (x : bits) :
  is_base_bits (BaseBits x).
proof. done. qed.

clone import UCCore as UCCore' with
  type base <- base
proof *.
(* nothing to realize *)

(************************** Forwarding Functionality **************************)

theory Forward.

(* theory parameters *)

(* port index of adversary that functionality communicates with *)

op adv_pi : int.

axiom fwd_pi_uniq : uniq [adv_pi; 0].

(* end theory parameters *)

(* request sent to port 1 of forwarding functionality: pt1 is asking
   to forward u to pt2 *)

op fw_req (func : addr, pt1 pt2 : port, u : univ) : msg =
     (Dir, (func, 1), pt1, UnivPair (UnivPort pt2, u)).

op dec_fw_req (m : msg) : (addr * port * port * univ) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Adv \/ pt1.`2 <> 1 \/ ! is_univ_pair v) ?
        None :
        let (v1, v2) = oget (dec_univ_pair v)
        in (! is_univ_port v1) ?
           None :
           Some (pt1.`1, pt2, oget(dec_univ_port v1), v2).

lemma enc_dec_fw_req (func : addr, pt1 pt2 : port, u : univ) :
  dec_fw_req (fw_req func pt1 pt2 u) = Some (func, pt1, pt2, u).
proof. done. qed.

op is_fw_req (m : msg) : bool =
     dec_fw_req m <> None.

lemma is_fw_req (func : addr, pt1 pt2 : port, u : univ) :
  is_fw_req (fw_req func pt1 pt2 u).
proof. done. qed.

(* response sent from port 1 of forwarding functionality to pt2,
   completing the forwarding of u that was requested by pt1 *)

op fw_rsp (func : addr, pt1 pt2 : port, u : univ) : msg =
     (Dir, pt2, (func, 1), UnivPair (UnivPort pt1, u)).

op dec_fw_rsp (m : msg) : (addr * port * port * univ) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Adv \/ pt2.`2 <> 1 \/ ! is_univ_pair v) ?
        None :
        let (v1, v2) = oget (dec_univ_pair v)
        in (! is_univ_port v1) ?
           None :
           Some (pt2.`1, oget(dec_univ_port v1), pt1, v2).

lemma enc_dec_fw_rsp (func : addr, pt1 pt2 : port, u : univ) :
  dec_fw_rsp (fw_rsp func pt1 pt2 u) = Some (func, pt1, pt2, u).
proof. done. qed.

op is_fw_rsp (m : msg) : bool =
     dec_fw_rsp m <> None.

lemma is_fw_rsp (func : addr, pt1 pt2 : port, u : univ) :
  is_fw_rsp (fw_rsp func pt1 pt2 u).
proof. done. qed.

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
                 oget(dec_univ_port v1),
                 oget(dec_univ_port v2),
                 v3).

lemma enc_dec_fw_obs (func adv : addr, pt1 pt2 : port, u : univ) :
  dec_fw_obs (fw_obs func adv pt1 pt2 u) = Some (func, adv, pt1, pt2, u).
proof.
by rewrite /fw_obs /dec_fw_obs /=
   (is_univ_triple (UnivPort pt2) (UnivPort pt2) u) /=
    enc_dec_univ_triple.
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

op is_fw_ok (m : msg) : bool =
     dec_fw_ok m <> None.

lemma is_fw_ok (func adv : addr) :
  is_fw_ok (fw_ok func adv).
proof. done. qed.

type fw_state = [
    FwStateInit
  | FwStateWait of (port * port * univ)
  | FwStateFinal
].

op dec_fw_state_wait (st : fw_state) : (port * port * univ) option =
     with st = FwStateInit   => None
     with st = FwStateWait t => Some t
     with st = FwStateFinal  => None.

lemma enc_dec_fw_state_wait (t : port * port * univ) :
  dec_fw_state_wait (FwStateWait t) = Some t.
proof. done. qed.

op is_fw_state_wait (st : fw_state) : bool =
  dec_fw_state_wait st <> None.

lemma is_fw_state_wait (t : port * port * univ) :
  is_fw_state_wait (FwStateWait t).
proof. done. qed.

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
    if (st = FwStateInit) {
      if (is_fw_req m) {
        (addr1, pt1, pt2, u) <- oget(dec_fw_req m);
        if (self = addr1 /\ ! self <= pt2.`1 /\ ! self <= pt2.`1) {
          r <- Some (fw_obs self adv pt1 pt2 u);
          st <- FwStateWait (pt1, pt2, u);
        }
      }
    }
    elif (is_fw_state_wait st) {
      (pt1, pt2, u) <- oget (dec_fw_state_wait st);
      if (is_fw_ok m) {
        (addr1, addr2) <- oget (dec_fw_ok m);
        if (addr1 = self) {
          (pt1, pt2, u) <- oget (dec_fw_state_wait st);
          r <- Some (fw_rsp self pt1 pt2 u);
          st <- FwStateFinal;
        }
      }
    }
    return r;
  }
}.

end Forward.

theory KeyExchange.

(* theory parameters *)

(* port index of adversary that key exchange functionalities
   communicate with *)

op adv_fw_pi : int.

(* port index of adversary that simulator communicates with *)

op ke_sim_adv_pi : int.

axiom ke_pi_uniq : uniq [ke_sim_adv_pi; adv_fw_pi; 0].

(* end theory parameters *)

(* request sent to port 1 of key exchange functionality: pt1 wants to
   exchange a key with pt2 *)

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

(* response sent from port 2 of key exchange functionality to pt2,
   completing first phase of key exchange initiated by pt1 *)

op ke_rsp1 (func : addr, pt1 pt2 : port, x : bits) : msg =
     (Dir, pt2, (func, 2), UnivPair (UnivPort pt1, UnivBase (BaseBits x))).

op dec_ke_rsp1 (m : msg) : (addr * port * port * bits) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Adv \/ pt2.`2 <> 2 \/ ! is_univ_pair v) ?
        None :
        let (v1, v2) = oget (dec_univ_pair v)
        in (! is_univ_port v1 \/ ! is_univ_base v2) ?
           None :
           let b = oget (dec_univ_base v2)
           in (! is_base_bits b) ?
              None :
              Some (pt2.`1, oget(dec_univ_port v1), pt1, oget (dec_base_bits b)).

lemma enc_dec_ke_rsp1 (func : addr, pt1 pt2 : port, x : bits) :
  dec_ke_rsp1 (ke_rsp1 func pt1 pt2 x) = Some (func, pt1, pt2, x).
proof.
by rewrite /ke_rsp1 /dec_ke_rsp1 /=
           (is_univ_pair (UnivPort pt1, UnivBase (BaseBits x))) /=
           oget_some /= (is_univ_port pt1) /= oget_some.
qed.

op is_ke_rsp1 (m : msg) : bool =
     dec_ke_rsp1 m <> None.

lemma is_ke_rsp1 (func : addr, pt1 pt2 : port, x : bits) :
  is_ke_rsp1 (ke_rsp1 func pt1 pt2 x).
proof.
by rewrite /is_ke_rsp1 enc_dec_ke_rsp1.
qed.

(* request sent to port 2 of key exchange functionality by pt2 to
   initiate phase 2 of key exchange with party 1 *)

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

(* response sent from port 1 of key exchange functionality to pt1,
   completing second phase of key exchange with Party 2 initiated by
   itself *)

op ke_rsp2 (func : addr, pt1 : port, x : bits) : msg =
     (Dir, pt1, (func, 1), UnivBase (BaseBits x)).

op dec_ke_rsp2 (m : msg) : (addr * port * bits) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Adv \/ pt2.`2 <> 1 \/ ! is_univ_base v) ?
        None :
        let bse = oget (dec_univ_base v)
        in (! is_base_bits bse) ?
           None :
           Some (pt2.`1, pt1, oget (dec_base_bits bse)).

lemma enc_dec_ke_rsp2 (func : addr, pt1 : port, x : bits) :
  dec_ke_rsp2 (ke_rsp2 func pt1 x) = Some (func, pt1, x).
proof.
by rewrite /ke_rsp2 /dec_ke_rsp2 /= (is_univ_base (BaseBits x)) /=
           oget_some (is_base_bits x).
qed.

op is_ke_rsp2 (m : msg) : bool =
     dec_ke_rsp2 m <> None.

lemma is_ke_rsp2 (func : addr, pt1 : port, x : bits) :
  is_ke_rsp2 (ke_rsp2 func pt1 x).
proof.
by rewrite /is_ke_rsp2 enc_dec_ke_rsp2.
qed.

clone Forward as Fwd1
  with op adv_pi <- adv_fw_pi
proof *.
realize fwd_pi_uniq. by have := ke_pi_uniq. qed.

clone Forward as Fwd2
  with op adv_pi <- adv_fw_pi
proof *.
realize fwd_pi_uniq. by have := ke_pi_uniq. qed.

type ke_real_state = [
    KERealStateWaitReq1
  | KERealStateWaitFwd1 of (port * port)
  | KERealStateWaitReq2 of (port * port)
  | KERealStateWaitFwd2 of (port * port)
  | KERealStateFinal
].

op dec_ke_real_state_wait_fwd1 (st : ke_real_state) : (port * port) option =
     with st = KERealStateWaitReq1   => None
     with st = KERealStateWaitFwd1 p => Some p
     with st = KERealStateWaitReq2 _ => None
     with st = KERealStateWaitFwd2 _ => None
     with st = KERealStateFinal      => None.

lemma enc_dec_ke_real_state_wait_fwd1 (p : port * port) :
  dec_ke_real_state_wait_fwd1 (KERealStateWaitFwd1 p) = Some p.
proof. done. qed.

op is_ke_real_state_wait_fwd1 (st : ke_real_state) : bool =
  dec_ke_real_state_wait_fwd1 st <> None.

lemma is_ke_real_state_wait_fwd1 (p : port * port) :
  is_ke_real_state_wait_fwd1 (KERealStateWaitFwd1 p).
proof. done. qed.

op dec_ke_real_state_wait_req2 (st : ke_real_state) : (port * port) option =
     with st = KERealStateWaitReq1   => None
     with st = KERealStateWaitFwd1 _ => None
     with st = KERealStateWaitReq2 p => Some p
     with st = KERealStateWaitFwd2 _ => None
     with st = KERealStateFinal      => None.

lemma enc_dec_ke_real_state_wait_req2 (p : port * port) :
  dec_ke_real_state_wait_req2 (KERealStateWaitReq2 p) = Some p.
proof. done. qed.

op is_ke_real_state_wait_req2 (st : ke_real_state) : bool =
  dec_ke_real_state_wait_req2 st <> None.

lemma is_ke_real_state_wait_req2 (p : port * port) :
  is_ke_real_state_wait_req2 (KERealStateWaitReq2 p).
proof. done. qed.

op dec_ke_real_state_wait_fwd2 (st : ke_real_state) : (port * port) option =
     with st = KERealStateWaitReq1   => None
     with st = KERealStateWaitFwd1 _ => None
     with st = KERealStateWaitReq2 _ => None
     with st = KERealStateWaitFwd2 p => Some p
     with st = KERealStateFinal      => None.

lemma enc_dec_ke_real_state_wait_fwd2 (p : port * port) :
  dec_ke_real_state_wait_fwd2 (KERealStateWaitFwd2 p) = Some p.
proof. done. qed.

op is_ke_real_state_wait_fwd2 (st : ke_real_state) : bool =
  dec_ke_real_state_wait_fwd2 st <> None.

lemma is_ke_real_state_wait_fwd2 (p : port * port) :
  is_ke_real_state_wait_fwd2 (KERealStateWaitFwd2 p).
proof. done. qed.

module KEReal : FUNC = {
  var self, adv : addr
  var q1, q2 : exp
  var st : ke_real_state

  proc init(self_ adv_ : addr) : unit = {
    self <- self_; adv <- adv_;
    Fwd1.Forw.init(self ++ [1], adv); Fwd2.Forw.init(self ++ [2], adv);
    q1 <$ dexp; q2 <$ dexp;
    st <- KERealStateWaitReq1;
  }

  proc parties(m : msg) : msg option = {
    var pt1, pt2, pt1', pt2' : port; var addr : addr;
    var u : univ; var b1, b2 : base; var x1, x2 : bits;
    var r : msg option <- None;
    if (st = KERealStateWaitReq1) {  (* P1 can respond *)
      if (is_ke_req1 m) {
        (addr, pt1, pt2) <- oget (dec_ke_req1 m);
        if (! self <= pt1.`1 /\ ! self <= pt2.`1) {
          r <-
            Some (Fwd1.fw_req (self ++ [1]) (self, 1) (self, 2)
                              (UnivBase (BaseBits (g ^ q1))));
          st <- KERealStateWaitFwd1(pt1, pt2);
        }
      }
    }
    elif (is_ke_real_state_wait_fwd1 st) {  (* P2 can respond *)
      (pt1, pt2) <- oget (dec_ke_real_state_wait_fwd1 st);
      if (Fwd1.is_fw_rsp m) {
        (addr, pt1', pt2', u) <- oget (Fwd1.dec_fw_rsp m);
        if (addr = self ++ [1]) {
          b1 <- oget (dec_univ_base (oget (dec_univ_pair u)).`2);
          x1 <- oget (dec_base_bits b1);
          r <- Some (ke_rsp1 self pt1 pt2 (x1 ^ q2));
          st <- KERealStateWaitReq2(pt1, pt2);
        }
      }
    }
    elif (is_ke_real_state_wait_req2 st) {  (* P2 can respond *)
      (pt1, pt2) <- oget (dec_ke_real_state_wait_req2 st);
      if (is_ke_req2 m) {
        (addr, pt2') <- oget (dec_ke_req2 m);
        if (pt2' = pt2) {
          r <-
            Some (Fwd2.fw_req (self ++ [2]) (self, 2) (self, 1)
                              (UnivBase (BaseBits (g ^ q2))));
          st <- KERealStateWaitFwd2(pt1, pt2);
        }
      }
    }
    elif (is_ke_real_state_wait_fwd2 st) {  (* P1 can respond *)
      (pt1, pt2) <- oget (dec_ke_real_state_wait_fwd2 st);
      if (Fwd2.is_fw_rsp m) {
        (addr, pt1', pt2', u) <- oget (Fwd2.dec_fw_rsp m);
        if (addr = self ++ [2]) {
          b2 <- oget (dec_univ_base (oget (dec_univ_pair u)).`2);
          x2 <- oget (dec_base_bits b2);
          r <- Some (ke_rsp2 self pt1 (x2 ^ q1));
          st <- KERealStateFinal;
        }
      }
    }
    else {  (* st = KERealStateFinal *)
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
    var addr1, addr2 : addr; var n1, n2 : int;
    var r : msg option <- None;
    (mod, pt1, pt2, u) <- m;
    (addr1, n1) <- pt1; (addr2, n2) <- pt2;
    if ((mod = Dir /\ addr1 = self) \/
        (mod = Adv /\ (self ++ [1] <= addr1 \/ self ++ [2] <= addr1))) {
      r <- loop(m);
    }
    return r;
  }
}.

(* request sent from port 1 of key exchange ideal functionality to
   port ke_sim_adv_pi of key exchange simulator, initiating first phase
   of execution of simulator *)

op ke_sim_req1 (ideal adv : addr) : msg =
     (Adv, (adv, ke_sim_adv_pi), (ideal, 1), UnivUnit).

op dec_ke_sim_req1 (m : msg) : (addr * addr) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Dir \/ pt1.`2 <> ke_sim_adv_pi \/ pt2.`2 <> 1 \/
         ! v = UnivUnit) ?
        None :
        Some (pt2.`1, pt1.`1).

lemma enc_dec_ke_sim_req1 (ideal adv : addr) :
  dec_ke_sim_req1 (ke_sim_req1 ideal adv) = Some (ideal, adv).
proof. done. qed.

op is_ke_sim_req1 (m : msg) : bool =
     dec_ke_sim_req1 m <> None.

lemma is_ke_sim_req1 (ideal adv : addr) :
  is_ke_sim_req1 (ke_sim_req1 ideal adv).
proof. done. qed.

(* response sent from port ke_sim_adv_pi of key exchange simulator to
   port 2 of key exchange ideal functionality, completing first
   phase of simulator execution *)

op ke_sim_rsp1 (ideal adv : addr) : msg =
     (Adv, (ideal, 2), (adv, ke_sim_adv_pi), UnivUnit).

op dec_ke_sim_rsp1 (m : msg) : (addr * addr) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Dir \/ pt1.`2 <> 2 \/ pt2.`2 <> ke_sim_adv_pi \/
         ! v = UnivUnit) ?
        None :
        Some (pt1.`1, pt2.`1).

lemma enc_dec_ke_sim_rsp1 (ideal adv : addr) :
  dec_ke_sim_rsp1 (ke_sim_rsp1 ideal adv) = Some (ideal, adv).
proof. done. qed.

op is_ke_sim_rsp1 (m : msg) : bool =
     dec_ke_sim_rsp1 m <> None.

lemma is_ke_sim_rsp1 (ideal adv : addr) :
  is_ke_sim_rsp1 (ke_sim_rsp1 ideal adv).
proof. done. qed.

(* request sent from port 2 of key exchange ideal functionality to
   port ke_sim_adv_pi of key exchange simulator, initiating second phase
   of execution of simulator *)

op ke_sim_req2 (ideal adv : addr) : msg =
     (Adv, (adv, ke_sim_adv_pi), (ideal, 2), UnivUnit).

op dec_ke_sim_req2 (m : msg) : (addr * addr) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Dir \/ pt1.`2 <> ke_sim_adv_pi \/ pt2.`2 <> 2 \/
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

(* response sent from port ke_sim_adv_pi of key exchange simulator to
   port 1 of key exchange ideal functionality, completing second
   phase of simulator execution *)

op ke_sim_rsp2 (ideal adv : addr) : msg =
     (Adv, (ideal, 1), (adv, ke_sim_adv_pi), UnivUnit).

op dec_ke_sim_rsp2 (m : msg) : (addr * addr) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Dir \/ pt1.`2 <> 1 \/ pt2.`2 <> ke_sim_adv_pi \/
         ! v = UnivUnit) ?
        None :
        Some (pt1.`1, pt2.`1).

lemma enc_dec_ke_sim_rsp2 (ideal adv : addr) :
  dec_ke_sim_rsp2 (ke_sim_rsp2 ideal adv) = Some (ideal, adv).
proof. done. qed.

op is_ke_sim_rsp2 (m : msg) : bool =
     dec_ke_sim_rsp2 m <> None.

lemma is_ke_sim_rsp2 (ideal adv : addr) :
  is_ke_sim_rsp2 (ke_sim_rsp2 ideal adv).
proof. done. qed.

type ke_ideal_state = [
    KEIdealStateWaitReq1
  | KEIdealStateWaitSim1 of (port * port)
  | KEIdealStateWaitReq2 of (port * port)
  | KEIdealStateWaitSim2 of (port * port)
  | KEIdealStateFinal
].

op dec_ke_ideal_state_wait_sim1 (st : ke_ideal_state) : (port * port) option =
     with st = KEIdealStateWaitReq1   => None
     with st = KEIdealStateWaitSim1 p => Some p
     with st = KEIdealStateWaitReq2 _ => None
     with st = KEIdealStateWaitSim2 _ => None
     with st = KEIdealStateFinal      => None.

lemma enc_dec_ke_ideal_state_wait_sim1 (p : port * port) :
  dec_ke_ideal_state_wait_sim1 (KEIdealStateWaitSim1 p) = Some p.
proof. done. qed.

op is_ke_ideal_state_wait_sim1 (st : ke_ideal_state) : bool =
  dec_ke_ideal_state_wait_sim1 st <> None.

lemma is_ke_ideal_state_wait_sim1 (p : port * port) :
  is_ke_ideal_state_wait_sim1 (KEIdealStateWaitSim1 p).
proof. done. qed.

op dec_ke_ideal_state_wait_req2 (st : ke_ideal_state) : (port * port) option =
     with st = KEIdealStateWaitReq1   => None
     with st = KEIdealStateWaitSim1 _ => None
     with st = KEIdealStateWaitReq2 p => Some p
     with st = KEIdealStateWaitSim2 _ => None
     with st = KEIdealStateFinal      => None.

lemma enc_dec_ke_ideal_state_wait_req2 (p : port * port) :
  dec_ke_ideal_state_wait_req2 (KEIdealStateWaitReq2 p) = Some p.
proof. done. qed.

op is_ke_ideal_state_wait_req2 (st : ke_ideal_state) : bool =
  dec_ke_ideal_state_wait_req2 st <> None.

lemma is_ke_ideal_state_wait_req2 (p : port * port) :
  is_ke_ideal_state_wait_req2 (KEIdealStateWaitReq2 p).
proof. done. qed.

op dec_ke_ideal_state_wait_sim2 (st : ke_ideal_state) : (port * port) option =
     with st = KEIdealStateWaitReq1   => None
     with st = KEIdealStateWaitSim1 _ => None
     with st = KEIdealStateWaitReq2 _ => None
     with st = KEIdealStateWaitSim2 p => Some p
     with st = KEIdealStateFinal      => None.

lemma enc_dec_ke_ideal_state_wait_sim2 (p : port * port) :
  dec_ke_ideal_state_wait_sim2 (KEIdealStateWaitSim2 p) = Some p.
proof. done. qed.

op is_ke_ideal_state_wait_sim2 (st : ke_ideal_state) : bool =
  dec_ke_ideal_state_wait_sim2 st <> None.

lemma is_ke_ideal_state_wait_sim2 (p : port * port) :
  is_ke_ideal_state_wait_sim2 (KEIdealStateWaitSim2 p).
proof. done. qed.

module KEIdeal : FUNC = {
  var self, adv : addr
  var q : exp
  var st : ke_ideal_state

  proc init(self_ adv_ : addr) : unit = {
    self <- self_; adv <- adv_;
    q <$ dexp;
    st <- KEIdealStateWaitReq1;
  }

  proc parties(m : msg) : msg option = {
    var pt1, pt2, pt2' : port; var addr1, addr2 : addr;
    var r : msg option <- None;
    if (st = KEIdealStateWaitReq1) {  (* P1 can respond *)
      if (is_ke_req1 m) {
        (addr1, pt1, pt2) <- oget (dec_ke_req1 m);
        if (! self <= pt1.`1 /\ ! self <= pt2.`1) {
          r <- Some (ke_sim_req1 self adv);
          st <- KEIdealStateWaitSim1(pt1, pt2);
        }
      }
    }
    elif (is_ke_ideal_state_wait_sim1 st) {  (* P2 can respond *)
      (pt1, pt2) <- oget (dec_ke_ideal_state_wait_sim1 st);
      if (is_ke_sim_rsp1 m) {
        (addr1, addr2) <- oget (dec_ke_sim_rsp1 m);
        r <- Some (ke_rsp1 self pt1 pt2 (g ^ q));
        st <- KEIdealStateWaitReq2(pt1, pt2);
      }
    }
    elif (is_ke_ideal_state_wait_req2 st) {  (* P2 can respond *)
      (pt1, pt2) <- oget (dec_ke_ideal_state_wait_req2 st);
      if (is_ke_req2 m) {
        (addr1, pt2') <- oget (dec_ke_req2 m);
        if (pt2' = pt2) {
          r <- Some (ke_sim_req2 self adv);
          st <- KEIdealStateWaitSim2(pt1, pt2);
        }
      }
    }
    elif (is_ke_ideal_state_wait_sim2 st) {  (* P1 can respond *)
      (pt1, pt2) <- oget (dec_ke_ideal_state_wait_sim2 st);
      if (is_ke_sim_rsp2 m) {
        (addr1, addr2) <- oget (dec_ke_sim_rsp2 m);
        r <- Some (ke_rsp2 self pt1 (g ^ q));
        st <- KEIdealStateFinal;
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
    (addr1, n1) <- pt1; (addr2, n2) <- pt2;
    if (addr1 = self /\ (n1 = 1 \/ n1 = 2)) {
      r <- parties(m);
    }
    return r;
  }
}.

type ke_sim_state = [
    KESimStateWaitReq1
  | KESimStateWaitAdv1 of addr
  | KESimStateWaitReq2 of addr
  | KESimStateWaitAdv2 of addr
  | KESimStateFinal
].

op dec_ke_sim_state_wait_adv1 (st : ke_sim_state) : addr option =
     with st = KESimStateWaitReq1   => None
     with st = KESimStateWaitAdv1 x => Some x
     with st = KESimStateWaitReq2 _ => None
     with st = KESimStateWaitAdv2 _ => None
     with st = KESimStateFinal      => None.

lemma enc_dec_ke_sim_state_wait_adv1 (x : addr) :
  dec_ke_sim_state_wait_adv1 (KESimStateWaitAdv1 x) = Some x.
proof. done. qed.

op is_ke_sim_state_wait_adv1 (st : ke_sim_state) : bool =
  dec_ke_sim_state_wait_adv1 st <> None.

lemma is_ke_sim_state_wait_adv1 (x : addr) :
  is_ke_sim_state_wait_adv1 (KESimStateWaitAdv1 x).
proof. done. qed.

op dec_ke_sim_state_wait_req2 (st : ke_sim_state) : addr option =
     with st = KESimStateWaitReq1   => None
     with st = KESimStateWaitAdv1 _ => None
     with st = KESimStateWaitReq2 x => Some x
     with st = KESimStateWaitAdv2 _ => None
     with st = KESimStateFinal      => None.

lemma enc_dec_ke_sim_state_wait_req2 (x : addr) :
  dec_ke_sim_state_wait_req2 (KESimStateWaitReq2 x) = Some x.
proof. done. qed.

op is_ke_sim_state_wait_req2 (st : ke_sim_state) : bool =
  dec_ke_sim_state_wait_req2 st <> None.

lemma is_ke_sim_state_wait_req2 (x : addr) :
  is_ke_sim_state_wait_req2 (KESimStateWaitReq2 x).
proof. done. qed.

op dec_ke_sim_state_wait_adv2 (st : ke_sim_state) : addr option =
     with st = KESimStateWaitReq1   => None
     with st = KESimStateWaitAdv1 _ => None
     with st = KESimStateWaitReq2 _ => None
     with st = KESimStateWaitAdv2 x => Some x
     with st = KESimStateFinal      => None.

lemma enc_dec_ke_sim_state_wait_adv2 (x : addr) :
  dec_ke_sim_state_wait_adv2 (KESimStateWaitAdv2 x) = Some x.
proof. done. qed.

op is_ke_sim_state_wait_adv2 (st : ke_sim_state) : bool =
  dec_ke_sim_state_wait_adv2 st <> None.

lemma is_ke_sim_state_wait_adv2 (x : addr) :
  is_ke_sim_state_wait_adv2 (KESimStateWaitAdv2 x).
proof. done. qed.

module KESim (Adv : FUNC) = {
  var self, adv : addr
  var q1, q2 : exp
  var st : ke_sim_state

  proc init(self_ adv_ : addr) : unit = {
    self <- self_; adv <- adv_;
    Adv.init(self, adv);
    q1 <$ dexp; q2 <$ dexp;
    st <- KESimStateWaitReq1;
  }

  proc loop(m : msg) : msg option = {
    var mod : mode; var pt1, pt2 : port; var u : univ;
    var addr, addr1, addr2 : addr;
    var r : msg option <- None;
    var not_done : bool <- true;
    while (not_done) {
      (* mod = Adv /\ pt1.`1 = self *)
      (mod, pt1, pt2, u) <- m;
      if (pt1.`2 = ke_sim_adv_pi) {  (* simulator *)
        r <- None;
        if (st = KESimStateWaitReq1) {
          if (is_ke_sim_req1 m) {
            (addr1, addr2) <- oget (dec_ke_sim_req1 m);
            r <-
              Some (Fwd1.fw_obs (addr1 ++ [1]) self (addr1, 1) (addr1, 2)
                    (UnivBase (BaseBits (g ^ q1))));
            st <- KESimStateWaitAdv1 addr1;
          }
        }
        elif (is_ke_sim_state_wait_req2 st) {
          addr <- oget (dec_ke_sim_state_wait_req2 st);
          if (is_ke_sim_req2 m) {
            (addr1, addr2) <- oget (dec_ke_sim_req2 m);
            r <-
              Some (Fwd2.fw_obs (addr ++ [2]) self (addr, 2) (addr, 1)
                    (UnivBase (BaseBits (g ^ q2))));
            st <- KESimStateWaitAdv2 addr;
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
          m <- oget r;
          (mod, pt1, pt2, u) <- m;
          if (is_ke_sim_state_wait_adv1 st) {
            addr <- oget (dec_ke_sim_state_wait_adv1 st);
            r <- None;
            if (Fwd1.is_fw_ok m) {
              (addr1, addr2) <- oget (Fwd1.dec_fw_ok m);
              if (addr1 = addr ++ [1]) {
                r <- Some (ke_sim_rsp1 addr self);
                st <- KESimStateWaitReq2 addr;
              }
            }
          }
          elif (is_ke_sim_state_wait_adv2 st) {
            r <- None;
            addr <- oget (dec_ke_sim_state_wait_adv2 st);
            if (Fwd2.is_fw_ok m) {
              (addr1, addr2) <- oget (Fwd2.dec_fw_ok m);
              if (addr1 = addr ++ [2]) {
                r <- Some (ke_sim_rsp2 addr self);
                st <- KESimStateFinal;
              }
            }
          }
          elif (self <= pt1.`1) {  (* not waiting on adversary *)
            r <- None;
          }
          not_done <- false;
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

module DDH_Adv (Env : ENV, Adv : FUNC) = {
  var func, adv : addr

  proc main(x1 x2 x3 : bits) : bool = {
    (* placeholder *)
    return true;
  }
}.

section.

declare module Adv : FUNC{KEReal, KEIdeal, KESim, DDH_Adv}.
declare module Env : ENV{Adv, KEReal, KEIdeal, KESim, DDH_Adv}.

lemma KESec (func adv : addr) &m :
  exper_pre func adv (fset1 adv_fw_pi) =>
  DDH_Adv.func{m} = func => DDH_Adv.adv{m} = adv =>
  `|Pr[Exper(MakeInter(KEReal, Adv), Env).main
         (func, adv, fset1 adv_fw_pi) @ &m : res] -
    Pr[Exper(MakeInter(KEIdeal, KESim(Adv)), Env).main
         (func, adv, fset1 adv_fw_pi) @ &m : res]| <=
  `|Pr[DDH1(DDH_Adv(Env, Adv)).main() @ &m : res] -
    Pr[DDH2(DDH_Adv(Env, Adv)).main() @ &m : res]|.
proof.
admit.
qed.

end section.

lemma KESecurity
        (Adv <: FUNC{KEReal, KEIdeal, KESim, DDH_Adv})
        (Env <: ENV{Adv, KEReal, KEIdeal, KESim, DDH_Adv})
        (func adv : addr) &m :
  exper_pre func adv (fset1 adv_fw_pi) =>
  DDH_Adv.func{m} = func => DDH_Adv.adv{m} = adv =>
  `|Pr[Exper(MakeInter(KEReal, Adv), Env).main
         (func, adv, fset1 adv_fw_pi) @ &m : res] -
    Pr[Exper(MakeInter(KEIdeal, KESim(Adv)), Env).main
         (func, adv, fset1 adv_fw_pi) @ &m : res]| <=
  `|Pr[DDH1(DDH_Adv(Env, Adv)).main() @ &m : res] -
    Pr[DDH2(DDH_Adv(Env, Adv)).main() @ &m : res]|.
proof.
move => pre func_eq adv_eq.
by apply (KESec Adv Env func adv &m).
qed.

end KeyExchange.

theory SMC.

(* theory parameters *)

(* port index of adversary that forwarding functionalities communicate
   with *)

op adv_fw_pi : int.

(* port index of adversary that key exchange's simulator communicates
   with *)

op ke_sim_adv_pi : int.

(* port index of adversary that SMC's simulator communicates
   with *)

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
              Some (pt2.`1, oget(dec_univ_port v1), pt1, oget (dec_base_bits b)).

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
  | SMCRealStateFinal
].

op dec_smc_real_state_wait_ke1 (st : smc_real_state) :
     (port * port * bits) option =
     with st = SMCRealStateWaitReq   => None
     with st = SMCRealStateWaitKE1 x => Some x
     with st = SMCRealStateWaitKE2 _ => None
     with st = SMCRealStateWaitFwd _ => None
     with st = SMCRealStateFinal     => None.

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
     with st = SMCRealStateFinal     => None.

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
     with st = SMCRealStateFinal     => None.

lemma enc_dec_smc_real_state_wait_fwd (x : port * port * bits * bits * bits) :
  dec_smc_real_state_wait_fwd (SMCRealStateWaitFwd x) = Some x.
proof. done. qed.

op is_smc_real_state_wait_fwd (st : smc_real_state) : bool =
  dec_smc_real_state_wait_fwd st <> None.

lemma is_smc_real_state_wait_fwd (x : port * port * bits * bits * bits) :
  is_smc_real_state_wait_fwd (SMCRealStateWaitFwd x).
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
        (addr, pt1, pt2, x1) <- oget (dec_smc_req m);
        if (! self <= pt1.`1 /\ ! self <= pt2.`1) {
          r <-
            Some (KeyEx.ke_req1 (self ++ [2]) (self, 1) (self, 2));
          st <- SMCRealStateWaitKE1(pt1, pt2, x1);
        }
      }
    }
    elif (is_smc_real_state_wait_ke1 st) {  (* P2 *)
      (pt1, pt2, x1) <- oget (dec_smc_real_state_wait_ke1 st);
      if (KeyEx.is_ke_rsp1 m) {
        (addr, pt1', pt2', k2) <- oget (KeyEx.dec_ke_rsp1 m);
        r <-
          Some (KeyEx.ke_req2 (self ++ [2]) (self, 2));
        st <- SMCRealStateWaitKE2(pt1, pt2, x1, k2);
      }
    }
    elif (is_smc_real_state_wait_ke2 st) {  (* P1 *)
      (pt1, pt2, x1, k2) <- oget (dec_smc_real_state_wait_ke2 st);
      if (KeyEx.is_ke_rsp2 m) {
        (addr, pt1', k1) <- oget (KeyEx.dec_ke_rsp2 m);
        r <-
          Some (Fwd.fw_req (self ++ [1]) (self, 1) (self, 2)
                (UnivBase (BaseBits (x1 ^^ k1))));
        st <- SMCRealStateWaitFwd(pt1, pt2, x1, k2, k1);
      }
    }
    elif (is_smc_real_state_wait_fwd st) {  (* P2 *)
      (pt1, pt2, x1, k2, k1) <- oget (dec_smc_real_state_wait_fwd st);
      if (Fwd.is_fw_rsp m) {
        (addr, pt1', pt2', u) <- oget (Fwd.dec_fw_rsp m);
        x2 <- oget (dec_base_bits (oget (dec_univ_base u))) ^^ k2;
        r <- Some (smc_rsp self pt1 pt2 x2);
        st <- SMCRealStateFinal;
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
    if ((mod = Dir /\ addr1 = self) \/
        (mod = Adv /\ (self ++ [1] <= addr1 \/ self ++ [2] <= addr1))) {
      r <- loop(m);
    }
    return r;
  }
}.

(* request sent from port 1 of SMC ideal functionality to port
   smc_sim_adv_pi of SMC simulator *)

op smc_sim_req (ideal adv : addr) : msg =
     (Adv, (adv, smc_sim_adv_pi), (ideal, 1), UnivUnit).

op dec_smc_sim_req (m : msg) : (addr * addr) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Dir \/ pt1.`2 <> smc_sim_adv_pi \/ pt2.`2 <> 1 \/
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

(* response sent from port smc_sim_adv_pi of SMC simulator to port 2
   of SMC ideal functionality *)

op smc_sim_rsp (ideal adv : addr) : msg =
     (Adv, (ideal, 2), (adv, smc_sim_adv_pi), UnivUnit).

op dec_smc_sim_rsp (m : msg) : (addr * addr) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Dir \/ pt1.`2 <> 2 \/ pt2.`2 <> smc_sim_adv_pi \/
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
  | SMCIdealStateFinal
].

op dec_smc_ideal_state_wait_sim (st : smc_ideal_state) :
     (port * port * bits) option =
     with st = SMCIdealStateWaitReq   => None
     with st = SMCIdealStateWaitSim x => Some x
     with st = SMCIdealStateFinal     => None.

lemma enc_dec_smc_ideal_state_wait_sim (x : port * port * bits) :
  dec_smc_ideal_state_wait_sim (SMCIdealStateWaitSim x) = Some x.
proof. done. qed.

op is_smc_ideal_state_wait_sim (st : smc_ideal_state) : bool =
  dec_smc_ideal_state_wait_sim st <> None.

lemma is_smc_ideal_state_wait_sim (x : port * port * bits) :
  is_smc_ideal_state_wait_sim (SMCIdealStateWaitSim x).
proof. done. qed.

module SMCIdeal : FUNC = {
  var self, adv : addr
  var st : smc_ideal_state

  proc init(self_ adv_ : addr) : unit = {
    var u : exp;
    self <- self_; adv <- adv_;
    st <- SMCIdealStateWaitReq;
  }

  proc parties(m : msg) : msg option = {
    var pt1, pt2, pt1', pt2' : port; var addr, addr1, addr2 : addr;
    var x : bits;
    var r : msg option <- None;
    if (st = SMCIdealStateWaitReq) {  (* P1 *)
      if (is_smc_req m) {
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
        (addr1, addr2) <- oget (dec_smc_sim_rsp m);
        r <- Some (smc_rsp self pt1 pt2 x);
        st <- SMCIdealStateFinal;
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
    if (mod = Dir /\ addr1 = self) {
      r <- parties(m);
    }
    return r;
  }
}.

type smc_sim_state = [
    SMCSimStateWaitReq
  | SMCSimStateWaitAdv1 of addr
  | SMCSimStateWaitAdv2 of addr
  | SMCSimStateWaitAdv3 of addr
  | SMCSimStateFinal
].

op dec_smc_sim_state_wait_adv1 (st : smc_sim_state) : addr option =
     with st = SMCSimStateWaitReq    => None
     with st = SMCSimStateWaitAdv1 x => Some x
     with st = SMCSimStateWaitAdv2 _ => None
     with st = SMCSimStateWaitAdv3 _ => None
     with st = SMCSimStateFinal      => None.

lemma enc_dec_smc_sim_state_wait_adv1 (x : addr) :
  dec_smc_sim_state_wait_adv1 (SMCSimStateWaitAdv1 x) = Some x.
proof. done. qed.

op is_smc_sim_state_wait_adv1 (st : smc_sim_state) : bool =
  dec_smc_sim_state_wait_adv1 st <> None.

lemma is_smc_sim_state_wait_adv1 (x : addr) :
  is_smc_sim_state_wait_adv1 (SMCSimStateWaitAdv1 x).
proof. done. qed.

op dec_smc_sim_state_wait_adv2 (st : smc_sim_state) : addr option =
     with st = SMCSimStateWaitReq    => None
     with st = SMCSimStateWaitAdv1 _ => None
     with st = SMCSimStateWaitAdv2 x => Some x
     with st = SMCSimStateWaitAdv3 _ => None
     with st = SMCSimStateFinal      => None.

lemma enc_dec_smc_sim_state_wait_adv2 (x : addr) :
  dec_smc_sim_state_wait_adv2 (SMCSimStateWaitAdv2 x) = Some x.
proof. done. qed.

op is_smc_sim_state_wait_adv2 (st : smc_sim_state) : bool =
  dec_smc_sim_state_wait_adv2 st <> None.

lemma is_smc_sim_state_wait_adv2 (x : addr) :
  is_smc_sim_state_wait_adv2 (SMCSimStateWaitAdv2 x).
proof. done. qed.

op dec_smc_sim_state_wait_adv3 (st : smc_sim_state) : addr option =
     with st = SMCSimStateWaitReq    => None
     with st = SMCSimStateWaitAdv1 _ => None
     with st = SMCSimStateWaitAdv2 _ => None
     with st = SMCSimStateWaitAdv3 x => Some x
     with st = SMCSimStateFinal      => None.

lemma enc_dec_smc_sim_state_wait_adv3 (x : addr) :
  dec_smc_sim_state_wait_adv3 (SMCSimStateWaitAdv3 x) = Some x.
proof. done. qed.

op is_smc_sim_state_wait_adv3 (st : smc_sim_state) : bool =
  dec_smc_sim_state_wait_adv3 st <> None.

lemma is_smc_sim_state_wait_adv3 (x : addr) :
  is_smc_sim_state_wait_adv3 (SMCSimStateWaitAdv3 x).
proof. done. qed.

module SMCSim (Adv : FUNC) = {
  var self, adv : addr
  var x : bits
  var st : smc_sim_state

  proc init(self_ adv_ : addr) : unit = {
    var q : exp;
    self <- self_; adv <- adv_;
    Adv.init(self, adv);
    q <$ dexp; x <- g ^ q;
    st <- SMCSimStateWaitReq;
  }

  proc loop(m : msg) : msg option = {
    var mod : mode; var pt1, pt2 : port; var u : univ;
    var addr, addr1, addr2 : addr;
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
            r <- Some (KeyEx.ke_sim_req1 (addr1 ++ [2]) self);
            st <- SMCSimStateWaitAdv1 addr1;
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
            addr <- oget (dec_smc_sim_state_wait_adv1 st);
            r <- None;
            if (KeyEx.is_ke_sim_rsp1 m) {
              (addr1, addr2) <- oget (KeyEx.dec_ke_sim_rsp1 m);
              if (addr1 = addr ++ [2]) {
                r <- Some (KeyEx.ke_sim_req2 (addr ++ [2]) self);
                st <- SMCSimStateWaitAdv2 addr;
              }
            }
          }
          if (is_smc_sim_state_wait_adv2 st) {
            addr <- oget (dec_smc_sim_state_wait_adv2 st);
            r <- None;
            if (KeyEx.is_ke_sim_rsp2 m) {
              (addr1, addr2) <- oget (KeyEx.dec_ke_sim_rsp2 m);
              if (addr1 = addr ++ [2]) {
                r <-
                  Some (Fwd.fw_obs (addr ++ [1]) self (addr, 1) (addr, 2)
                        (UnivBase (BaseBits x)));
                st <- SMCSimStateWaitAdv3 addr;
              }
            }
          }
          if (is_smc_sim_state_wait_adv3 st) {
            addr <- oget (dec_smc_sim_state_wait_adv3 st);
            r <- None;
            if (Fwd.is_fw_ok m) {
              (addr1, addr2) <- oget (Fwd.dec_fw_ok m);
              if (addr1 = addr ++ [1]) {
                r <- Some (smc_sim_rsp addr self);
                st <- SMCSimStateFinal;
              }
            }
          }
          elif (self <= pt1.`1) {  (* not waiting on adversary *)
            r <- None;
          }
          not_done <- false;
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

module CompEnv (Env : ENV, Inter : INTER) = {
  proc main(func adv : addr, in_guard : int fset) : bool = {
    (* placeholder *)
    return true;
  }
}.

section.

declare module Adv : FUNC{SMCReal, KeyEx.KEReal, KeyEx.KEIdeal,
                          KeyEx.KESim, KeyEx.DDH_Adv}.
declare module Env : ENV{Adv, SMCReal, KeyEx.KEReal, KeyEx.KEIdeal,
                         KeyEx.KESim, KeyEx.DDH_Adv}.

lemma SMCSec1 (func adv : addr) &m :
  exper_pre func adv (fset1 adv_fw_pi) =>
  KeyEx.DDH_Adv.func{m} = func => KeyEx.DDH_Adv.adv{m} = adv =>
  `|Pr[Exper(MakeInter(SMCReal(KeyEx.KEReal), Adv), Env).main
         (func, adv, fset1 adv_fw_pi) @ &m : res] -
    Pr[Exper(MakeInter(SMCReal(KeyEx.KEIdeal), KeyEx.KESim(Adv)), Env).main
         (func, adv, fset1 adv_fw_pi) @ &m : res]| <=
  `|Pr[DDH1(KeyEx.DDH_Adv(CompEnv(Env), Adv)).main() @ &m : res] -
    Pr[DDH2(KeyEx.DDH_Adv(CompEnv(Env), Adv)).main() @ &m : res]|.
proof.
move => pre func_eq adv_eq.
admit.
qed.

end section.

lemma SMCSecurity1
        (Adv <: FUNC{SMCReal, KeyEx.KEReal, KeyEx.KEIdeal,
                     KeyEx.KESim, KeyEx.DDH_Adv})
        (Env <: ENV{Adv, SMCReal, KeyEx.KEReal, KeyEx.KEIdeal,
                    KeyEx.KESim, KeyEx.DDH_Adv})
        (func adv : addr) &m :
  exper_pre func adv (fset1 adv_fw_pi) =>
  KeyEx.DDH_Adv.func{m} = func => KeyEx.DDH_Adv.adv{m} = adv =>
  `|Pr[Exper(MakeInter(SMCReal(KeyEx.KEReal), Adv), Env).main
         (func, adv, fset1 adv_fw_pi) @ &m : res] -
    Pr[Exper(MakeInter(SMCReal(KeyEx.KEIdeal), KeyEx.KESim(Adv)), Env).main
         (func, adv, fset1 adv_fw_pi) @ &m : res]| <=
  `|Pr[DDH1(KeyEx.DDH_Adv(CompEnv(Env), Adv)).main() @ &m : res] -
    Pr[DDH2(KeyEx.DDH_Adv(CompEnv(Env), Adv)).main() @ &m : res]|.
proof.
move => pre func_eq adv_eq.
by apply (SMCSec1 Adv Env func adv &m).
qed.

section.

declare module Adv : FUNC{SMCReal, KeyEx.KEIdeal, SMCIdeal, SMCSim}.
declare module Env : ENV{Adv, SMCReal, KeyEx.KEIdeal, SMCIdeal, SMCSim}.

lemma SMCSec2 (func adv : addr) &m :
  exper_pre func adv (fset1 adv_fw_pi) =>
  Pr[Exper(MakeInter(SMCReal(KeyEx.KEIdeal), Adv), Env).main
       (func, adv, fset1 adv_fw_pi) @ &m : res] =
  Pr[Exper(MakeInter(SMCIdeal, SMCSim(Adv)), Env).main
       (func, adv, fset1 adv_fw_pi) @ &m : res].
proof.
move => pre.
byequiv => //.
proc.
admit.
qed.

end section.

lemma SMCSecurity2
        (Adv <: FUNC{SMCReal, SMCIdeal, SMCSim, KeyEx.KEIdeal})
        (Env <: ENV{Adv, SMCReal, SMCIdeal, SMCSim, KeyEx.KEIdeal})
        (func adv : addr) &m :
  exper_pre func adv (fset1 adv_fw_pi) =>
  Pr[Exper(MakeInter(SMCReal(KeyEx.KEIdeal), Adv), Env).main
       (func, adv, fset1 adv_fw_pi) @ &m : res] =
  Pr[Exper(MakeInter(SMCIdeal, SMCSim(Adv)), Env).main
       (func, adv, fset1 adv_fw_pi) @ &m : res].
proof.
move => pre.
by apply (SMCSec2 Adv Env func adv &m).
qed.

lemma SMCSecurity
        (Adv <: FUNC{SMCReal, SMCIdeal, SMCSim, KeyEx.KEReal, KeyEx.KEIdeal,
                     KeyEx.KESim, KeyEx.DDH_Adv})
        (Env <: ENV{Adv, SMCReal, SMCIdeal, SMCSim, KeyEx.KEReal, KeyEx.KEIdeal,
                    KeyEx.KESim, KeyEx.DDH_Adv})
        (func adv : addr) &m :
  exper_pre func adv (fset1 adv_fw_pi) =>
  KeyEx.DDH_Adv.func{m} = func => KeyEx.DDH_Adv.adv{m} = adv =>
  `|Pr[Exper(MakeInter(SMCReal(KeyEx.KEReal), Adv), Env).main
         (func, adv, fset1 adv_fw_pi) @ &m : res] -
    Pr[Exper(MakeInter(SMCIdeal, SMCSim(KeyEx.KESim(Adv))), Env).main
         (func, adv, fset1 adv_fw_pi) @ &m : res]| <=
  `|Pr[DDH1(KeyEx.DDH_Adv(CompEnv(Env), Adv)).main() @ &m : res] -
    Pr[DDH2(KeyEx.DDH_Adv(CompEnv(Env), Adv)).main() @ &m : res]|.
proof.
move => pre func_eq adv_eq.
by rewrite -(SMCSecurity2 (KeyEx.KESim(Adv)) Env func adv &m) //
           (SMCSecurity1 Adv Env func adv &m).
qed.
