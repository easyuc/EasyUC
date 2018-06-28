(* SMC.ec *)

prover quorum=2 ["Alt-Ergo" "Z3"].

require import AllCore List FSet SmtMap Distr ListAux ListPO.
require DDH UCCore RedundantHashing.

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

axiom mulA (q r s : exp) : q * r * s = q * (r * s).

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

axiom double_exp_gen (q1 q2 : exp) : (g ^ q1) ^ q2 = g ^ (q1 * q2).

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

lemma log_genK : cancel gen log.
proof.
rewrite /gen /log /cancel => q.
have choice_g2q := choicebP (gen_rel (g ^ q)) e.
have /choice_g2q @/gen_rel /gen_inj {2}-> // :
  exists (q' : exp), gen_rel (g ^ q) q'
  by rewrite /gen_rel; by exists q.
qed.

lemma gen_logK : cancel log gen.
proof.
rewrite /gen /log /cancel => x.
have @/gen_rel <- // := choicebP (gen_rel x) e.
rewrite gen_surj.
qed.

lemma double_exp (x : bits, q1 q2 : exp) :
  (x ^ q1) ^ q2 = x ^ (q1 * q2).
proof.
have -> : x = g ^ log x by smt(gen_logK).
by rewrite !double_exp_gen mulA.
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
realize mulA. apply mulA. qed.
realize dexp_fu. apply dexp_fu. qed.
realize dexp_uni. apply dexp_uni. qed.
realize dexp_ll. apply dexp_ll. qed.
realize double_exp_gen. apply double_exp_gen. qed.
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

(* request sent to port index 1 of forwarding functionality: pt1 is
   asking to forward u to pt2 *)

op fw_req (func : addr, pt1 pt2 : port, u : univ) : msg =
     (Dir, (func, 1), pt1, UnivPair (UnivPort pt2, u)).

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
proof. done. qed.

op is_fw_req (m : msg) : bool =
     dec_fw_req m <> None.

lemma is_fw_req (func : addr, pt1 pt2 : port, u : univ) :
  is_fw_req (fw_req func pt1 pt2 u).
proof. done. qed.

lemma dest_good_fw_req (m : msg) :
  is_fw_req m =>
  (oget (dec_fw_req m)).`1 = m.`2.`1 /\ m.`2.`2 = 1.
proof.
case m => mod pt1 pt2 u.
rewrite /is_fw_req /dec_fw_req /=.
case (mod = Adv \/ pt1.`2 <> 1 \/ ! is_univ_pair u) => //.
rewrite !negb_or /=.
move => [#] _ _.
rewrite /is_univ_pair /dec_univ_pair; case u => // x /=.
rewrite oget_some; case x => /= x1 x2.
case (is_univ_port x1) => //=.
qed.

(* response sent from port index 1 of forwarding functionality to pt2,
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
           Some (pt2.`1, oget (dec_univ_port v1), pt1, v2).

lemma enc_dec_fw_rsp (func : addr, pt1 pt2 : port, u : univ) :
  dec_fw_rsp (fw_rsp func pt1 pt2 u) = Some (func, pt1, pt2, u).
proof. done. qed.

op is_fw_rsp (m : msg) : bool =
     dec_fw_rsp m <> None.

lemma is_fw_rsp (func : addr, pt1 pt2 : port, u : univ) :
  is_fw_rsp (fw_rsp func pt1 pt2 u).
proof. done. qed.

print fw_rsp.

lemma dest_good_fw_rsp (m : msg) :
  is_fw_rsp m => (oget (dec_fw_rsp m)).`3 = m.`2.
proof.
case m => mod pt1 pt2 u.
rewrite /is_fw_rsp /dec_fw_rsp /=.
case (mod = Adv \/ pt2.`2 <> 1 \/ ! is_univ_pair u) => //.
rewrite !negb_or /=.
move => [#] _ _.
rewrite /is_univ_pair /dec_univ_pair; case u => // x /=.
rewrite oget_some; case x => /= x1 x2.
case (is_univ_port x1) => //.
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

lemma dest_good_fw_ok (m : msg) :
  is_fw_ok m => (oget (dec_fw_ok m)).`1 = m.`2.`1 /\
  m.`2.`2 = 1.
proof.
case m => mod pt1 pt2 u.
rewrite /is_fw_ok /dec_fw_ok /=.
case
  (mod = Dir \/ pt1.`2 <> 1 \/ pt2.`2 <> adv_pi \/
   u <> UnivUnit) => //.
by rewrite !negb_or /=.
qed.

type fw_state = [
    FwStateInit
  | FwStateWait  of (port * port * univ)
  | FwStateFinal of (port * port * univ)
].

op dec_fw_state_wait (st : fw_state) : (port * port * univ) option =
     with st = FwStateInit    => None
     with st = FwStateWait t  => Some t
     with st = FwStateFinal _ => None.

lemma enc_dec_fw_state_wait (t : port * port * univ) :
  dec_fw_state_wait (FwStateWait t) = Some t.
proof. done. qed.

op is_fw_state_wait (st : fw_state) : bool =
  dec_fw_state_wait st <> None.

lemma is_fw_state_wait (t : port * port * univ) :
  is_fw_state_wait (FwStateWait t).
proof. done. qed.

op dec_fw_state_final (st : fw_state) : (port * port * univ) option =
     with st = FwStateInit    => None
     with st = FwStateWait _  => None
     with st = FwStateFinal x => Some x.

lemma enc_dec_fw_final (t : port * port * univ) :
  dec_fw_state_final (FwStateFinal t) = Some t.
proof. done. qed.

op is_fw_state_final (st : fw_state) : bool =
  dec_fw_state_final st <> None.

lemma is_fw_state_final (t : port * port * univ) :
  is_fw_state_final (FwStateFinal t).
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
        (addr1, pt1, pt2, u) <- oget (dec_fw_req m);
        if (self = addr1 /\ ! self <= pt1.`1 /\ ! self <= pt2.`1) {
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
          r <- Some (fw_rsp self pt1 pt2 u);
          st <- FwStateFinal (pt1, pt2, u);
        }
      }
    }
    return r;
  }
}.

end Forward.

(************************ Diffie-Hellman Key Exchange *************************)

theory KeyExchange.

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
              Some (pt2.`1, oget (dec_univ_port v1), pt1,
                    oget (dec_base_bits b)).

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
    var u : univ; var x2 : bits; var q1 : exp;
    var r : msg option <- None;
    if (st1 = KERealP1StateWaitReq1) {
      if (is_ke_req1 m) {
        (* destination of m is (self, 1) *)
        (addr, pt1, pt2) <- oget (dec_ke_req1 m);
        if (! self <= pt1.`1 /\ ! self <= pt2.`1) {
          q1 <$ dexp;
          r <-
            Some
            (Fwd1.fw_req
             (self ++ [1]) (self, 3) (self, 4)
              (univ_triple (UnivPort pt1) (UnivPort pt2)
               (UnivBase (BaseBits (g ^ q1)))));
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
          x2 <- oget (dec_base_bits (oget (dec_univ_base u)));
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
    var u, v1, v2, v3 : univ; var x1 : bits; var q2 : exp;
    var r : msg option <- None;
    if (st2 = KERealP2StateWaitFwd1) {
      if (Fwd1.is_fw_rsp m) {
        (addr, pt1', pt2', u) <- oget (Fwd1.dec_fw_rsp m);
        if (pt2' = (self, 4)) {
          (* destination of m is (self, 4) *)
          (v1, v2, v3) <- oget (dec_univ_triple u);
          pt1 <- oget (dec_univ_port v1);
          pt2 <- oget (dec_univ_port v2);
          x1 <- oget (dec_base_bits (oget (dec_univ_base v3)));
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
             (UnivBase (BaseBits (g ^ q2))));
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
   port 3 of key exchange ideal functionality, completing first
   phase of simulator execution *)

op ke_sim_rsp1 (ideal adv : addr) : msg =
     (Adv, (ideal, 3), (adv, ke_sim_adv_pi), UnivUnit).

op dec_ke_sim_rsp1 (m : msg) : (addr * addr) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Dir \/ pt1.`2 <> 3 \/ pt2.`2 <> ke_sim_adv_pi \/
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

(* response sent from port ke_sim_adv_pi of key exchange simulator to
   port 3 of key exchange ideal functionality, completing second
   phase of simulator execution *)

op ke_sim_rsp2 (ideal adv : addr) : msg =
     (Adv, (ideal, 3), (adv, ke_sim_adv_pi), UnivUnit).

op dec_ke_sim_rsp2 (m : msg) : (addr * addr) option =
     let (mod, pt1, pt2, v) = m
     in (mod = Dir \/ pt1.`2 <> 3 \/ pt2.`2 <> ke_sim_adv_pi \/
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
        if (! self <= pt1.`1 /\ ! self <= pt2.`1) {
          r <- Some (ke_sim_req1 self adv pt1 pt2);
          st <- KEIdealStateWaitSim1 (pt1, pt2);
        }
      }
    }
    elif (is_ke_ideal_state_wait_sim1 st) {
      (pt1, pt2) <- oget (dec_ke_ideal_state_wait_sim1 st);
      if (is_ke_sim_rsp1 m) {
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
      if (is_ke_sim_rsp2 m) {
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
    var addr, addr1, addr2 : addr; var q1, q2 : exp;
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
                (UnivBase (BaseBits (g ^ q1)))));
            st <- KESimStateWaitAdv1 (addr1, q1);
          }
        }
        elif (is_ke_sim_state_wait_req2 st) {
          (addr, q1, q2) <- oget (dec_ke_sim_state_wait_req2 st);
          if (is_ke_sim_req2 m) {
            (addr1, addr2) <- oget (dec_ke_sim_req2 m);
            r <-
              Some (Fwd2.fw_obs (addr ++ [2]) self (addr, 4) (addr, 3)
                    (UnivBase (BaseBits (g ^ q2))));
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
        if (r = None) {
          not_done <- false;
        }
        else {
          m <- oget r;
          (mod, pt1, pt2, u) <- m;
          if (is_ke_sim_state_wait_adv1 st) {
            (addr, q1) <- oget (dec_ke_sim_state_wait_adv1 st);
            r <- None;
            if (Fwd1.is_fw_ok m) {
              (addr1, addr2) <- oget (Fwd1.dec_fw_ok m);
              if (addr1 = addr ++ [1]) {
                q2 <$ dexp;
                r <- Some (ke_sim_rsp1 addr self);
                st <- KESimStateWaitReq2 (addr, q1, q2);
              }
            }
          }
          elif (is_ke_sim_state_wait_adv2 st) {
            r <- None;
            (addr, q1, q2) <- oget (dec_ke_sim_state_wait_adv2 st);
            if (Fwd2.is_fw_ok m) {
              (addr1, addr2) <- oget (Fwd2.dec_fw_ok m);
              if (addr1 = addr ++ [2]) {
                r <- Some (ke_sim_rsp2 addr self);
                st <- KESimStateFinal (addr, q1, q2);
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

abstract theory KESimp.

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
        if (! self <= pt1.`1 /\ ! self <= pt2.`1) {
          q1 <$ dexp;
          u <-
            univ_triple (UnivPort pt1) (UnivPort pt2)
                        (UnivBase (BaseBits (g ^ q1)));
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
          u <- UnivBase (BaseBits (g ^ q2));
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
                  (UnivBase (BaseBits (g ^ q1))))) /\
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
                  (UnivBase (BaseBits (g ^ q1))))) /\
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
                  (UnivBase (BaseBits (g ^ q1))))) /\
  (st.`real_simp_rel_st_fws2 =
     Fwd2.FwStateWait
     ((st.`real_simp_rel_st_func, 4), (st.`real_simp_rel_st_func, 3),
      UnivBase (BaseBits (g ^ q2)))) /\
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
                  (UnivBase (BaseBits (g ^ q1))))) /\
  (st.`real_simp_rel_st_fws2 =
     Fwd2.FwStateFinal
     ((st.`real_simp_rel_st_func, 4), (st.`real_simp_rel_st_func, 3),
      UnivBase (BaseBits (g ^ q2)))) /\
  (st.`real_simp_rel_st_rss  = KERealSimpStateFinal (pt1, pt2, q1, q2)).

inductive ke_real_simp_rel (st : real_simp_rel_st) =
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
   ke_real_simp_rel
   {|real_simp_rel_st_func = func;
     real_simp_rel_st_r1s  = KEReal.st1{1};
     real_simp_rel_st_r2s  = KEReal.st2{1};
     real_simp_rel_st_fws1 = Fwd1.Forw.st{1};
     real_simp_rel_st_fws2 = Fwd2.Forw.st{1};
     real_simp_rel_st_rss  = KERealSimp.st{2}|} ==>
   ={res} /\
   KEReal.self{1} = func /\ KEReal.adv{1} = adv /\
   Fwd1.Forw.self{1} = func ++ [1] /\ Fwd1.Forw.adv{1} = adv /\
   Fwd2.Forw.self{1} = func ++ [2] /\ Fwd2.Forw.adv{1} = adv /\
   KERealSimp.self{2} = func /\ KERealSimp.adv{2} = adv /\
   ke_real_simp_rel
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
   ke_real_simp_rel
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
by rewrite oget_some enc_dec_base_bits oget_some.
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
     real_simp_rel_st_r1s   = KEReal.st1{1};
     real_simp_rel_st_r2s   = KEReal.st2{1};
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

end KESimp.

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
  var x1, x2, x3 : bits

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
          if (! self <= pt1.`1 /\ ! self <= pt2.`1) {
            u <-
              univ_triple (UnivPort pt1) (UnivPort pt2)
                          (UnivBase (BaseBits x1));
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
            u <- UnivBase (BaseBits x2);
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

  proc main(x1_ x2_ x3_ : bits) : bool = {
    var b : bool;
    x1 <- x1_; x2 <- x2_; x3 <- x3_; 
    b <@ Exper(MI(KEDDH, Adv), Env).main(func, adv, fset1 adv_fw_pi);
    return b;
  }
}.

section.

declare module Adv : FUNC{MI, KEReal, KEIdeal, KESim, DDH_Adv}.
declare module Env : ENV{Adv, MI, KEReal, KEIdeal, KESim, DDH_Adv}.

local clone import KESimp as KESimp'.

local lemma Exper_KEReal_KERealSimp (func' adv' : addr) &m :
  exper_pre func' adv' (fset1 adv_fw_pi) =>
  Pr[Exper(MI(KEReal, Adv), Env).main
       (func', adv', fset1 adv_fw_pi) @ &m : res] =
  Pr[Exper(MI(KERealSimp, Adv), Env).main
       (func', adv', fset1 adv_fw_pi) @ &m : res].
proof.
move => pre.
byequiv => //.
proc.
seq 1 1 :
  (={func, adv, in_guard} /\
   func{1} = func' /\ adv{1} = adv' /\ in_guard{1} = fset1 adv_fw_pi /\
   ={MI.func, MI.adv, MI.in_guard} /\
   MI.func{1} = func' /\ MI.adv{1} = adv' /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   ! func' <= adv' /\
   KEReal.self{1} = func' /\ KEReal.adv{1} = adv' /\
   Fwd1.Forw.self{1} = func' ++ [1] /\ Fwd1.Forw.adv{1} = adv' /\
   Fwd2.Forw.self{1} = func' ++ [2] /\ Fwd2.Forw.adv{1} = adv' /\
   KERealSimp.self{2} = func' /\ KERealSimp.adv{2} = adv' /\
   ={glob Adv} /\
   ke_real_simp_rel
   {|real_simp_rel_st_func = func';
     real_simp_rel_st_r1s  = KEReal.st1{1};
     real_simp_rel_st_r2s  = KEReal.st2{1};
     real_simp_rel_st_fws1 = Fwd1.Forw.st{1};
     real_simp_rel_st_fws2 = Fwd2.Forw.st{1};
     real_simp_rel_st_rss  = KERealSimp.st{2}|}).
inline*.
call (_ : true).
auto; progress; [smt() | rewrite RealSimpRel0 /#].
call 
  (_ :
   ={MI.func, MI.adv, MI.in_guard} /\
   MI.func{1} = func' /\ MI.adv{1} = adv' /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   ! func' <= adv' /\
   KEReal.self{1} = func' /\ KEReal.adv{1} = adv' /\
   Fwd1.Forw.self{1} = func' ++ [1] /\ Fwd1.Forw.adv{1} = adv' /\
   Fwd2.Forw.self{1} = func' ++ [2] /\ Fwd2.Forw.adv{1} = adv' /\
   KERealSimp.self{2} = func' /\ KERealSimp.adv{2} = adv' /\
   ={glob Adv} /\
   ke_real_simp_rel
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
wp; sp 3 3.
while
  (={not_done} /\ ={m0, r0} /\
   ={MI.func, MI.adv, MI.in_guard} /\
   MI.func{1} = func' /\ MI.adv{1} = adv' /\
   MI.in_guard{1} = fset1 adv_fw_pi /\
   ! func' <= adv' /\
   KEReal.self{1} = func' /\ KEReal.adv{1} = adv' /\
   Fwd1.Forw.self{1} = func' ++ [1] /\ Fwd1.Forw.adv{1} = adv' /\
   Fwd2.Forw.self{1} = func' ++ [2] /\ Fwd2.Forw.adv{1} = adv' /\
   KERealSimp.self{2} = func' /\ KERealSimp.adv{2} = adv' /\
   ={glob Adv} /\
   ke_real_simp_rel
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
          if (! self <= pt1.`1 /\ ! self <= pt2.`1) {
            q1 <@ Hash.hash(exp1);
            u <-
              univ_triple (UnivPort pt1) (UnivPort pt2)
                          (UnivBase (BaseBits (g ^ q1)));
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
            u <- UnivBase (BaseBits (g ^ q2));
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

local lemma Exper_KERealSimp_GOptHashing_KERealSimpHashingAdv (func' adv' : addr) &m :
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
apply RealSimpHashRel0.
rewrite /real_simp_hash_rel0 /=; smt(emptyE).
qed.

(* relation supporting transition from
  RH.GNonOptHashing(KERealSimpHashingAdv) to
  DDH1(DDH_Adv(Env, Adv)) *)

type real_simp_hash_ddh1_rel_st = {
  real_simp_hash_ddh1_rel_st_x1 : bits;
  real_simp_hash_ddh1_rel_st_x2 : bits;
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
smt(gen_logK).
rewrite (RealSimpHashDDH1Rel1 _ pt10{2} pt20{2}) /#.
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
rewrite (RealSimpHashDDH1Rel2 _ pt1 pt2).
by rewrite /real_simp_hash_ddh1_rel2 /= mp_exp2_eq oget_some.
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

module KEHybrid : FUNC = {
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
        if (! self <= pt1.`1 /\ ! self <= pt2.`1) {
          q1 <$ dexp;
          u <-
            univ_triple (UnivPort pt1) (UnivPort pt2)
                        (UnivBase (BaseBits (g ^ q1)));
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
          u <- UnivBase (BaseBits (g ^ q2));
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
        if (! self <= pt1.`1 /\ ! self <= pt2.`1) {
          q1 <@ Hash.hash(exp1);
          u <-
            univ_triple (UnivPort pt1) (UnivPort pt2)
                        (UnivBase (BaseBits (g ^ q1)));
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
          u <- UnivBase (BaseBits (g ^ q2));
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

local lemma DDH2_DDH_Adv_KEHybridHashingAdv_NonOptHashing
            (func' adv' : addr) &m :
  DDH_Adv.func{m} = func' => DDH_Adv.adv{m} = adv' =>
  Pr[DDH2(DDH_Adv(Env, Adv)).main() @ &m : res] =
  Pr[RH.GNonOptHashing(KEHybridHashingAdv).main() @ &m : res].
proof.
admit.
qed.

local lemma KEHybridHashingAdv_OptHashing_Exper_KEHybrid (func' adv' : addr) &m :
  DDH_Adv.func{m} = func' => DDH_Adv.adv{m} = adv' =>
  Pr[RH.GOptHashing(KEHybridHashingAdv).main() @ &m : res] =
  Pr[Exper(MI(KEHybrid, Adv), Env).main
       (func', adv', fset1 adv_fw_pi) @ &m : res].
proof.
admit.
qed.

local lemma Exper_KEHybrid_KEIdeal_KESim (func' adv' : addr) &m :
  exper_pre func' adv' (fset1 adv_fw_pi) =>
  Pr[Exper(MI(KEHybrid, Adv), Env).main
       (func', adv', fset1 adv_fw_pi) @ &m : res] =
  Pr[Exper(MI(KEIdeal, KESim(Adv)), Env).main
       (func', adv', fset1 adv_fw_pi) @ &m : res].
proof.
admit.
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
by rewrite (Exper_KEReal_KERealSimp func adv &m) //
           (Exper_KERealSimp_GOptHashing_KERealSimpHashingAdv
            func adv &m) //
           -(RH.GNonOptHashing_GOptHashing KERealSimpHashingAdv &m)
           (KERealSimpHashingAdv_NonOptHashing_DDH1_DDH_Adv
            func adv &m) //
           -(Exper_KEHybrid_KEIdeal_KESim func adv &m) //
           -(KEHybridHashingAdv_OptHashing_Exper_KEHybrid func adv &m) //
           -(RH.GNonOptHashing_GOptHashing KEHybridHashingAdv &m) //
           -(DDH2_DDH_Adv_KEHybridHashingAdv_NonOptHashing
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

end KeyExchange.

(*********************** Secure Message Communication *************************)

theory SMC.

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

end SMC.
