(* KeysExponentsAndPlaintexts.ec *)

(********************** Keys, Exponents and Plain texts ***********************)

prover [""].  (* no use of SMT provers *)

require import AllCore Distr.
require import UCBasicTypes.

(*************************** Begin Theory Parameters **************************)

(* group of keys *)

type key.

op (^^) : key -> key -> key.  (* binary operation *)

op kid : key.  (* identity *)

op kinv : key -> key.  (* inverse *)

axiom kmulA (x y z : key) : x ^^ y ^^ z = x ^^ (y ^^ z).

axiom kid_l (x : key) : kid ^^ x = x.

axiom kid_r (x : key) : x ^^ kid = x.

axiom kinv_l (x : key) : kinv x ^^ x = kid.

axiom kinv_r (x : key) : x ^^ kinv x = kid.

(* commutative semigroup of exponents *)

type exp.

op e : exp.  (* some exponent *)

op ( * ) : exp -> exp -> exp.  (* multiplication *)

axiom mulC (q r : exp) : q * r = r * q.

axiom mulA (q r s : exp) : q * r * s = q * (r * s).

op epdp_exp_univ : (exp, univ) epdp.  (* EPDP from exp to univ *)

axiom valid_epdp_exp_univ : valid_epdp epdp_exp_univ.

(* full (every element has non-zero weight), uniform (all elements
   with non-zero weight have same weight) and lossless (sum of all
   weights is 1%r) distribution over exp

   consequently exp has only finitely many elements *)

op dexp : exp distr.

axiom dexp_fu  : is_full dexp.
axiom dexp_uni : is_uniform dexp.
axiom dexp_ll  : is_lossless dexp.

(* connection between key and exp, via generator key and
   exponentiation operation *)

op g : key.  (* generator *)

op (^) : key -> exp -> key.  (* exponentiation *)

axiom double_exp_gen (q1 q2 : exp) : (g ^ q1) ^ q2 = g ^ (q1 * q2).

(* the following axioms say that each key is uniquely generated from g
   by exponentiation *)

axiom gen_surj (x : key) : exists (q : exp), x = g ^ q.

axiom gen_inj (q r : exp) : g ^ q = g ^ r => q = r.

(* plain texts, with an EPDP to key *)

type text.

op epdp_text_key : (text, key) epdp.  (* EPDP from text to key *)

axiom valid_epdp_text_key : valid_epdp epdp_text_key.

(************************** End of Theory Parameters **************************)

(* simplification hints involving theory parameter axioms *)

hint simplify valid_epdp_exp_univ.
hint simplify dexp_ll.
hint simplify valid_epdp_text_key.

(* common simplifications needed in security proofs suitable
   for use in automated rewriting: *)

lemma one_time (x y : key) :
  x ^^ y ^^ kinv y = x.
proof.
by rewrite kmulA kinv_r kid_r.
qed.

hint simplify [reduce] one_time.

(* we can define a bijection between exp and key *)

op gen (q : exp) : key = g ^ q.

op gen_rel (x : key) (q : exp) : bool = x = g ^ q.

op log (x : key) : exp = choiceb (gen_rel x) e.

lemma gen_log : cancel gen log.
proof.
rewrite /gen /log /cancel => q.
have choice_g2q := choicebP (gen_rel (g ^ q)) e.
have /choice_g2q @/gen_rel /gen_inj {2}-> // :
  exists (q' : exp), gen_rel (g ^ q) q'
  by rewrite /gen_rel; by exists q.
qed.

lemma log_gen : cancel log gen.
proof.
rewrite /gen /log /cancel => x.
have @/gen_rel <- // := choicebP (gen_rel x) e.
rewrite gen_surj.
qed.

lemma double_exp (x : key, q1 q2 : exp) :
  (x ^ q1) ^ q2 = x ^ (q1 * q2).
proof.
have -> : x = g ^ log x.
  by rewrite -/(gen (log x)) log_gen.
by rewrite !double_exp_gen mulA.
qed.

(* now we can combine our one_time lemma with Diffie-Hellman: *)

lemma one_time_dh (x : key, q1 q2 : exp) :
  x ^^ (g ^ q2 ^ q1) ^^ kinv (g ^ q1 ^ q2) = x.
proof.
have -> : g ^ q1 ^ q2 = g ^ q2 ^ q1.
  by rewrite 2!double_exp mulC.
by rewrite one_time.
qed.

hint simplify [reduce] one_time_dh.

(* isomorphism of exp for use with rnd tactic in real/ideal security
   proof *)

op pad_iso_l (t : text, q : exp) : exp =
  log (epdp_text_key.`enc t ^^ (g ^ q)).

op pad_iso_r (t : text, q : exp) : exp =
  log (kinv (epdp_text_key.`enc t) ^^ (g ^ q)).

lemma pad_iso_lr (t : text) : cancel (pad_iso_l t) (pad_iso_r t).
proof.
rewrite /cancel /pad_iso_l /pad_iso_r => q.
by rewrite -/(gen q) -/(gen (log (epdp_text_key.`enc t ^^ (g ^ q))))
   log_gen -kmulA kinv_l kid_l gen_log.
qed.

lemma pad_iso_rl (t : text) : cancel (pad_iso_r t) (pad_iso_l t).
proof.
rewrite /cancel /pad_iso_l /pad_iso_r => q.
by rewrite -/(gen q) -/(gen (log (kinv (epdp_text_key.`enc t) ^^ gen q)))
           log_gen -kmulA kinv_r kid_l gen_log.
qed.

(* lemma for connecting real and ideal games in security proof *)

lemma gen_to_pad_iso_l_eq (t : text, q : exp) :
  g ^ (pad_iso_l t q) = epdp_text_key.`enc t ^^ (g ^ q).
proof.
rewrite /pad_iso_l.
have -> :
  g ^ log (epdp_text_key.`enc t ^^ (g ^ q)) =
  gen (log (epdp_text_key.`enc t ^^ (g ^ q))) by rewrite /gen.
by rewrite log_gen.
qed.

(* EPDP from key to univ *)

op [opaque smt_opaque] epdp_key_univ : (key, univ) epdp =
  epdp_comp epdp_exp_univ (epdp_bijection log gen).

lemma valid_epdp_key_univ : valid_epdp epdp_key_univ.
proof.
rewrite /epdp_key_univ.
rewrite !epdp 1:log_gen gen_log.
qed.

hint simplify valid_epdp_key_univ.

(* EPDP from text to univ *)

op [opaque smt_opaque] epdp_text_univ : (text, univ) epdp =
  epdp_comp epdp_key_univ epdp_text_key.

lemma valid_epdp_text_univ : valid_epdp epdp_text_univ.
proof.
rewrite /epdp_text_univ !epdp.
qed.

hint simplify valid_epdp_text_univ.

(* EPDP between port * port and univ *)

op [opaque smt_opaque] epdp_port_port_univ : (port * port, univ) epdp =
  epdp_pair_univ epdp_port_univ epdp_port_univ.

lemma valid_epdp_port_port_univ :
  valid_epdp epdp_port_port_univ.
proof.
by rewrite /epdp_port_port_univ.
qed.

hint simplify valid_epdp_port_port_univ.

(* EPDP between port * port * key and univ *)

op [opaque smt_opaque] epdp_port_port_key_univ : (port * port * key, univ) epdp =
  epdp_tuple3_univ epdp_port_univ epdp_port_univ epdp_key_univ.

lemma valid_epdp_port_port_key_univ :
  valid_epdp epdp_port_port_key_univ.
proof.
by rewrite /epdp_port_port_key_univ.
qed.

hint simplify valid_epdp_port_port_key_univ.
