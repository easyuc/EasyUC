(* KeysExponentsAndPlainTexts.ec *)

prover [""].  (* no use of SMT provers *)

require import AllCore Distr.
require import UCBasicTypes.

(********************** Keys, Exponents and Plain texts ***********************)

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

hint simplify valid_epdp_exp_univ.  (* so simplify and smt() can use axiom *)

(* full (every element has non-zero weight), uniform (all elements
   with non-zero weight have same weight) and lossless (sum of all
   weights is 1%r) distribution over exp

   consequently exp has only finitely many elements *)

op dexp : exp distr.

axiom dexp_fu  : is_full dexp.
axiom dexp_uni : is_uniform dexp.
axiom dexp_ll  : is_lossless dexp.

hint simplify dexp_ll.

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

hint simplify valid_epdp_text_key.

(* consequences of axioms *)

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
