(* KeysExpsTexts.ec *)

(********************** Keys, Exponents and Plain texts ***********************)

prover [""].  (* no use of SMT provers *)

require import AllCore Distr.
require import UCBasicTypes.
require KeyExp.

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

op [full uniform lossless] dexp : exp distr.

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

(**************************** End Theory Parameters ***************************)

clone export KeyExp as KeyExp' with
  type key         <- key,
  op (^^)          <- (^^),
  op kid           <- kid,
  op kinv          <- kinv,
  type exp         <- exp,
  op e             <- e,
  op ( * )         <- ( * ),
  op epdp_exp_univ <- epdp_exp_univ,
  op dexp          <- dexp,
  op g             <- g,
  op (^)           <- (^)
proof *.
realize kmulA. apply kmulA. qed.
realize kid_l. apply kid_l. qed.
realize kid_r. apply kid_r. qed.
realize kinv_l. apply kinv_l. qed.
realize kinv_r. apply kinv_r. qed.
realize mulC. apply mulC. qed.
realize mulA. apply mulA. qed.
realize valid_epdp_exp_univ. apply valid_epdp_exp_univ. qed.
realize dexp_fu. apply dexp_fu. qed.
realize dexp_uni. apply dexp_uni. qed.
realize dexp_ll. apply dexp_ll. qed.
realize double_exp_gen. apply double_exp_gen. qed.
realize gen_surj. apply gen_surj. qed.
realize gen_inj. apply gen_inj. qed.

(* simplification hint involving theory parameter *)

hint simplify valid_epdp_text_key.

(* version of one_time_dh from KeyExp' but in terms of key and exp,
   not KeyExp'.key and KeyExp'.exp

   this is needed for the decryption to succeed during interpretation *)

lemma one_time_dh (k : key, q1 q2 : exp) :
  k ^^ (g ^ q2 ^ q1) ^^ kinv (g ^ q1 ^ q2) = k.
proof.
trivial.
qed.

(* a simplification hint does not suffice *)
hint rewrite ucdsl_interpreter_hints : one_time_dh.

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

(* EPDP from text to univ *)

op [opaque smt_opaque] epdp_text_univ : (text, univ) epdp =
  epdp_comp epdp_key_univ epdp_text_key.

lemma valid_epdp_text_univ : valid_epdp epdp_text_univ.
proof.
rewrite /epdp_text_univ !epdp.
qed.

hint simplify valid_epdp_text_univ.
