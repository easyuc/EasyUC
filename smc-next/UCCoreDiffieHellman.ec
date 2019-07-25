(* UCCoreDiffieHellman.ec *)

prover quorum=2 ["Alt-Ergo" "Z3"].

require import AllCore Distr.
require UCCore DDH.

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

(* full (every element has non-zero weight), uniform (all elements
   with non-zero weight have same weight) and lossless (sum of all
   weights is 1%r) distribution over exp

   consequently exp has only finitely many elements *)

op dexp : exp distr.

axiom dexp_fu : is_full dexp.
axiom dexp_uni : is_uniform dexp.
axiom dexp_ll : is_lossless dexp.

(* connection between key and exp, via generator key and
   exponentiation operation *)

op g : key.  (* generator *)

op (^) : key -> exp -> key.  (* exponentiation *)

axiom double_exp_gen (q1 q2 : exp) : (g ^ q1) ^ q2 = g ^ (q1 * q2).

(* the following axioms say that each key is uniquely generated from g
   by exponentiation *)

axiom gen_surj (x : key) : exists (q : exp), x = g ^ q.

axiom gen_inj (q r : exp) : g ^ q = g ^ r => q = r.

(* plain texts, with injection into keys, and partial projection back *)

type text.

op inj  : text -> key.  (* injection *)
op proj : key -> text option.  (* partial projection *)

axiom inj_inj (t s : text) : inj t = inj s => t = s.

axiom proj_inj_out (x : key, t : text) : proj x = None => inj t <> x.

axiom proj_inj_in (x : key, t : text) : proj x = Some t => inj t = x.

(* consequences of axioms *)

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
have -> : x = g ^ log x
  by rewrite -/(gen (log x)) log_gen.
by rewrite !double_exp_gen mulA.
qed.

lemma proj_injK (t : text) : proj (inj t) = Some t.
proof.
case (proj (inj t) = None).
by have := (proj_inj_out (inj t) t).
move => /some_oget /proj_inj_in /inj_inj {2}<-.
have inj_proj_t_ne_none : proj (inj t) <> None
  by have := (proj_inj_out (inj t) t).
by rewrite -some_oget.
qed.

(******************** Decisional Diffie-Hellman Assumption ********************)

clone export DDH as DDH' with
  type key <- key,
  op (^^) <- (^^),
  op kid <- kid,
  op kinv <- kinv,
  type exp <- exp,
  op e <- e,
  op ( * ) <- ( * ),
  op dexp <- dexp,
  op g <- g,
  op (^) <- (^)
proof *.
realize kmulA. apply kmulA. qed.
realize kid_l. apply kid_l. qed.
realize kid_r. apply kid_r. qed.
realize kinv_l. apply kinv_l. qed.
realize kinv_r. apply kinv_r. qed.
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
  | BaseKey of key
  | BaseText of text
].

op dec_base_exp : base -> exp option = get_as_BaseExp.

lemma enc_dec_base_exp (q : exp) :
  dec_base_exp (BaseExp q) = Some q.
proof. done. qed.

lemma dec_enc_base_exp (bse : base, q : exp) :
  dec_base_exp bse = Some q =>
  bse = BaseExp q.
proof. by case bse. qed.

op is_base_exp (bse : base) : bool =
     dec_base_exp bse <> None.

lemma is_base_exp (q : exp) :
  is_base_exp (BaseExp q).
proof. done. qed.

op dec_base_key : base -> key option = get_as_BaseKey.

lemma enc_dec_base_key (x : key) :
  dec_base_key (BaseKey x) = Some x.
proof. done. qed.

lemma dec_enc_base_key (bse : base, x : key) :
  dec_base_key bse = Some x =>
  bse = BaseKey x.
proof. by case bse. qed.

op is_base_key (bse : base) : bool =
     dec_base_key bse <> None.

lemma is_base_key (x : key) :
  is_base_key (BaseKey x).
proof. done. qed.

op dec_base_text : base -> text option = get_as_BaseText.

lemma enc_dec_base_text (x : text) :
  dec_base_text (BaseText x) = Some x.
proof. done. qed.

lemma dec_enc_base_text (bse : base, x : text) :
  dec_base_text bse = Some x =>
  bse = BaseText x.
proof. by case bse. qed.

op is_base_text (bse : base) : bool =
     dec_base_text bse <> None.

lemma is_base_text (x : text) :
  is_base_text (BaseText x).
proof. done. qed.

clone export UCCore as UCCore' with
  type base <- base
proof *.
(* nothing to realize *)
