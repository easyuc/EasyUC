(* UCCoreDiffieHellman.ec *)

prover quorum=2 ["Alt-Ergo" "Z3"].

require import AllCore Distr.
require UCCore DDH.

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

clone export DDH as DDH' with
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

clone export UCCore as UCCore' with
  type base <- base
proof *.
(* nothing to realize *)
