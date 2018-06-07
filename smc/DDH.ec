(* DDH.h *)

(* Decisional Diffie-Hellman Assumption *)

prover [""].  (* no provers *)

require import AllCore Distr.

(***************************** Exponents and Keys *****************************)

(* we minimally axiomatize two types and associated operators

   a type key of keys, equipped with a generator g

   a type exp of exponents equipped with an element e (about which
   nothing is assumed), a commutative multiplication operator ( * ),
   and a full, uniform and lossless distribution over exp

   key and exp are connected via an exponentiation operator (^) of
   type key -> exp -> key with the property that every element of
   key is uniquely generated using exponentiation from g *)

type exp.  (* exponents *)

op e : exp.  (* some exponent *)

op ( * ) : exp -> exp -> exp.  (* multiplication *)

axiom mulC (q r : exp) : q * r = r * q.

(* full, uniform and lossless distribution over exp - which implies
   that exp is finite *)

op dexp : exp distr.

axiom dexp_fu : is_full dexp.
axiom dexp_uni : is_uniform dexp.
axiom dexp_ll : is_lossless dexp.

type key.  (* keys *)

op g : key.  (* generator *)

op (^) : key -> exp -> key.  (* exponentiation *)

(* the following axioms say that each key is uniquely generated from g
   by exponentiation *)

axiom gen_surj (x : key) : exists (q : exp), x = g ^ q.

axiom gen_inj (q r : exp) : g ^ q = g ^ r => q = r.

(******************** Decisional Diffie-Hellman Assumption ********************)

(* DDH Adversary *)

module type DDH_ADV = {
  proc * main(x1 x2 x3 : key) : bool
}.

module DDH1 (Adv : DDH_ADV) = {
  proc main() : bool = {
    var b : bool; var u1, u2 : exp;
    u1 <$ dexp; u2 <$ dexp;
    b <@ Adv.main(g ^ u1, g ^ u2, g ^ (u1 * u2));
    return b;
  }
}.
  
module DDH2 (Adv : DDH_ADV) = {
  proc main() : bool = {
    var b : bool; var u1, u2, u3 : exp;
    u1 <$ dexp; u2 <$ dexp; u3 <$ dexp;
    b <@ Adv.main(g ^ u1, g ^ u2 , g ^ u3);
    return b;
  }
}.

(* the *advantage* of a DDH adversary Adv is

   `|Pr[DDH1(Adv).main() @ &m : res] - Pr[DDH2(Adv).main() @ &m : res]|

   this will be negligible under certain assumptions about exp, key, *,
   ^ and Adv (including that Adv doesn't compute the inverse of
   fun q => g ^ q *)
