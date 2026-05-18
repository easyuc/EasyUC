(* DDH.h *)

(* Decisional Diffie-Hellman Assumption *)

prover [""].  (* no provers *)

require import AllCore Distr KeysExponentsAndPlaintexts.

(******************** Decisional Diffie-Hellman Assumption ********************)

(* DDH Adversary *)

module type DDH_ADV = {
  proc main(k1 k2 k3 : key) : bool
}.

module DDH1 (Adv : DDH_ADV) = {
  proc main() : bool = {
    var b : bool; var q1, q2 : exp;
    q1 <$ dexp; q2 <$ dexp;
    b <@ Adv.main(g ^ q1, g ^ q2, g ^ (q1 * q2));
    return b;
  }
}.
  
module DDH2 (Adv : DDH_ADV) = {
  proc main() : bool = {
    var b : bool; var q1, q2, q3 : exp;
    q1 <$ dexp; q2 <$ dexp; q3 <$ dexp;
    b <@ Adv.main(g ^ q1, g ^ q2 , g ^ q3);
    return b;
  }
}.

(* the *advantage* of a DDH adversary Adv is

   `|Pr[DDH1(Adv).main() @ &m : res] - Pr[DDH2(Adv).main() @ &m : res]|

   this will be negligible under certain assumptions about the group
   key, the commutative semigroup exp, and the efficiency of Adv
   (including that Adv doesn't compute the inverse of fun q => g ^
   q *)
