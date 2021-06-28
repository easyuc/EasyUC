(* random sampling lemma for permutations *)

require import AllCore Distr.

(* a type t, forward and backward operators on t, plus the axioms
   saying: going forward then backward is the identity; going backward
   then forward is the identity *)

type t.

op forw : t -> t.

op back : t -> t.

axiom forw_back (x : t) : back (forw x) = x.

axiom back_forw (x : t) : forw (back x) = x.

(* a distribution on t that is lossless (the sum of the weights of all
   elements of t is 1%r), full (every element of t has a non-zero
   weight), and uniform (all elements have the same weight) *)

op d : t distr.

axiom d_ll : is_lossless d.

axiom d_fu : is_full d.

axiom d_uni : is_uniform d.

(* like what happens in Hyb: *)

module M = {
  proc f() : t * t = {
    var x : t;
    x <$ d;
    return (x, forw x);
  }
}.

(* like what happens in Ideal: *)

module N = {
  proc f() : t * t = {
    var y : t;
    y <$ d;
    return (back y, y);
  }
}.

lemma M_N :
  equiv [M.f ~ N.f : true ==> ={res}].
proof.
proc.
rnd forw back.
auto; progress.
by rewrite back_forw.
rewrite (d_uni yR (back yR)) // 2!d_fu.
rewrite d_fu.
by rewrite forw_back.
qed.
