(* Hybrid Lemma Plus Example Application *)

require import AllCore Real StdOrder Distr.
import RealOrder.

module type T = {
  proc main(n : int) : bool
}.

lemma hybrid (p : real) (m : int) (M <: T) &m :
  0%r <= p => 1 <= m =>
  (forall (i : int) &m,
   1 <= i < m => 
   `|Pr[M.main(i) @ &m : res] - Pr[M.main(i + 1) @ &m : res]| <= p) =>
  `|Pr[M.main(1) @ &m : res] - Pr[M.main(m) @ &m : res]| <= m%r * p.
proof.
move => ge0_p ge1_m step.
have H :
  forall (i : int),
  0 <= i => 1 <= i <= m =>
  `|Pr[M.main(1) @ &m : res] - Pr[M.main(i) @ &m : res]| <= i%r * p.
  elim => [// | i ge0_i IH [_ i_plus1_le_m]].
  case (i = 0) => [-> /= | ne0_i].
  rewrite ger0_norm // ge0_p.
  rewrite fromintD Domain.mulrDl /=.
  rewrite (ler_trans
           (`|Pr[M.main(1) @ &m : res] - Pr[M.main(i) @ &m : res]| +
            `|Pr[M.main(i) @ &m : res] - Pr[M.main(i + 1) @ &m : res]|)).
  rewrite RealOrder.ler_dist_add.
  rewrite ler_add 1:IH 1:/# step /#.
by rewrite H // (IntOrder.ler_trans 1).
qed.

(* example *)

op n : {int | 1 <= n} as ge1_n.

type t.  (* we want t to have 2 ^ n elements, including def *)

op def : t.

op dt : t distr.

axiom dt_ll : is_lossless dt.

axiom mu1_dt (x : t) : mu1 dt x = 1%r / (2 ^ n)%r.

lemma dt_uniform : is_uniform dt.
proof.
move => x y _ _. by rewrite !mu1_dt.
qed.

lemma dt_full : is_full dt.
proof.
move => x.
by rewrite supportP mu1_dt gtr_eqF 1:divr_gt0 //
           lt_fromint IntOrder.expr_gt0.
qed.

op m : {int | 1 <= m} as ge1_m.

module GReal = {
  proc main() : bool = {
    var b <- true;
    var i : int <- 1;
    var x : t;
    while (i < m) {
      x <$ dt;
      if (x = def) {
        b <- false;
      }
      i <- i + 1;
    }
    return b;
  }
}.

module GIdeal = {
  proc main() : bool = {
    return true;
  }
}.

(* we want to prove:

lemma GReal_GIdeal &m :
  `|Pr[GReal.main() @ &m : res] - Pr[GIdeal.main() @ &m : res]| <=
  m%r * (1%r / (2 ^ n)%r).
*)

module GHybrid = {
  proc main(i : int) : bool = {
    var b <- true;
    var x : t;
    (* start from i: *)
    while (i < m) {
      x <$ dt;
      if (x = def) {
        b <- false;
      }
      i <- i + 1;
    }
    return b;
  }
}.

lemma GReal_GHybrid_1 &m :
  Pr[GReal.main() @ &m : res] = Pr[GHybrid.main(1) @ &m : res].
proof.
byequiv => //.
proc.
seq 2 1 : (={b, i} /\ i{1} = 1); first auto.
sim.
qed.

lemma GHybrid_m &m :
  Pr[GHybrid.main(m) @ &m : res] = Pr[GIdeal.main() @ &m : res].
proof.
byequiv => //.
proc; sp.
rcondf{1} 1; auto.
qed.

(* we use upto bad reasoning *)

module GBad1 = {
  var bad : bool  (* bad event *)

  proc main(i : int) : bool = {
    var b <- true;
    var x : t;
    bad <- false;
    x <$ dt;
    if (x = def) {
      bad <- true;  (* bad event *)
      b <- false;   (* assignment to b *)
    }
    i <- i + 1;
    while (i < m) {  (* rest as usual *)
      x <$ dt;
      if (x = def) {
        b <- false;
      }
      i <- i + 1;
    }
    return b;
  }
}.

module GBad2 = {
  var bad : bool

  proc main(i : int) : bool = {
    var b <- true;
    var x : t;
    bad <- false;
    x <$ dt;
    if (x = def) {
      bad <- true;  (* bad event *)
      (* but no assignment to b *)
    }
    i <- i + 1;
    while (i < m) {  (* rest as usual *)
      x <$ dt;
      if (x = def) {
        b <- false;
      }
      i <- i + 1;
    }
    return b;
  }
}.

lemma GHybrid_step (i' : int) &m :
  1 <= i' < m =>
  `|Pr[GHybrid.main(i') @ &m : res] - Pr[GHybrid.main(i' + 1) @ &m : res]| <=
  1%r / (2 ^ n)%r.
proof.
move => [ge1_i' lt_i'_m]. 
have -> :
  Pr[GHybrid.main(i') @ &m : res] = Pr[GBad1.main(i') @ &m : res].
  byequiv => //.
  proc; sp 1 2.
  rcondt{1} 1; first auto.
  sim.
have -> :
  Pr[GHybrid.main(i' + 1) @ &m : res] = Pr[GBad2.main(i') @ &m : res].
  byequiv => //.
  proc; sp 1 2.
  seq 0 1 : (={b} /\ i{1} = i{2} + 1).
  rnd{2}; skip; progress.
  rewrite dt_ll.
  if{2}; sp; sim.
rewrite (ler_trans Pr[GBad2.main(i') @ &m : GBad2.bad]).
byequiv
  (_ :
   ={i} ==>
   GBad1.bad{1} = GBad2.bad{2} /\ (! GBad2.bad{2} => ={res})) :
  GBad1.bad => //.
proc.
seq 5 5 :
  (GBad1.bad{1} = GBad2.bad{2} /\ ={i} /\
   (!GBad2.bad{2} => ={b})); first auto.
case (GBad1.bad{1}).
while (={i}); auto.
while (={i, b}); auto; smt().
smt().
byphoare => //.
proc; sp.
seq 2 :
  GBad2.bad
  (1%r / (2 ^ n)%r)
  1%r
  (1%r - (1%r / (2 ^ n)%r))
  0%r.
auto.
wp.
rnd (pred1 def).
auto; progress.
by rewrite mu1_dt.
conseq (_ : _ ==> _ : = 1%r).
while (true) (m - i) => [z |].
auto; progress.
by rewrite dt_ll.
smt().
auto; smt().
hoare.
while (true); auto.
trivial.
qed.

lemma GHybrid_1_m &m :
  `|Pr[GHybrid.main(1) @ &m : res] - Pr[GHybrid.main(m) @ &m : res]| <=
  m%r * (1%r / (2 ^ n)%r).
proof.
rewrite (hybrid _ _ GHybrid).
by rewrite divr_ge0 // le_fromint IntOrder.expr_ge0.
rewrite ge1_m.
apply GHybrid_step.
qed.

lemma GReal_GIdeal &m :
  `|Pr[GReal.main() @ &m : res] - Pr[GIdeal.main() @ &m : res]| <=
  m%r * (1%r / (2 ^ n)%r).
proof.
rewrite (GReal_GHybrid_1 &m) -(GHybrid_m &m) (GHybrid_1_m &m).
qed.
