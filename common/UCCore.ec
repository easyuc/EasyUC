(* UCCore.ec *)

(* Core UC Definitions and Lemmas *)

prover quorum=2 ["Z3" "Alt-Ergo"].

(* standard theories, encoding and partial decoding pairs (EPDPs), the
   type univ plus a number of EPDPs with target univ, addresses and
   ports *)

require export UCBasicTypes.
require import UCListAux.
require StdOrder.

(* module type used for real protocols and ideal functionalities
   (collectively, "functionalities") *)

(* precondition for functionalities: *)

op func_init_pre (self : addr) : bool = inc self adv.

(* envport0 self adv pt says that pt is part of the environment, not
   the functionality or adversary; it's allowed to be the root port of
   the environment, env_root_port (([], 0)) *)

op envport0 (self : addr, pt : port) : bool =
  ! self <= pt.`1 /\ ! adv <= pt.`1.

module type FUNC = {
  (* initialize functionality telling it its address (self)

     precondition: func_init_pre self *)

  proc init(self : addr) : unit

  (* respond to an incoming message, producing an optional
     outgoing message (None means error)

     messages to a functionality should have destination addresses
     that are >= self

     if Some m' is returned, then the source address of m' should be
     >= self; when m' is a direct message, the destination address should
     satisfy envport self; when m' is an adversarial message, the destination
     port should be (adv, adv_pi), for adv_pi > 0 *)

  proc invoke(m : msg) : msg option
}.

(* module type used for an adversary (including the application of
   a simulator to an adversary) *)

module type ADV = {
  proc init() : unit

  (* messages sent to the adversary should have destination addresses
     equal to adv; the destination port index should be 0 iff the
     message is from the root of the environment; otherwise it should
     be > 0

     see the code for interfaces to understand what will be required
     of outgoing messages from the adversary (for failure to not occur) *)

  proc invoke(m : msg) : msg option
}.

(* module type of interfaces (to environment): consists of
   a functionality part and an adversary part *)

(* precondition: *)

op inter_init_pre (func : addr) : bool = inc func adv.

module type INTER = {
  (* initialize interface, telling it:

       * the address (func) of its functionality part;

       * an incoming message guard (in_guard)

     the interface will initialize its functionality and adversary
     parts

     precondition:

       inter_init_pre func *)

  proc init(func : addr, in_guard : int fset) : unit

  (* respond to an incoming message from the environment, producing an
     optional outgoing message (None means error) *)

  proc invoke(m : msg) : msg option
}.

(* module type of environments, parameterized by interfaces *)

op env_init_pre (func : addr) : bool = inter_init_pre func.

module type ENV (Inter : INTER) = {
  (* start environment, and let it interact with Inter (only via
     Inter.invoke, not via Inter.init), eventually returning a boolean
     judgment

     we have:

       * func is the address of interface's functionality part

     precondition : env_pre func *)

  proc main(func : addr, in_guard : int fset) : bool {Inter.invoke}
}.

(* carry out experiment in which the environment is allowed to
   interact with, and issue a final boolean judgment about, an
   interface, which is first initialized *)

op exper_pre (func : addr) : bool = inter_init_pre func.

lemma exper_pre_ext1 (func ext : addr) :
  exper_pre func => exper_pre (func ++ ext).
proof.
rewrite /exper_pre /inter_init_pre.
move => |> inc_fun_adv.
by apply inc_extl.
qed.

lemma exper_pre_func_nle_env_root_addr (func : addr) :
  exper_pre func => ! func <= env_root_addr.
proof.
smt(inc_nle_l le_trans ge_nil).
qed.

lemma exper_pre_adv_nle_env_root_addr (func : addr) :
  exper_pre func => ! adv <= env_root_addr.
proof.
smt(inc_nle_r le_trans ge_nil).
qed.

module Exper (Inter : INTER, Env : ENV) = {
  module E = Env(Inter)

  (* arguments to main:

       * func is address of interface's functionality part

       * in_guard is the incoming message guard used by the interface
         and supplied to the environment

     precondition:

       exper_pre func adv *)

  proc main(func : addr, in_guard : int fset) : bool = {
    var b : bool;
    Inter.init(func, in_guard);
    b <@ E.main(func, in_guard);
    return b;
  }
}.

(* working with disjoint sets, which will be done in conjunction
   with input guards *)

lemma disjoint_sym (xs ys : 'a fset) :
  disjoint xs ys => disjoint ys xs.
proof.
rewrite !disjointP => disj_xs_ys z z_in_ys.
case (z \in xs) => [z_in_xs | //].
have // : z \notin ys by apply disj_xs_ys.
qed.

lemma disjoint_with_union_implies_disjoint_with_first
      (zs xs ys : 'a fset) :
  disjoint xs (ys `|` zs) => disjoint xs ys.
proof.
rewrite disjointP => disj_xs_union_ys_zs.
rewrite disjointP => x x_in_xs.
have := disj_xs_union_ys_zs x _; first trivial.
by rewrite in_fsetU negb_or.
qed.

lemma disjoint_with_union_implies_disjoint_with_second
      (ys xs zs : 'a fset) :
  disjoint xs (ys `|` zs) => disjoint xs zs.
proof.
rewrite disjointP => disj_xs_union_ys_zs.
rewrite disjointP => x x_in_xs.
have := disj_xs_union_ys_zs x _; first trivial.
by rewrite in_fsetU negb_or.
qed.

lemma disjoint_add_remove (xs ys : 'a fset) :
  disjoint xs ys => (xs `|` ys) `\` ys = xs.
proof.
rewrite disjointP => disj_xs_ys.
rewrite fsetDK eqEsubset.
split => z; rewrite in_fsetD => [[] -> // | z_in_xs].
rewrite z_in_xs /=.
case (z \in ys) => [z_in_ys | //].
have // : z \notin ys by apply disj_xs_ys.
qed.

lemma disjoint_with_disjoint_union_add_first_disjoint_with_second
      (xs ys zs : 'a fset) :
  disjoint xs (ys `|` zs) => disjoint ys zs =>
  disjoint (xs `|` ys) zs.
proof.
rewrite !disjointP => disj_xs_union_ys_zs disj_ys_zs => u.
rewrite in_fsetU => [[u_in_xs | u_in_ys]].
have := disj_xs_union_ys_zs u _; first trivial.
by rewrite in_fsetU negb_or.
by apply disj_ys_zs.
qed.

(* make interface out of functionality and adversary parts *)

(* loop invariant for interface's while loop *)

op mi_loop_invar
     (func : addr, in_guard : int fset,
      r : msg option, m : msg, not_done : bool) : bool =
  inter_init_pre func /\
  (not_done =>
   (m.`1 = Dir /\ func = m.`2.`1 /\ envport func m.`3) \/
   (m.`1 = Adv /\ func <= m.`2.`1 /\ m.`3.`1 = adv /\ 0 < m.`3.`2) \/
   (m.`1 = Adv /\ m.`2.`1 = adv /\
    (func <= m.`3.`1 /\ 0 < m.`2.`2 \/
     m.`3 = env_root_port /\ m.`2.`2 = 0 \/
     envport func m.`3 /\ 0 < m.`2.`2 /\
     m.`2.`2 \in in_guard))) /\
  (! not_done =>
   r = None \/
   (envport0 func (oget r).`2 /\
    ((oget r).`1 = Dir /\ (oget r).`2 <> env_root_port /\
      func = (oget r).`3.`1 \/
     (oget r).`1 = Adv /\ adv = (oget r).`3.`1 /\ 0 <= (oget r).`3.`2 /\
      ((oget r).`2 = env_root_port <=> (oget r).`3.`2 = 0)))).

lemma mi_loop_invar_not_done_imp_dest
      (func : addr, in_guard : int fset,
       m : msg, r : msg option) :
  mi_loop_invar func in_guard r m true =>
  func <= m.`2.`1 \/ m.`2.`1 = adv.
proof.
rewrite /mi_loop_invar; smt(le_refl).
qed.

(* guard for invoke procedure of interface *)

op main_guard (func : addr, in_guard : int fset, m : msg) : bool =
  m.`1 = Dir /\ func = m.`2.`1 /\ envport func m.`3 \/
  m.`1 = Adv /\ m.`2.`1 = adv /\
  (m.`2.`2 = 0 /\ m.`3 = env_root_port \/
   0 < m.`2.`2 /\ m.`2.`2 \in in_guard /\ envport func m.`3).

abstract theory MakeInterface.

module MI (Func : FUNC, Adv : ADV) : INTER = {
  var func : addr
  var in_guard : int fset

  proc init(func_ : addr, in_guard_ : int fset) : unit = {
    func <- func_; in_guard <- in_guard_;
    Func.init(func);
    Adv.init();
  }

  proc after_func(r : msg option) : msg option * msg * bool = {
    var m : msg <- witness;
    var not_done <- true;
    if (r = None) {
      not_done <- false;
    }
    else {
      m <- oget r;  (* next iteration, if any, will use m *)
      if (func <= m.`2.`1 \/ ! func <= m.`3.`1) {
        r <- None; not_done <- false;
      }
      (* else: ! func <= m.`2.`1 /\ func <= m.`3.`1 *)
      elif (m.`1 = Dir) {
        not_done <- false;
        if (adv <= m.`2.`1 \/ m.`2 = env_root_port \/ func <> m.`3.`1) {
          r <- None;
        }
        (* else: envport func m.`2 *)
      }
      (* else: m.`1 = Adv *)
      elif (m.`2.`1 <> adv \/ m.`2.`2 <= 0) {
        r <- None; not_done <- false;
      }
      (* else: m.`2.`1 = adv /\ 0 < m.`2.`2 *)
    }
    return (r, m, not_done);
  }

  proc after_adv(r : msg option) : msg option * msg * bool = {
    var m : msg <- witness;
    var not_done <- true;
    if (r = None) {
      not_done <- false;
    }
    else {
      m <- oget r;  (* next iteration, if any, will use m *)
      if (m.`1 = Dir \/ adv <= m.`2.`1 \/ adv <> m.`3.`1 \/ m.`3.`2 < 0) {
        r <- None; not_done <- false;
      }
      (* else: m.`1 = Adv /\ ! adv <= m.`2.`1 /\ adv = m.`3.`1 /\
         0 <= m.`3.`2 *)
      elif (func <= m.`2.`1) {
        if (m.`3.`2 = 0) {
          r <- None; not_done <- false;
        }
        (* else: 0 < m.`3.`2 *)
      }
      else {  (* envport0 func m.`2 *)
        not_done <- false;
        if (! (m.`3.`2 = 0 <=> m.`2 = env_root_port)) {
          r <- None;
        }
      }
    }
    return (r, m, not_done);
  }

  proc loop(m : msg) : msg option = {
    var r : msg option <- None;
    var not_done : bool <- true;

    while (not_done) {
      if (func <= m.`2.`1) {
        r <@ Func.invoke(m);
        (r, m, not_done) <@ after_func(r);
      }
      else {  (* adv = m.`2.`1 *)
        r <@ Adv.invoke(m);
        (r, m, not_done) <@ after_adv(r);
      }
    }
    return r;
  }

  proc invoke(m : msg) : msg option = {
    var r : msg option;
    if (main_guard func in_guard m) {
      r <@ loop(m);
    }
    else {
      r <- None;
    }
    return r;
  }
}.

(* check that invariant is actually preserved: *)

lemma MI_after_func_hoare (Func <: FUNC) (Adv <: ADV) :
  hoare
  [MI(Func, Adv).after_func :
   inter_init_pre MI.func ==>
   mi_loop_invar MI.func MI.in_guard res.`1 res.`2 res.`3].
proof.
proc; sp 2.
if; first auto.
sp 1.
if; first auto.
if; first sp 1.
auto; smt().
if; first auto.
auto => /> &hr pre r_not_none.
rewrite !negb_or /= not_dir /#.
qed.

lemma MI_after_adv_hoare (Func <: FUNC) (Adv <: ADV) :
  hoare
  [MI(Func, Adv).after_adv :
   inter_init_pre MI.func ==>
   mi_loop_invar MI.func MI.in_guard res.`1 res.`2 res.`3].
proof.
proc; sp 2.
if; first auto.
sp 1.
if; first auto.
if.
if; first auto.
auto => /> &hr pre _.
rewrite !negb_or /= not_dir /#.
sp 1.
if; first auto.
auto => /> &hr pre -> /=.
rewrite /envport0 !negb_or not_dir => [#] -> -> /= -> H /= ->.
rewrite -!eq_iff => -> /=.
by rewrite IntOrder.lerNgt.
qed.

lemma MI_invoke_hoare (Func <: FUNC{-MI}) (Adv <: ADV{-MI}) :
  hoare
  [MI(Func, Adv).invoke :
   inter_init_pre MI.func ==>
   res = None \/
   (envport0 MI.func (oget res).`2 /\
    ((oget res).`1 = Dir /\ (oget res).`2 <> env_root_port /\
      MI.func = (oget res).`3.`1 \/
     (oget res).`1 = Adv /\ adv = (oget res).`3.`1 /\ 0 <= (oget res).`3.`2 /\
      ((oget res).`2 = env_root_port <=> (oget res).`3.`2 = 0)))].
proof.
proc.
if.
inline MI(Func, Adv).loop.
wp; sp.
while (mi_loop_invar MI.func MI.in_guard r0 m0 not_done).
if.
seq 1 : (inter_init_pre MI.func /\ not_done).
call (_ : true); first auto => />.
call (MI_after_func_hoare Func Adv).
auto.
seq 1 : (inter_init_pre MI.func /\ not_done).
call (_ : true); first auto => />.
call (MI_after_adv_hoare Func Adv).
auto.
auto => |> /#.
auto.
qed.

(* phoare lemmas for after_func and after_adv: *)

op after_func_to_env (func : addr, r : msg option) : bool =
  r <> None /\
  (oget r).`1 = Dir /\ envport func (oget r).`2 /\
  func = (oget r).`3.`1.

op after_func_to_adv (func : addr, r : msg option) : bool =
  r <> None /\
  (oget r).`1 = Adv /\ (oget r).`2.`1 = adv /\ 0 < (oget r).`2.`2 /\
  func <= (oget r).`3.`1.

op after_func_error (func : addr, r : msg option) : bool =
  r = None \/
  func <= (oget r).`2.`1 \/
  (oget r).`1 = Dir /\
  (adv <= (oget r).`2.`1 \/ (oget r).`2 = env_root_port \/
   (oget r).`3.`1 <> func) \/
  (oget r).`1 = Adv /\
  ((oget r).`2.`1 <> adv \/ (oget r).`2.`2 <= 0 \/
   ! (func <= (oget r).`3.`1)).

lemma after_func_disj (func : addr, r : msg option) :
  after_func_to_env func r \/
  after_func_to_adv func r \/
  after_func_error func r.
proof.
rewrite /after_func_to_env /after_func_to_adv /after_func_error
        /envport /envport0.
case (r = None) => // _ /=.
case ((oget r).`1) => //=; smt().
qed.

lemma MI_after_func_to_env (Func <: FUNC) (Adv <: ADV)
      (r' : msg option) :
  phoare
  [MI(Func, Adv).after_func :
   inter_init_pre MI.func /\ r = r' /\
   after_func_to_env MI.func r ==>
   res.`1 = r' /\ res.`1 = Some res.`2 /\ !res.`3] = 1%r.
proof.
proc; auto; smt(some_oget le_refl).
qed.

lemma MI_after_func_to_adv (Func <: FUNC) (Adv <: ADV)
      (r' : msg option) :
  phoare
  [MI(Func, Adv).after_func :
   inter_init_pre MI.func /\ r = r' /\
   after_func_to_adv MI.func r ==>
   res.`1 = r' /\ res.`1 = Some res.`2 /\ res.`3] = 1%r.
proof.
proc; auto; smt(inc_nle_l some_oget).
qed.

lemma MI_after_func_error (Func <: FUNC) (Adv <: ADV) :
  phoare
  [MI(Func, Adv).after_func :
   inter_init_pre MI.func /\ after_func_error MI.func r ==>
   res.`1 = None /\ !res.`3] = 1%r.
proof.
proc; auto; smt().
qed.

op after_adv_to_env (func : addr, r : msg option) : bool =
   r <> None /\
   (oget r).`1 = Adv /\ ! func <= (oget r).`2.`1 /\
   ! adv <= (oget r).`2.`1 /\ adv = (oget r).`3.`1 /\
   0 <= (oget r).`3.`2 /\
   ((oget r).`2 = env_root_port <=> (oget r).`3.`2 = 0).

op after_adv_to_func (func : addr, r : msg option) : bool =
  r <> None /\
  (oget r).`1 = Adv /\ func <= (oget r).`2.`1 /\
  (oget r).`3.`1 = adv /\ 0 < (oget r).`3.`2.

op after_adv_error (func : addr, r : msg option) : bool =
   (r = None \/
    (oget r).`1 = Dir \/
    adv <= (oget r).`2.`1 \/
    adv <> (oget r).`3.`1 \/ (oget r).`3.`2 < 0 \/
    (func <= (oget r).`2.`1 /\ (oget r).`3.`2 = 0) \/
    (! func <= (oget r).`2.`1 /\
     ! ((oget r).`3.`2 = 0 <=> (oget r).`2 = env_root_port))).

lemma after_adv_disj (func : addr, r : msg option) :
  after_adv_to_env func r  \/
  after_adv_to_func func r \/
  after_adv_error func r.
proof.
rewrite /after_adv_to_env /after_adv_to_func /after_adv_error
        /envport /envport0.
case (r = None) => // _ /=.
case ((oget r).`1) => // /=.
smt().
qed.

lemma after_adv_to_env_ext_not_to_func
      (func : addr, r : msg option, i : int) :
  after_adv_to_env func r =>
  ! after_adv_to_func (func ++ [i]) r.
proof.
move => aate_func_r.
rewrite /after_adv_to_func !negb_and.
smt(not_le_ext).
qed.

lemma after_adv_to_env_ext_not_error
      (func : addr, r : msg option, i : int) :
  after_adv_to_env func r =>
  ! after_adv_error (func ++ [i]) r.
proof.
move => aate_func_r.
rewrite /after_adv_error !negb_or.
smt(not_le_ext).
qed.

lemma after_adv_to_env_ext
      (func : addr, r : msg option, i : int) :
  after_adv_to_env func r =>
  after_adv_to_env (func ++ [i]) r.
proof.
move => aate_func_r.
have [// | [A | B]] := after_adv_disj (func ++ [i]) r.
smt(after_adv_to_env_ext_not_to_func).
smt(after_adv_to_env_ext_not_error).
qed.

lemma after_adv_to_func_ext_not_error
      (func : addr, r : msg option, i : int) :
  inc func adv => after_adv_to_func func r =>
  ! after_adv_error (func ++ [i]) r.
proof.
move => inc_func_adv aatf_func_r.
rewrite /after_adv_error !negb_or /=.
smt(inc_le1_not_rl ge_nil le_trans inc_nle_l).
qed.

lemma after_adv_to_func_ext_to_func_or_env
      (func : addr, r : msg option, i : int) :
  inc func adv => after_adv_to_func func r =>
  after_adv_to_func (func ++ [i]) r \/
  after_adv_to_env (func ++ [i]) r.
proof.
move => inc_func_adv aatf_func_r.
smt(after_adv_to_func_ext_not_error after_adv_disj).
qed.

lemma after_adv_error_ext_not_to_func
      (func : addr, r : msg option, i : int) :
  inc func adv => after_adv_error func r =>
  ! after_adv_to_func (func ++ [i]) r.
proof.
move => inc_func_adv.
rewrite /after_adv_error /after_adv_to_func !negb_and /=.
smt(inc_extl inc_le2_not_lr not_le_ext).
qed.

lemma after_adv_error_ext_error_or_to_env
      (func : addr, r : msg option, i : int) :
  inc func adv => after_adv_error func r =>
  after_adv_error (func ++ [i]) r \/ after_adv_to_env (func ++ [i]) r.
proof.
move => inc_func_adv aae_func_r.
smt(after_adv_error_ext_not_to_func after_adv_disj).
qed.

lemma MI_after_adv_to_env (Func <: FUNC) (Adv <: ADV)
      (r' : msg option) :
  phoare
  [MI(Func, Adv).after_adv :
   inter_init_pre MI.func /\ r = r' /\
   after_adv_to_env MI.func r ==>
   res.`1 = r' /\ res.`1 = Some res.`2 /\ !res.`3] = 1%r.
proof.
proc; auto; smt().
qed.

lemma MI_after_adv_to_func (Func <: FUNC) (Adv <: ADV)
      (r' : msg option) :
  phoare
  [MI(Func, Adv).after_adv :
   inter_init_pre MI.func /\ r = r' /\
   after_adv_to_func MI.func r ==>
   res.`1 = r' /\ res.`1 = Some res.`2 /\ res.`3] = 1%r.
proof.
proc; auto; smt(oget_some some_oget inc_le1_not_rl IntOrder.lerNgt).
qed.

lemma MI_after_adv_error (Func <: FUNC) (Adv <: ADV) :
  phoare
  [MI(Func, Adv).after_adv :
   inter_init_pre MI.func /\ after_adv_error MI.func r ==>
   res.`1 = None /\ !res.`3] = 1%r.
proof.
proc; auto; smt().
qed.

(* transitivity of security, proved using the triangular inequality *)

lemma security_trans
      (F1 <: FUNC)  (F2 <: FUNC)  (F3 <: FUNC)
      (Adv1 <: ADV) (Adv2 <: ADV) (Adv3 <: ADV)
      (Env <: ENV)
      (func : addr) (guard : int fset) (b1 b2 : real) &m :
`|Pr[Exper(MI(F1, Adv1), Env).main(func, guard) @ &m : res] -
  Pr[Exper(MI(F2, Adv2), Env).main(func, guard) @ &m : res]| <= b1 =>
`|Pr[Exper(MI(F2, Adv2), Env).main(func, guard) @ &m : res] -
  Pr[Exper(MI(F3, Adv3), Env).main(func, guard) @ &m : res]| <= b2 =>
`|Pr[Exper(MI(F1, Adv1), Env).main(func, guard) @ &m : res] -
  Pr[Exper(MI(F3, Adv3), Env).main(func, guard) @ &m : res]| <= b1 + b2.
move => first second.
rewrite
  (RealOrder.ler_trans
   (`|Pr[Exper(MI(F1, Adv1), Env).main(func, guard) @ &m : res] -
      Pr[Exper(MI(F2, Adv2), Env).main(func, guard) @ &m : res]| +
    `|Pr[Exper(MI(F2, Adv2), Env).main(func, guard) @ &m : res] -
      Pr[Exper(MI(F3, Adv3), Env).main(func, guard) @ &m : res]|))
  1:RealOrder.ler_dist_add RealOrder.ler_add //.
qed.

end MakeInterface.

(* the top-level interface in theorems *)

clone MakeInterface as MakeInt
proof *.

module MI = MakeInt.MI.

(* Converting Hoare lemmas about invariants and termination metrics
   for functionalities into equiv lemmas

   lemmas for invoke have three forms, one of them restricting
   destination adversarial port indices to a single index (and also
   restricting the source port index to 1), one restricting them to a
   finite set of indices, and one making no restriction on them *)

(* init lemma for use with any functionality, Fun, with an invariant
   for which we know the corresponding hoare lemma *)

lemma init_invar_hoare_implies_equiv (Fun <: FUNC)
      (invar : glob Fun -> bool) :
  hoare [Fun.init : true ==> invar (glob Fun)] =>
  equiv
  [Fun.init ~ Fun.init :
   ={self, glob Fun} ==>
   ={glob Fun} /\ invar (glob Fun){1}].
proof.
move => init_hoare.
conseq
  (_ : ={self, glob Fun} ==> ={glob Fun})
  (_ : true ==> invar (glob Fun))
  (_ : true ==> true) => //.
sim.
qed.

(* invoke lemma for use with any functionality, Fun, with an invariant
   and termination metric making no restriction on destination
   adversarial port indices, for which we know the corresponding hoare
   lemma *)

lemma invoke_term_metric_hoare_implies_equiv (Fun <: FUNC)
      (invar : glob Fun -> bool, tm : glob Fun -> int, n : int) :
  hoare
  [Fun.invoke :
   invar (glob Fun) /\ tm (glob Fun) = n ==>
   invar (glob Fun) /\
   (res <> None => tm (glob Fun) < n)] =>
  equiv
  [Fun.invoke ~ Fun.invoke :
   ={m, glob Fun} /\ invar (glob Fun){1} /\
   tm (glob Fun){1} = n ==>
   ={res, glob Fun} /\ invar (glob Fun){1} /\
   (res{1} <> None => tm (glob Fun){1} < n)].
proof.
move => invoke_hoare.
conseq
  (_ : ={m, glob Fun} ==> ={glob Fun, res})
  (_ :
   invar (glob Fun) /\ tm (glob Fun) = n ==>
   invar (glob Fun) /\
   (res <> None => tm (glob Fun) < n))
  (_ : true ==> true) => //.
sim.
qed.

(* invoke lemma for use with any functionality, Fun, with an invariant
   and termination metric restricting outgoing adversarial messages to
   have a specified destination port index and also have the source
   port index 1, for which we know the corresponding hoare lemma

   this is for use with ideal functionalities *)

lemma invoke_term_metric_adv_pi_hoare_implies_equiv (Fun <: FUNC)
      (invar : glob Fun -> bool, tm : glob Fun -> int,
       n : int, adv_pi : int) :
  hoare
  [Fun.invoke :
   invar (glob Fun) /\ tm (glob Fun) = n ==>
   invar (glob Fun) /\
   (res <> None =>
    tm (glob Fun) < n /\
    ((oget res).`1 = Adv =>
     (oget res).`2.`2 = adv_pi /\ (oget res).`3.`2 = 1))] =>
  equiv
  [Fun.invoke ~ Fun.invoke :
   ={m, glob Fun} /\ invar (glob Fun){1} /\
   tm (glob Fun){1} = n ==>
   ={res, glob Fun} /\ invar (glob Fun){1} /\
   (res{1} <> None =>
    tm (glob Fun){1} < n /\
    ((oget res{1}).`1 = Adv =>
     (oget res{1}).`2.`2 = adv_pi /\ (oget res{1}).`3.`2 = 1))].
proof.
move => invoke_hoare.
conseq
  (_ : ={m, glob Fun} ==> ={glob Fun, res})
  (_ :
   invar (glob Fun) /\ tm (glob Fun) = n ==>
   invar (glob Fun) /\
   (res <> None =>
    tm (glob Fun) < n /\
    ((oget res).`1 = Adv =>
     (oget res).`2.`2 = adv_pi /\ (oget res).`3.`2 = 1)))
  (_ : true ==> true) => //.
sim.
qed.

(* invoke lemma for use with any functionality, Fun, with an invariant
   and termination metric restricting destination adversarial port
   indices to a finite set of port indices, for which we know the
   corresponding hoare lemma *)

lemma invoke_term_metric_adv_pis_hoare_implies_equiv (Fun <: FUNC)
      (invar : glob Fun -> bool, tm : glob Fun -> int,
       n : int, adv_pis : int fset) :
  hoare
  [Fun.invoke :
   invar (glob Fun) /\ tm (glob Fun) = n ==>
   invar (glob Fun) /\
   (res <> None =>
    tm (glob Fun) < n /\
    ((oget res).`1 = Adv => (oget res).`2.`2 \in adv_pis))] =>
  equiv
  [Fun.invoke ~ Fun.invoke :
   ={m, glob Fun} /\ invar (glob Fun){1} /\
   tm (glob Fun){1} = n ==>
   ={res, glob Fun} /\ invar (glob Fun){1} /\
   (res{1} <> None =>
    tm (glob Fun){1} < n /\
    ((oget res{1}).`1 = Adv => (oget res{1}).`2.`2 \in adv_pis))].
proof.
move => invoke_hoare.
conseq
  (_ : ={m, glob Fun} ==> ={glob Fun, res})
  (_ :
   invar (glob Fun) /\ tm (glob Fun) = n ==>
   invar (glob Fun) /\
   (res <> None =>
    tm (glob Fun) < n /\
    ((oget res).`1 = Adv => (oget res).`2.`2 \in adv_pis)))
  (_ : true ==> true) => //.
sim.
qed.

(* Converting Hoare lemmas about invariants and termination metrics
   for adversaries into equiv lemmas

   This will be used for simulator cores *)

(* init lemma for use with any adversary, Adv, with an invariant
   for which we know the corresponding hoare lemma *)

lemma adv_init_invar_hoare_implies_equiv (Adv <: ADV)
      (invar : glob Adv -> bool) :
  hoare [Adv.init : true ==> invar (glob Adv)] =>
  equiv
  [Adv.init ~ Adv.init :
   ={glob Adv} ==>
   ={glob Adv} /\ invar (glob Adv){1}].
proof.
move => init_hoare.
conseq
  (_ : ={glob Adv} ==> ={glob Adv})
  (_ : true ==> invar (glob Adv))
  (_ : true ==> true) => //.
sim.
qed.

(* invoke lemma for use with any adversary, Adv, with an invariant and
   termination metric for which we know the corresponding hoare lemma *)

lemma adv_invoke_term_metric_hoare_implies_equiv (Adv <: ADV)
      (invar : glob Adv -> bool, tm : glob Adv -> int, n : int) :
  hoare
  [Adv.invoke :
   invar (glob Adv) /\ tm (glob Adv) = n ==>
   invar (glob Adv) /\
   (res <> None => tm (glob Adv) < n)] =>
  equiv
  [Adv.invoke ~ Adv.invoke :
   ={m, glob Adv} /\ invar (glob Adv){1} /\
   tm (glob Adv){1} = n ==>
   ={res, glob Adv} /\ invar (glob Adv){1} /\
   (res{1} <> None => tm (glob Adv){1} < n)].
proof.
move => invoke_hoare.
conseq
  (_ : ={m, glob Adv} ==> ={glob Adv, res})
  (_ :
   invar (glob Adv) /\ tm (glob Adv) = n ==>
   invar (glob Adv) /\
   (res <> None => tm (glob Adv) < n))
  (_ : true ==> true) => //.
sim.
qed.

(* Wrapper for Real Functionalities

   Translator from UC DSL to EasyCrypt will turn real functionalities
   into plugins to the wrapper. *)

type rf_info =
  {rfi_num_parties         : int;
   rfi_num_subfuns         : int;
   rfi_num_params          : int;
   rfi_adv_pi_begin        : int;  (* first adv pi of instance of unit *)
   rfi_adv_pi_main_end     : int;  (* last advi pi not from params *)
   rfi_adv_pi_begin_params : int list;
   rfi_adv_pi_end_params   : int list}.

(* indexed from 1: *)

op nth1_adv_pi_begin_params (rfi : rf_info, pari) : int =
  nth 0 rfi.`rfi_adv_pi_begin_params (pari - 1).

op nth1_adv_pi_end_params (rfi : rf_info, pari) : int =
  nth 0 rfi.`rfi_adv_pi_end_params (pari - 1).

op adv_pis_rf_info (rfi : rf_info) : int fset =
  if rfi.`rfi_num_params = 0
  then rangeset rfi.`rfi_adv_pi_begin
       (rfi.`rfi_adv_pi_main_end + 1)
  else rangeset rfi.`rfi_adv_pi_begin
       (nth1_adv_pi_end_params rfi rfi.`rfi_num_params + 1).

op rf_info_valid (rfi : rf_info) : bool =
  1 <= rfi.`rfi_num_parties /\
  0 <= rfi.`rfi_num_subfuns /\
  0 <= rfi.`rfi_num_params /\
  1 <= rfi.`rfi_adv_pi_begin /\
  (* includes adv pi of ideal functionality of unit *)
  rfi.`rfi_adv_pi_begin <= rfi.`rfi_adv_pi_main_end /\
  size rfi.`rfi_adv_pi_begin_params = rfi.`rfi_num_params /\
  size rfi.`rfi_adv_pi_end_params   = rfi.`rfi_num_params /\
  (1 <= rfi.`rfi_num_params =>
   nth1_adv_pi_begin_params rfi 1 = rfi.`rfi_adv_pi_main_end + 1 /\
   (forall (pari : int),
    1 <= pari <= rfi.`rfi_num_params =>
    nth1_adv_pi_begin_params rfi pari <= nth1_adv_pi_end_params rfi pari) /\
   (forall (pari : int),
    1 <= pari <= rfi.`rfi_num_params - 1 =>
    nth1_adv_pi_begin_params rfi (pari + 1) =
    nth1_adv_pi_end_params rfi pari + 1)).

lemma rfi_valid_adv_pi_main_end_lt_adv_pi_param_begin
      (rfi : rf_info, pari : int) :
  rf_info_valid rfi => 1 <= pari <= rfi.`rfi_num_params =>
  rfi.`rfi_adv_pi_main_end < nth1_adv_pi_begin_params rfi pari.
proof.
move => rf_info_valid_rfi.
have ind :
  forall pi,
  0 <= pi => 1 <= pi <= rfi.`rfi_num_params =>
  rfi.`rfi_adv_pi_main_end < nth1_adv_pi_begin_params rfi pi.
elim; smt().
smt().
qed.

lemma rfi_valid_lt_par_indices_implies_lt_param_adv_pi_begins
      (rfi : rf_info, pari parj : int) :
  rf_info_valid rfi => 1 <= pari < parj <= rfi.`rfi_num_params =>
  nth1_adv_pi_begin_params rfi pari < nth1_adv_pi_begin_params rfi parj.
proof.
move => rf_info_valid_rfi [#] ge1_pari lt_pari_parj.
have ind :
  forall pj,
  0 <= pj => pari < pj <= rfi.`rfi_num_params =>
  nth1_adv_pi_begin_params rfi pari < nth1_adv_pi_begin_params rfi pj.
elim; smt().
smt().
qed.

lemma rfi_valid_param_adv_pi_in_range_for_pari (rfi : rf_info, i : int) :
  rf_info_valid rfi => 1 <= rfi.`rfi_num_params =>
  nth1_adv_pi_begin_params rfi 1 <= i <=
  nth1_adv_pi_end_params rfi rfi.`rfi_num_params =>
  (exists (pari : int),
   1 <= pari <= rfi.`rfi_num_params /\
   nth1_adv_pi_begin_params rfi pari <= i <=
   nth1_adv_pi_end_params rfi pari).
proof.
move => rf_info_valid_rfi rfi_num_params_ge1 i_is_param_adv_pi.
case
  (exists (pari : int),
   (1 <= pari && pari <= rfi.`rfi_num_params) /\
   nth1_adv_pi_begin_params rfi pari <= i &&
   i <= nth1_adv_pi_end_params rfi pari) => [// | contrad].
have /# :
  forall (j : int),
  0 <= j => 1 <= j <= rfi.`rfi_num_params =>
  ! (nth1_adv_pi_begin_params rfi 1 <= i <=
     nth1_adv_pi_end_params rfi j) by
    elim => [// | j ge0_j IH j_plus1_good_par /#].
qed.

op adv_pis_rf_info_first (rfi : rf_info) : int =
  rfi.`rfi_adv_pi_begin.

op adv_pis_rf_info_last (rfi : rf_info) : int =
  if rfi.`rfi_num_params = 0
  then rfi.`rfi_adv_pi_main_end
  else nth1_adv_pi_end_params rfi rfi.`rfi_num_params.

lemma adv_pis_rf_info_rangeset (rfi : rf_info) :
  adv_pis_rf_info rfi =
  rangeset (adv_pis_rf_info_first rfi) (adv_pis_rf_info_last rfi + 1).
proof.
rewrite /adv_pis_rf_info /adv_pis_rf_info_first /adv_pis_rf_info_last.
by case (rfi.`rfi_num_params = 0).
qed.

lemma adv_pis_rf_info_first_ge1 (rfi : rf_info) :
  rf_info_valid rfi => 1 <= adv_pis_rf_info_first rfi.
proof. smt(). qed.

lemma adv_pis_rf_info_first_le_last (rfi : rf_info) :
  rf_info_valid rfi =>
  adv_pis_rf_info_first rfi <= adv_pis_rf_info_last rfi.
proof.
smt(rfi_valid_adv_pi_main_end_lt_adv_pi_param_begin).
qed.

op addr_ge_param (rfi : rf_info, self addr : addr) : bool =
  exists (k : int),
  1 <= k <= rfi.`rfi_num_params /\ self ++ [k] <= addr.

op addr_eq_param (rfi : rf_info, self addr : addr) : bool =
  exists (k : int),
  1 <= k <= rfi.`rfi_num_params /\ addr = self ++ [k].

op addr_eq_subfun (rfi : rf_info, self addr : addr) : bool =
  exists (k : int),
  rfi.`rfi_num_params + 1 <= k <=
  rfi.`rfi_num_params + rfi.`rfi_num_subfuns /\
  addr = self ++ [k].

(* should only be applied when addr is >= self ++ [i], for some
   necessarily unique i; returns the i *)

op next_of_addr (self addr : addr) : int =
  head_of_drop_size_first 0 self addr.

lemma next_of_addr_ge_self_plus (self addr : addr, i : int) :
  self ++ [i] <= addr => next_of_addr self addr = i.
proof.
move => self_concat_i_le_addr.
have <- : self ++ [i] ++ drop (size (self ++ [i])) addr = addr
  by rewrite -le_drop.
rewrite /next_of_addr /head_of_drop_size_first /drop_size_first.
by rewrite -catA drop_size_cat.
qed.

lemma next_of_addrs_ge_self_plus_eq (self addr1 addr2 : addr, i : int) :
  self ++ [i] <= addr1 => self ++ [i] <= addr2 =>
  next_of_addr self addr1 = next_of_addr self addr2.
proof.
move => self_i_le_addr1 self_i_le_addr2.
rewrite (next_of_addr_ge_self_plus _ _ i) //
        (next_of_addr_ge_self_plus _ _ i) //.
qed.

lemma disjoint_addr_eq_param_subfun (rfi : rf_info, self addr : addr) :
  addr_eq_param rfi self addr => addr_eq_subfun rfi self addr =>
  false.
proof.
rewrite /addr_eq_param /addr_eq_subfun.
move =>
  [k1] [#] _ le_k1_num_params ->
  [k2] [#] le_num_params_pl1_k2 _ /#.
qed.

lemma disjoint_addr_ge_param_eq_subfun (rfi : rf_info, self addr : addr) :
  addr_ge_param rfi self addr => addr_eq_subfun rfi self addr =>
  false.
proof.
rewrite /addr_ge_param /addr_eq_subfun.
move =>
  [k1] [#] _ le_k1_num_params sing_k1_le_sing_k2
  [k2] [#] le_num_params_pl1_k2 _ ->>.
rewrite le_pre in sing_k1_le_sing_k2.
smt(sing_not_le).
qed.

lemma not_addr_ge_param_self (rfi : rf_info, self : addr) :
  ! addr_ge_param rfi self self.
proof.
by case (addr_ge_param rfi self self).
qed.

lemma not_addr_eq_param_self (rfi : rf_info, self : addr) :
  ! addr_eq_param rfi self self.
proof.
by case (addr_eq_param rfi self self).
qed.

lemma not_addr_eq_subfun_self (rfi : rf_info, self : addr) :
  ! addr_eq_subfun rfi self self.
proof.
by case (addr_eq_subfun rfi self self).
qed.

lemma disjoint_addr_eq_param_envport
      (rfi : rf_info, self addr : addr, pi : int) :
  addr_eq_param rfi self addr => envport self (addr, pi) =>
  false.
proof.
rewrite /addr_eq_param /envport /=.
move => [k] [#] _ _ -> /#.
qed.

lemma disjoint_addr_eq_subfun_envport
      (rfi : rf_info, self addr : addr, pi : int) :
  addr_eq_subfun rfi self addr => envport self (addr, pi) =>
  false.
proof.
rewrite /addr_eq_subfun /envport /=.
move => [k] [#] _ _ -> /#.
qed.

abstract theory RealFunctionality.

(* begin theory parameters *)

op rf_info : rf_info.

axiom rf_info_valid : rf_info_valid rf_info.

(* end theory parameters *)

module MakeRF (Core : FUNC) : FUNC = {
  var self : addr

  proc init(_self : addr) : unit = {
    self <- _self;
    Core.init(_self);
  }

  proc after_core(r : msg option, orig_dest_addr : addr)
         : msg option * msg * bool = {
    var m : msg <- witness;
    var not_done <- true;
    if (r = None) {
      not_done <- false;
    }
    else {
      m <- oget r;  (* next iteration, if any, will use m *)
      if (m.`1 = Dir) {
        if (m.`3.`1 = self /\ self = orig_dest_addr) {
          if (envport self m.`2) {
            not_done <- false;
          }
          elif (addr_eq_subfun rf_info self m.`2.`1 \/
                addr_eq_param rf_info self m.`2.`1) {
          }
          else {
            not_done <- false; r <- None;
          }
        }
        elif (addr_eq_subfun rf_info self m.`3.`1 /\
              m.`3.`1 = orig_dest_addr /\ m.`2.`1 = self) {
        }
        elif (addr_eq_param rf_info self m.`3.`1 /\
              self ++ [next_of_addr self m.`3.`1] <= orig_dest_addr /\
              m.`2.`1 = self) {
        }
        else {
          not_done <- false; r <- None;
        }
      }
      else {  (* m.`1 = Adv *)
        not_done <- false;
        if (m.`2.`1 <> adv \/ ! 0 < m.`2.`2) {
          r <- None;
        }
        elif ((m.`3.`1 = self \/
               addr_eq_subfun rf_info self m.`3.`1) /\
              m.`3.`1 = orig_dest_addr) {
        }
        elif (addr_ge_param rf_info self m.`3.`1 /\
              self ++ [next_of_addr self m.`3.`1] <= orig_dest_addr) {
        }
        else {
          r <- None;
        }
      }
    }
    return (r, m, not_done);
  }

  proc loop(m : msg) : msg option = {
    var r : msg option <- None;
    var not_done : bool <- true;
    while (not_done) {
      r <@ Core.invoke(m);
      (r, m, not_done) <@ after_core(r, m.`2.`1);
    }
    return r;
  }

  proc invoke(m : msg) : msg option = {
    var r : msg option <- None;
    (* we can assume m.`3.`1 is not >= self *)
    if ((m.`1 = Dir /\ m.`2.`1 = self) \/
        (m.`1 = Adv /\
         (m.`2.`1 = self \/
          addr_ge_param rf_info self m.`2.`1 \/
          addr_eq_subfun rf_info self m.`2.`1))) {
      r <@ loop(m);
    }
    return r;
  }
}.

op after_core_return
   (func : addr, r : msg option, orig_dest_addr : addr) : bool =
  r <> None /\
  (((oget r).`1 = Dir /\ (oget r).`3.`1 = func /\ func = orig_dest_addr /\
    envport func (oget r).`2) \/
   ((oget r).`1 = Adv /\ (oget r).`2.`1 = adv /\ 0 < (oget r).`2.`2 /\
    ((((oget r).`3.`1 = func \/ addr_eq_subfun rf_info func (oget r).`3.`1) /\
       (oget r).`3.`1 = orig_dest_addr) \/
     (addr_ge_param rf_info func (oget r).`3.`1 /\
      func ++ [next_of_addr func (oget r).`3.`1] <= orig_dest_addr)))).

op after_core_continue
   (func : addr, r : msg option, orig_dest_addr : addr) : bool =
  r <> None /\ (oget r).`1 = Dir /\
  (((oget r).`3.`1 = func /\ func = orig_dest_addr /\
    (addr_eq_subfun rf_info func (oget r).`2.`1 \/
     addr_eq_param rf_info func (oget r).`2.`1)) \/
   (addr_eq_subfun rf_info func (oget r).`3.`1 /\
    (oget r).`3.`1 = orig_dest_addr /\ (oget r).`2.`1 = func) \/
   (addr_eq_param rf_info func (oget r).`3.`1 /\
    func ++ [next_of_addr func (oget r).`3.`1] <= orig_dest_addr /\
    (oget r).`2.`1 = func)).

op after_core_error
   (func : addr, r : msg option, orig_dest_addr : addr) : bool =
  r = None \/
  ((oget r).`1 = Dir /\ (oget r).`3.`1 = func /\
   ! envport func (oget r).`2 /\
   ! addr_eq_param rf_info func (oget r).`2.`1 /\
   ! addr_eq_subfun rf_info func (oget r).`2.`1) \/
  ((oget r).`1 = Dir /\
   ((oget r).`3.`1 <> func \/ func <> orig_dest_addr) /\
   (! addr_eq_subfun rf_info func (oget r).`3.`1 \/
      (oget r).`3.`1 <> orig_dest_addr \/ (oget r).`2.`1 <> func) /\
   (! addr_eq_param rf_info func (oget r).`3.`1 \/
    ! func ++ [next_of_addr func (oget r).`3.`1] <= orig_dest_addr \/
    (oget r).`2.`1 <> func)) \/
  ((oget r).`1 = Adv /\ (oget r).`2.`1 <> adv) \/
  ((oget r).`1 = Adv /\ ! 0 < (oget r).`2.`2) \/
  ((oget r).`1 = Adv /\
   (((oget r).`3.`1 <> func /\ ! addr_eq_subfun rf_info func (oget r).`3.`1) \/
     (oget r).`3.`1 <> orig_dest_addr) /\
   (! addr_ge_param rf_info func (oget r).`3.`1 \/
    ! func ++ [next_of_addr func (oget r).`3.`1] <= orig_dest_addr)).

lemma after_core_disj (func adv : addr, r : msg option,
      orig_dest_addr : addr) :
  after_core_return func r orig_dest_addr \/
  after_core_continue func r orig_dest_addr \/
  after_core_error func r orig_dest_addr.
proof.
rewrite /after_core_return /after_core_continue
        /after_core_error.
case (r = None) => // _ /=.
case ((oget r).`2.`1 = UCBasicTypes.adv) => // _ /= /#.
qed.

lemma MakeRF_after_core_return (Core <: FUNC) (r' : msg option) :
  phoare
  [MakeRF(Core).after_core :
   r = r' /\
   after_core_return MakeRF.self r orig_dest_addr ==>
   res.`1 = r' /\ res.`1 = Some res.`2 /\ ! res.`3] = 1%r.
proof.
proc; auto; smt().
qed.

lemma MakeRF_after_core_continue (Core <: FUNC) (r' : msg option) :
  phoare
  [MakeRF(Core).after_core :
   r = r' /\
   after_core_continue MakeRF.self r orig_dest_addr ==>
   res.`1 = r' /\ res.`1 = Some res.`2 /\ res.`3] = 1%r.
proof.
proc => /=.
auto;
  smt(disjoint_addr_eq_param_envport
      disjoint_addr_eq_subfun_envport).
qed.

lemma MakeRF_after_core_error (Core <: FUNC) :
  phoare
  [MakeRF(Core).after_core :
   after_core_error MakeRF.self r orig_dest_addr ==>
   res.`1 = None /\ ! res.`3] = 1%r.
proof.
proc => /=.
auto;
  smt(not_addr_eq_param_self not_addr_eq_subfun_self
      not_addr_eq_param_self not_addr_eq_subfun_self
      not_addr_ge_param_self disjoint_addr_ge_param_eq_subfun).
qed.

(* termination invariants and metrics

   lemmas for invoke also restrict destination adversarial
   port indices for adversarial messages *)

lemma MakeRF_init_invar_hoare (Core <: FUNC{-MakeRF})
      (core_invar : glob Core -> bool) :
  hoare [Core.init : true ==> core_invar (glob Core)] =>
  hoare [MakeRF(Core).init : true ==> core_invar (glob Core)].
proof.
move => Core_init.
proc; sp.
call Core_init.
auto.
qed.

lemma MakeRF_invoke_term_metric_hoare (Core <: FUNC{-MakeRF})
      (invar_Core : glob Core -> bool, tm_Core : glob Core -> int,
       n : int, advpis : int fset) :
  (forall (n : int),
   hoare
   [Core.invoke :
    invar_Core (glob Core) /\ tm_Core (glob Core) = n ==>
    invar_Core (glob Core) /\
    (res <> None =>
     tm_Core (glob Core) < n /\
     ((oget res).`1 = Adv => (oget res).`2.`2 \in advpis))]) =>
  hoare
  [MakeRF(Core).invoke :
   invar_Core (glob Core) /\ tm_Core (glob Core) = n ==>
   invar_Core (glob Core) /\
   (res <> None =>
    tm_Core (glob Core) < n /\
    ((oget res).`1 = Adv => (oget res).`2.`2 \in advpis))].
proof.
move => Core_invoke_invar_tm.
proc; sp 1; if => //.
inline 1; wp; sp.
conseq
  (_ :
   not_done /\
   invar_Core (glob Core) /\ tm_Core (glob Core) = n ==>
   _) => //.
rcondt 1; first auto.
seq 1 :
  (invar_Core (glob Core) /\
   (r0 <> None =>
    tm_Core (glob Core) < n /\
    ((oget r0).`1 = Adv => (oget r0).`2.`2 \in advpis))).
call (Core_invoke_invar_tm n); first auto; smt().
seq 1 :
  (invar_Core (glob Core) /\
   (r0 = None  => ! not_done) /\
   (r0 <> None =>
    tm_Core (glob Core) < n /\
    ((oget r0).`1 = Adv => (oget r0).`2.`2 \in advpis))).
inline*; auto; progress; smt().
while
  (invar_Core (glob Core) /\
   (r0 = None  => ! not_done) /\
   (r0 <> None =>
    tm_Core (glob Core) < n /\
    ((oget r0).`1 = Adv => (oget r0).`2.`2 \in advpis))).
conseq
  (_ :
   invar_Core (glob Core) /\
   tm_Core (glob Core) < n /\
   ((oget r0).`1 = Adv => (oget r0).`2.`2 \in advpis) ==>
   _); first smt().
exlim (tm_Core (glob Core)) => n'.
seq 1 :
  (invar_Core (glob Core) /\
   (r0 <> None =>
    tm_Core (glob Core) < n /\
    ((oget r0).`1 = Adv => (oget r0).`2.`2 \in advpis))).
call (Core_invoke_invar_tm n'); first auto; smt().
inline*; auto; progress; smt().
auto.
qed.

end RealFunctionality.

(* dummy adversary (DA) - completely controlled by environment *)

(* message from port env_root_port of environment to port
   adv_root_port (adv, 0) of dummy adversary, instructing dummy
   adversary to send message (Adv, dfe_pt, (adv, dfe_n), dfe_tag,
   dfe_u); this instruction will only be obeyed if 0 < dfe_n,
   dfe_pt <> env_root_port and dfe_pt.`1 is not >= adv *)

type da_from_env =
  {(* data: *)
   dfe_pt  : port;   (* destination port of message to be sent by DA *)
   dfe_n   : int;    (* source port index of message to be sent by DA *)
   dfe_tag : tag;    (* tag of message to be sent by DA *)
   dfe_u   : univ}.  (* value of message to be sent by DA *)

op enc_da_from_env (x : da_from_env) : msg =  (* let SMT provers inspect *)
  (Adv, adv_root_port, env_root_port,
   TagNoInter,
   (epdp_tuple4_univ epdp_port_univ epdp_int_univ
    epdp_tag_univ epdp_id).`enc
    (x.`dfe_pt, x.`dfe_n, x.`dfe_tag, x.`dfe_u)).

op [opaque smt_opaque] dec_da_from_env (m : msg) : da_from_env option =
  let (mod, pt1, pt2, tag, v) = m
  in (mod = Dir \/ pt1 <> adv_root_port \/ pt2 <> env_root_port \/
      tag <> TagNoInter) ?
     None :
     match (epdp_tuple4_univ
            epdp_port_univ epdp_int_univ epdp_tag_univ epdp_id).`dec v with
     | None   => None
     | Some x =>
         let (pt, n, tag, u) = x
         in Some {|dfe_pt = pt; dfe_n = n; dfe_tag = tag; dfe_u = u|}
     end.

op epdp_da_from_env =
  {|enc = enc_da_from_env; dec = dec_da_from_env|}.

lemma valid_epdp_da_from_env : valid_epdp epdp_da_from_env.
proof.
apply epdp_intro.
move => x.
rewrite /epdp_da_from_env /= /dec_da_from_env /enc_da_from_env /=.
by case x.
move => [mod pt1 pt2 tag u] v.
rewrite /epdp_da_from_env /dec_da_from_env /enc_da_from_env /=.
case
  (mod = Dir \/ pt1 <> adv_root_port \/ pt2 <> env_root_port \/
   tag <> TagNoInter) => //.
rewrite !negb_or /= not_dir => [#] -> -> -> -> match_eq_some /=.
have val_u :
  (epdp_tuple4_univ epdp_port_univ epdp_int_univ
   epdp_tag_univ epdp_id).`dec u =
  Some (v.`dfe_pt, v.`dfe_n, v.`dfe_tag, v.`dfe_u).
  move : match_eq_some.
  case ((epdp_tuple4_univ epdp_port_univ epdp_int_univ
         epdp_tag_univ epdp_id).`dec u) => //.
  by case.
move : match_eq_some.
rewrite val_u /= => <- /=.
by rewrite (epdp_dec_enc _ _ u).
qed.

hint simplify [eqtrue] valid_epdp_da_from_env.
hint rewrite epdp : valid_epdp_da_from_env.

lemma eq_of_valid_da_from_env (m : msg) :
  is_valid epdp_da_from_env m =>
  m =
  let x = oget (epdp_da_from_env.`dec m) in
  (Adv,
   adv_root_port,
   env_root_port,
   TagNoInter,
   (epdp_tuple4_univ epdp_port_univ epdp_int_univ epdp_tag_univ epdp_id).`enc
    (x.`dfe_pt, x.`dfe_n, x.`dfe_tag, x.`dfe_u)).
proof.
rewrite /is_valid.
move => val_m.
have [] x : exists (x : da_from_env), epdp_da_from_env.`dec m = Some x.
  exists (oget (epdp_da_from_env.`dec m)); by rewrite -some_oget.
case x => x1 x2 x3 x4.
move => /(epdp_dec_enc _ _ _ valid_epdp_da_from_env) <- //.
qed.

(* message from port adv_root_port of dummy adversary to port
   env_root_port of environment, telling environment that dummy
   adversary received message (Adv, (adv, dte_n), dte_pt, dte_tag,
   dte_u), where 0 < dtn_n and dte_pt <> env_root_port *)

type da_to_env =
  {(* data: *)
   dte_n   : int;    (* destination port index of message sent to DA;
                        the port's address will be adv
                        (enforced by interface/simulator) *)
   dte_pt  : port;   (* source port of message sent to DA *)
   dte_tag : tag;    (* tag of message sent to DA *)
   dte_u   : univ}.  (* value of message sent to DA *)

op enc_da_to_env (x : da_to_env) : msg =  (* let SMT provers inspect *)
  (Adv, env_root_port, adv_root_port,
   TagNoInter,
   (epdp_tuple4_univ epdp_int_univ epdp_port_univ
    epdp_tag_univ epdp_id).`enc
    (x.`dte_n, x.`dte_pt, x.`dte_tag, x.`dte_u)).

op [opaque smt_opaque] dec_da_to_env (m : msg) : da_to_env option =
  let (mod, pt1, pt2, tag, v) = m
  in (mod = Dir \/ pt1 <> env_root_port \/ pt2 <> adv_root_port \/
      tag <> TagNoInter) ?
     None :
     match (epdp_tuple4_univ
            epdp_int_univ epdp_port_univ epdp_tag_univ
            epdp_id).`dec v with
     | None   => None
     | Some x =>
         let (n, pt, tag, u) = x
        in Some {|dte_n = n; dte_pt = pt; dte_tag = tag; dte_u = u|}
     end.

op epdp_da_to_env =  (* let SMT provers inspect *)
  {|enc = enc_da_to_env; dec = dec_da_to_env|}.

lemma valid_epdp_da_to_env : valid_epdp epdp_da_to_env.
proof.
apply epdp_intro.
move => x.
rewrite /epdp_da_to_env /= /dec_da_to_env /enc_da_to_env /=.
by case x.
move => [mod pt1 pt2 tag u] v.
rewrite /epdp_da_to_env /dec_da_to_env /enc_da_to_env /=.
case (mod = Dir \/ pt1 <> env_root_port \/ pt2 <> adv_root_port \/
      tag <> TagNoInter) => //.
rewrite !negb_or /= not_dir => [#] -> -> -> -> match_eq_some /=.
have val_u :
  (epdp_tuple4_univ epdp_int_univ epdp_port_univ
   epdp_tag_univ epdp_id).`dec u =
  Some (v.`dte_n, v.`dte_pt, v.`dte_tag, v.`dte_u).
  move : match_eq_some.
  case ((epdp_tuple4_univ epdp_int_univ epdp_port_univ
         epdp_tag_univ epdp_id).`dec u) => //.
  by case.
move : match_eq_some.
rewrite val_u /= => <- /=.
by rewrite (epdp_dec_enc _ _ u).
qed.

hint simplify [eqtrue] valid_epdp_da_to_env.
hint rewrite epdp : valid_epdp_da_to_env.

lemma eq_of_valid_da_to_env (m : msg) :
  is_valid epdp_da_to_env m =>
  m =
  let x = oget (epdp_da_to_env.`dec m) in
  (Adv,
   env_root_port,
   adv_root_port,
   TagNoInter,
   (epdp_tuple4_univ epdp_int_univ epdp_port_univ
    epdp_tag_univ epdp_id).`enc
    (x.`dte_n, x.`dte_pt, x.`dte_tag, x.`dte_u)).
proof.
rewrite /is_valid.
move => val_m.
have [] x : exists (x : da_to_env), epdp_da_to_env.`dec m = Some x.
  exists (oget (epdp_da_to_env.`dec m)); by rewrite -some_oget.
case x => x1 x2 x3 x4.
move => /(epdp_dec_enc _ _ _ valid_epdp_da_to_env) <- //.
qed.

lemma dest_pi_gt0_implies_dec_epdp_da_from_env_fails (m : msg) :
  0 < m.`2.`2 => epdp_da_from_env.`dec m = None.
proof.
case m => x1 x2 x3 x4 x5; case x2 => x2_1 x2_2 /=.
move => gt0_dest_pi.
rewrite /epdp_da_from_env /dec_da_from_env /=.
rewrite /adv_root_port /= negb_and.
have -> // : x2_2 <> 0 by smt().
qed.

module DummyAdv : ADV = {
  proc init() : unit = { }

  proc invoke(m : msg) : msg option = {
    var r : msg option <- None;

    match epdp_da_from_env.`dec m with
      Some x => {
        (* m.`1 = Adv, m.`2 = adv_root_port, m.`3 = env_root_port *)
        if (0 < x.`dfe_n /\ x.`dfe_pt <> env_root_port /\
            ! adv <= x.`dfe_pt.`1) {
          r <- Some (Adv, x.`dfe_pt, (adv, x.`dfe_n), x.`dfe_tag, x.`dfe_u);
        }
      }
    | None   => {
        (* message from functionality or environment;
           interface/simulator will enforce that m.`1 = Adv /\
           m.`2.`1 = adv /\ 0 <= m.`2.`2 /\ ! adv <= m.`3.`1 /\
           (m.`3 = env_root_port <=> m.`2.`2 = 0) *)
        if (0 < m.`2.`2) { (* so can't overlap with above *)
          r <-
            Some
            (epdp_da_to_env.`enc
             {|dte_n = m.`2.`2; dte_pt = m.`3;
               dte_tag = m.`4; dte_u = m.`5|});
        }
      }
    end;
    return r;
  }
}.

(* module type for simulators

   a module that takes in Adv : ADV and yields an ADV will have this
   type, making it possible to quantify over simulators *)

module type SIM (Adv : ADV) = {
  proc init() : unit {Adv.init}
  proc invoke(m : msg) : msg option {Adv.invoke}
}.

(* simulator composition *)

module (SimComp (Sim2 : SIM, Sim1 : SIM) : SIM) (Adv : ADV) : ADV =
  Sim2(Sim1(Adv)).

(* making simulators and dummy adversary theorem *)

abstract theory Simulator.

(* begin theory parameters *)

(* adversarial port index of simulator *)

op sim_adv_pi : int.

axiom sim_adv_pi_ge1 : 1 <= sim_adv_pi.

(* end theory parameters *)

module (MS (Core : ADV) : SIM) (Adv : ADV) : ADV = {
  (* address of ideal functionality; only known after first message
     received with destination port index sim_adv_pi

     if non-None, inc (oget if_addr_opt) adv *)

  var if_addr_opt : addr option

  proc init() : unit = {
    if_addr_opt <- None;
    Core.init();
    Adv.init();
  }

  proc after_core(r : msg option) : msg option * msg * bool = {
    var m : msg <- witness; var not_done;
    var if_addr : addr <- oget if_addr_opt;  (* will be non-None *)
    if (r = None) {
      not_done <- false;
    }
    else {
      m <- oget r;
      if (m.`1 = Dir) {
        r <- None; not_done <- false;
      }
      elif (m.`2.`1 = adv) {
        if (0 < m.`2.`2 /\ m.`2.`2 <> sim_adv_pi /\ if_addr <= m.`3.`1) {
          not_done <- true;
        }
        else {
          r <- None; not_done <- false;
        }
      }
      elif (m.`2.`1 = if_addr) {
        if (m.`2.`2 = 1 /\ m.`3 = (adv, sim_adv_pi)) {
          not_done <- false;
        }
        else {
          r <- None; not_done <- false;
        }
      }
      else {
        r <- None; not_done <- false;
      }
    }
    return (r, m, not_done);
  }

  proc after_adv(r : msg option) : msg option * msg * bool = {
    var m : msg <- witness; var not_done;
    var if_addr : addr;
    if (r = None) {
      not_done <- false;
    }
    else {
      m <- oget r;
      if (m.`1 = Dir \/ adv <= m.`2.`1 \/ m.`3.`1 <> adv \/ m.`3.`2 < 0 \/
          ! (m.`3.`2 = 0 <=> m.`2 = env_root_port)) {
        r <- None; not_done <- false;
      }
      elif (if_addr_opt <> None /\ oget if_addr_opt <= m.`2.`1) {
        not_done <- true;
      }
      else {
        not_done <- false;
      }
    }
    return (r, m, not_done);
  }

  proc loop(m : msg) : msg option = {
    var r : msg option <- None;
    var not_done : bool <- true;

    while (not_done) {
      if (m.`2.`1 = adv) {
        if (m.`2.`2 = sim_adv_pi) {
          r <@ Core.invoke(m);
          (r, m, not_done) <@ after_core(r);
        }
        else {
          r <@ Adv.invoke(m);
          (r, m, not_done) <@ after_adv(r);
        }
      }
      else {  (* if_addr_opt <> None /\ oget if_addr_opt <= m.`2.`1 *)
        r <@ Core.invoke(m);
        (r, m, not_done) <@ after_core(r);
      }
    }
    return r;
  }

  (* (if_addr_opt <> None => inc (oget if_addr_opt) adv) /\

     m.`1 = Adv /\ m.`2.`1 = adv /\
     (m.`2.`2 = 0 /\ m.`3 = env_root_port \/
      0 < m.`2.`2 /\ ! adv <= m.`3.`1 /\ m.`3 <> env_root_port) *)

  proc invoke(m : msg) : msg option = {
    var r : msg option <- None;
    if (m.`2.`2 = sim_adv_pi) {
      if (if_addr_opt = None) {
        if (m.`3.`2 = 1) {  (* ideal functionality's port index *)
          (* for the ideal functionalities generated by the
             translator, m.`3.`1 will be equal to the address of the
             functionality, but we can't check for that *)
          if_addr_opt <- Some m.`3.`1;
          r <@ loop(m);
        }
      }
      elif (m.`3 = (oget if_addr_opt, 1)) {
        r <@ loop(m);
      }
    }
    else {
      r <@ loop(m);
    }
    return r;
  }
}.

op after_core_return (if_addr : addr, r : msg option) : bool =
  r <> None /\ (oget r).`1 = Adv /\ (oget r).`2.`1 = if_addr /\
  (oget r).`2.`2 = 1 /\ (oget r).`3 = (adv, sim_adv_pi).

op after_core_continue (if_addr : addr, r : msg option) : bool =
  r <> None /\ (oget r).`1 = Adv /\ (oget r).`2.`1 = adv /\
  0 < (oget r).`2.`2 /\ (oget r).`2.`2 <> sim_adv_pi /\
  if_addr <= (oget r).`3.`1.

op after_core_error (if_addr : addr, r : msg option) : bool =
  r = None \/
  (oget r).`1 = Dir \/
  (oget r).`2.`1 = adv /\
  (! 0 < (oget r).`2.`2 \/ (oget r).`2.`2 = sim_adv_pi \/
   ! if_addr <= (oget r).`3.`1) \/
  (oget r).`2.`1 = if_addr /\
  (! (oget r).`2.`2 = 1 \/ ! (oget r).`3 = (adv, sim_adv_pi)) \/
  (oget r).`2.`1 <> adv /\ (oget r).`2.`1 <> if_addr.

lemma after_core_disj (if_addr : addr, r : msg option) :
  after_core_return if_addr r \/
  after_core_continue if_addr r \/
  after_core_error if_addr r.
proof.
smt().
qed.

lemma MS_after_core_return (CoreSim <: ADV) (Adv <: ADV)
      (r' : msg option) :
  phoare
  [MS(CoreSim, Adv).after_core :
   r = r' /\
   MS.if_addr_opt <> None /\ inc (oget MS.if_addr_opt) adv /\
   after_core_return (oget MS.if_addr_opt) r ==>
   res.`1 = r' /\ res.`1 = Some res.`2 /\ ! res.`3] = 1%r.
proof.
proc; auto; smt(inc_ne_adv_func).
qed.

lemma MS_after_core_continue (CoreSim <: ADV) (Adv <: ADV)
      (r' : msg option) :
  phoare
  [MS(CoreSim, Adv).after_core :
   r = r' /\
   after_core_continue (oget MS.if_addr_opt) r ==>
   res.`1 = r' /\ res.`1 = Some res.`2 /\ res.`3] = 1%r.
proof.
proc; auto; smt().
qed.

lemma MS_after_core_error (CoreSim <: ADV) (Adv <: ADV) :
  phoare
  [MS(CoreSim, Adv).after_core :
   MS.if_addr_opt <> None /\ inc (oget MS.if_addr_opt) adv /\
   after_core_error (oget MS.if_addr_opt) r ==>
   res.`1 = None /\ ! res.`3] = 1%r.
proof.
proc; auto; smt(inc_ne_adv_func).
qed.

op after_adv_return (if_addr_opt : addr option, r : msg option) : bool =
  r <> None /\ (oget r).`1 = Adv /\ ! adv <= (oget r).`2.`1 /\
  (oget r).`3.`1 = adv /\ 0 <= (oget r).`3.`2 /\
  ((oget r).`3.`2 = 0 <=> (oget r).`2 = env_root_port) /\
  (if_addr_opt = None \/ ! oget if_addr_opt <= (oget r).`2.`1).

op after_adv_continue (if_addr_opt : addr option, r : msg option) : bool =
  r <> None /\ (oget r).`1 = Adv /\
  if_addr_opt <> None /\ oget if_addr_opt <= (oget r).`2.`1 /\
  ! adv <= (oget r).`2.`1 /\
  (oget r).`3.`1 = adv /\ 0 <= (oget r).`3.`2 /\
  ((oget r).`3.`2 = 0 <=> (oget r).`2 = env_root_port).

op after_adv_error (r : msg option) : bool =
  r = None \/ (oget r).`1 = Dir \/ adv <= (oget r).`2.`1 \/
  (oget r).`3.`1 <> adv \/ (oget r).`3.`2 < 0 \/
  ! ((oget r).`3.`2 = 0 <=> (oget r).`2 = env_root_port).

lemma after_adv_disj (if_addr_opt : addr option, r : msg option) :
  after_adv_return if_addr_opt r \/
  after_adv_continue if_addr_opt r \/
  after_adv_error r.
proof.
smt().
qed.

lemma MS_after_adv_return (CoreSim <: ADV) (Adv <: ADV)
      (r' : msg option) :
  phoare
  [MS(CoreSim, Adv).after_adv :
   r = r' /\
   after_adv_return MS.if_addr_opt r ==>
   res.`1 = r' /\ res.`1 = Some res.`2 /\ ! res.`3] = 1%r.
proof. proc; auto; smt(inc_ne_adv_func). qed.

lemma MS_after_adv_continue (CoreSim <: ADV) (Adv <: ADV)
      (r' : msg option) :
  phoare
  [MS(CoreSim, Adv).after_adv :
   r = r' /\
   after_adv_continue MS.if_addr_opt r ==>
   res.`1 = r' /\ res.`1 = Some res.`2 /\ res.`3] = 1%r.
proof. proc; auto; smt(). qed.

lemma MS_after_adv_error (CoreSim <: ADV) (Adv <: ADV) :
  phoare
  [MS(CoreSim, Adv).after_adv :
   after_adv_error r ==>
   res.`1 = None /\ ! res.`3] = 1%r.
proof. proc; auto; smt(). qed.

module (CombEnvAdv (Env : ENV, Adv : ADV) : ENV) (Inter : INTER) = {
  var func : addr
  var in_guard : int fset

  module CombInter : INTER = {
    proc init(func : addr, in_guard : int fset) : unit = { }

    proc after_adv(r : msg option) : msg option * msg * bool * bool = {
      var not_done : bool; var m : msg <- witness;
      var adv_to_adv : bool <- witness;

      if (r = None) {
        not_done <- false;
      }
      else {
        m <- oget r;
        if (m.`1 = Dir \/ adv <= m.`2.`1 \/ adv <> m.`3.`1 \/ m.`3.`2 < 0) {
          r <- None; not_done <- false;
        }
        elif (func <= m.`2.`1) {
          if (m.`3.`2 = 0) {
            r <- None; not_done <- false;
          }
          (* else: 0 < m.`3.`2 *)
          else {
            m <-
              epdp_da_from_env.`enc
              {|dfe_pt = m.`2; dfe_n = m.`3.`2; dfe_tag = m.`4;
                dfe_u = m.`5|};
            r <- Some m; not_done <- true;
            adv_to_adv <- false;  (* will be routed to Inter *)
          }
        }
        else {  (* envport0 func m.`2 *)
          not_done <- false;
          if (! (m.`3.`2 = 0 <=> m.`2 = env_root_port)) {
            r <- None;
          }
        }
      }
      return (r, m, not_done, adv_to_adv);
    }

    proc after_inter(r : msg option) : msg option * msg * bool * bool = {
      var not_done : bool; var m : msg <- witness;
      var adv_to_adv : bool <- witness; var dte : da_to_env;

      if (r = None) {
        not_done <- false;
      }
      else {
        m <- oget r;
        if (m.`1 = Dir) {
          not_done <- false;
        }
        else {
          dte <- oget (epdp_da_to_env.`dec m);
          m <-
            (Adv, (adv, dte.`dte_n), dte.`dte_pt,
             dte.`dte_tag, dte.`dte_u);
          r <- Some m; not_done <- true; adv_to_adv <- true;
        }
      }
      return (r, m, not_done, adv_to_adv);
    }

    proc loop(m : msg) : msg option = {
      var r : msg option <- None;
      var not_done : bool <- true;

      (* adversarial messages from environment will not go to dummy
         adversary *)
      var adv_to_adv : bool <- true;

      while (not_done) {
        if (m.`2.`1 = adv /\ adv_to_adv) {
          r <@ Adv.invoke(m);
          (r, m, not_done, adv_to_adv) <@ after_adv(r);
        }
        else {
          r <@ Inter.invoke(m);
          (r, m, not_done, adv_to_adv) <@ after_inter(r);
        }
      }
      return r;
    }

    proc invoke(m : msg) : msg option = {
      var r : msg option;
      if (main_guard func in_guard m) {  (* usual guard for interface *)
        r <@ loop(m);
      }
      else {
        r <- None;
      }
      return r;
    }
  }

  proc main(func_ : addr, in_guard_ : int fset) : bool = {
    var b : bool;
    func <- func_; in_guard <- in_guard_;
    Adv.init();
    b <@ Exper(CombInter, Env).main(func, in_guard);
    return b;
  }
}.

section.

declare module Env       <: ENV{-MI, -MS, -CombEnvAdv}.
declare module Adv       <: ADV{-MI, -MS, -CombEnvAdv, -Env}.
declare module RealFunc  <: FUNC{-MI, -CombEnvAdv, -Env, -Adv}.
declare module IdealFunc <: FUNC{-MI, -MS, -CombEnvAdv, -Env, -Adv}.
declare module SimCore   <:
  ADV{-MI, -MS, -CombEnvAdv, -Env, -Adv, -IdealFunc}.

declare op invar_rf : glob RealFunc -> bool.
declare op term_rf  : glob RealFunc -> int.
declare op invar_if : glob IdealFunc -> bool.
declare op term_if  : glob IdealFunc -> int.
declare op invar_sc : glob SimCore -> bool.
declare op term_sc  : glob SimCore -> int.

declare axiom ge0_term_rf (gl : glob RealFunc) :
  invar_rf gl => 0 <= term_rf gl.

declare axiom RealFunc_init :
   equiv
   [RealFunc.init ~ RealFunc.init :
    ={self, glob RealFunc} ==>
    ={glob RealFunc} /\ invar_rf (glob RealFunc){1}].

declare axiom RealFunc_invoke (n : int) :
   equiv
   [RealFunc.invoke ~ RealFunc.invoke :
    ={m, glob RealFunc} /\ invar_rf (glob RealFunc){1} /\
    term_rf (glob RealFunc){1} = n ==>
    ={res, glob RealFunc} /\ invar_rf (glob RealFunc){1} /\
    (res{1} <> None => term_rf (glob RealFunc){1} < n)].

declare axiom ge0_term_if (gl : glob IdealFunc) :
  invar_if gl => 0 <= term_if gl.

declare axiom IdealFunc_init :
   equiv
   [IdealFunc.init ~ IdealFunc.init :
    ={self, glob IdealFunc} ==>
    ={glob IdealFunc} /\ invar_if (glob IdealFunc){1}].

declare axiom IdealFunc_invoke (n : int) :
   equiv
   [IdealFunc.invoke ~ IdealFunc.invoke :
    ={m, glob IdealFunc} /\ invar_if (glob IdealFunc){1} /\
    term_if (glob IdealFunc){1} = n ==>
    ={res, glob IdealFunc} /\ invar_if (glob IdealFunc){1} /\
    (res{1} <> None =>
     term_if (glob IdealFunc){1} < n /\
     ((oget res{1}).`1 = Adv =>
      (oget res{1}).`2.`2 = sim_adv_pi /\ (oget res{1}).`3.`2 = 1))].

declare axiom ge0_term_sc (gl : glob SimCore) :
  invar_sc gl => 0 <= term_sc gl.

declare axiom SimCore_init :
   equiv
   [SimCore.init ~ SimCore.init :
    ={glob SimCore} ==>
    ={glob SimCore} /\ invar_sc (glob SimCore){1}].

declare axiom SimCore_invoke (n : int) :
   equiv
   [SimCore.invoke ~ SimCore.invoke :
    ={m, glob SimCore} /\ invar_sc (glob SimCore){1} /\
    term_sc (glob SimCore){1} = n ==>
    ={res, glob SimCore} /\ invar_sc (glob SimCore){1} /\
    (res{1} <> None => term_sc (glob SimCore){1} < n)].

local module RealLeft = {
  proc f(m : msg) : msg option = {
    var not_done <- true; var r : msg option <- witness;
    while (not_done) {
      if (MI.func <= m.`2.`1) {
        r <@ RealFunc.invoke(m);
        (r, m, not_done) <@ MI(RealFunc, Adv).after_func(r);
      }
      else {
        r <@ Adv.invoke(m);
        (r, m, not_done) <@ MI(RealFunc, Adv).after_adv(r);
      }
    }
    return r;
  }
}.

local module CI = CombEnvAdv(Env, Adv, MI(RealFunc, DummyAdv)).CombInter.

local module RealRight = {
  proc f(m : msg) : msg option = {
    var not_done <- true; var r : msg option <- witness;
    var adv_to_adv : bool <- true;

    while (not_done) {
      if (m.`2.`1 = adv /\ adv_to_adv) {    
        r <@ Adv.invoke(m);
        (r, m, not_done, adv_to_adv) <@
          CI.after_adv(r);
      }
      else {
        r <@ MI(RealFunc, DummyAdv).invoke(m);
        (r, m, not_done, adv_to_adv) <@
          CI.after_inter(r);
      }
    }
    return r;
  }
}.

local lemma bridge_real_induct (func' : addr, in_guard' : int fset) :
  exper_pre func' =>
  forall (n : int),
  equiv
  [RealLeft.f ~ RealRight.f :
   ={m, glob RealFunc, glob Adv} /\
   m{1}.`1 = Adv /\ m{1}.`2.`1 = adv /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' /\
   term_rf (glob RealFunc){1} = n /\ invar_rf (glob RealFunc){1} ==>
   ={res, glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   MakeInt.MI.func{1} = func' /\ MakeInt.MI.in_guard{1} = in_guard' /\
   MakeInt.MI.func{2} = func' /\ MakeInt.MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard'].
proof.
move => ep_func' n.
case (n < 0) => [lt0_n | ge0_n].
exfalso; smt(ge0_term_rf).
rewrite -lezNgt in ge0_n.
move : n ge0_n.
elim /Int.sintind => n ge0_n IH.
proc; sp.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
rcondf{1} 1; first auto; smt(inc_nle_l).
rcondt{2} 1; first auto.
seq 1 1 :
  (={r, glob RealFunc, glob Adv} /\
   term_rf (glob RealFunc){1} = n /\ invar_rf (glob RealFunc){1} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard').
call (_ : true); first auto.
inline{2} 1; sp 0 3.
case (MakeInt.after_adv_error func' r{1}).
seq 1 0 : 
  (={glob RealFunc, glob Adv} /\ r{1} = None /\ ! not_done{1} /\
   MakeInt.after_adv_error func' r0{2} /\
   term_rf (glob RealFunc){1} = n /\ invar_rf (glob RealFunc){1} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard').
call{1} (MakeInt.MI_after_adv_error RealFunc Adv).
auto.
rcondf{1} 1; first auto.
if{2}.
rcondf{2} 3; first auto.
auto.
sp 0 1.
if{2}.
rcondf{2} 4; first auto.
auto.
if{2}.
rcondt{2} 1; first auto; smt().
rcondf{2} 4; first auto; smt().
auto.
rcondf{2} 4; first auto.
auto; smt().
case (MakeInt.after_adv_to_env func' r{1}).
seq 1 0 : 
  (={glob RealFunc, glob Adv} /\ r{1} = r0{2} /\ ! not_done{1} /\
   ! MakeInt.after_adv_error func' r0{2} /\
   MakeInt.after_adv_to_env func' r0{2} /\
   term_rf (glob RealFunc){1} = n /\ invar_rf (glob RealFunc){1} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard').
exlim r{1} => r'.
call{1} (MakeInt.MI_after_adv_to_env RealFunc Adv r').
auto.
rcondf{1} 1; first auto.
rcondf{2} 1; first auto; smt().
rcondf{2} 2; first auto; smt().
rcondf{2} 2; first auto; smt().
rcondf{2} 5; first auto.
auto; smt().
seq 1 0 :
  (={glob RealFunc, glob Adv} /\ r{1} = r0{2} /\
   r{1} = Some m{1} /\ not_done{1} /\
   MakeInt.after_adv_to_func func' r0{2} /\
   term_rf (glob RealFunc){1} = n /\ invar_rf (glob RealFunc){1} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard').
exlim r{1} => r'.
call{1} (MakeInt.MI_after_adv_to_func RealFunc Adv r').
auto; progress; smt().
rcondt{1} 1; first auto.
rcondt{1} 1; first auto; smt(oget_some).
rcondf{2} 1; first auto.
rcondf{2} 2; first auto; smt(inc_le1_not_rl).
rcondt{2} 2; first auto; smt().
rcondf{2} 2; first auto; smt().
sp 0 6; rcondt{2} 1; first auto.
rcondf{2} 1; first auto.
inline{2} 1.
rcondt{2} 2; first auto.
inline{2} 2.
rcondt{2} 5; first auto.
rcondf{2} 5; first auto; progress.
by rewrite /epdp_da_from_env /enc_da_from_env /= inc_nle_l.
sp 0 4; elim* => r0_R.
inline{2} 1; sp 0 2.
match Some {2} 1; first auto; progress; smt().
rcondt{2} 1; first auto => /> &hr <- /=.
progress; smt(exper_pre_func_nle_env_root_addr inc_le1_not_rl).
sp.
seq 0 1 :
  (={glob RealFunc, glob Adv} /\ r2{2} = Some m2{2} /\
   m{1} = m2{2} /\ not_done1{2} /\
   MakeInt.after_adv_to_func func' r2{2} /\
   term_rf (glob RealFunc){1} = n /\ invar_rf (glob RealFunc){1} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard').
exlim r2{2} => r2'.
call{2} (MakeInt.MI_after_adv_to_func RealFunc DummyAdv r2').
auto => /> &1 &2 <- /=; progress; last 4 by rewrite H8.
rewrite H8 /= in H9. rewrite -H9 /#. smt().
rcondt{2} 1; first auto.
rcondt{2} 1; first auto; progress; smt(inc_le1_not_rl).
seq 1 1 :
  (={glob RealFunc, glob Adv} /\ r{1} = r2{2} /\
   (r{1} <> None => term_rf (glob RealFunc){1} < n) /\
   invar_rf (glob RealFunc){1} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard').
call (RealFunc_invoke n).
auto; smt().
(* begin copy *)
case (MakeInt.after_func_error func' r{1}).
seq 1 1 :
  (={glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   r{1} = r2{2} /\ r{1} = None /\
   not_done{1} = not_done1{2} /\ not_done{1} = false /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard').
call{1} (MakeInt.MI_after_func_error RealFunc Adv).
call{2} (MakeInt.MI_after_func_error RealFunc DummyAdv).
auto; smt().
rcondf{1} 1; first auto. rcondf{2} 1; first auto.
sp; inline{2} 1; sp 0 3.
rcondt{2} 1; first auto.
sp 0 2.
rcondf{2} 1; first auto.
auto.
case (MakeInt.after_func_to_env func' r{1}).
exlim r{1} => r'.
seq 1 1 :
  (={glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   r{1} = r2{2} /\ m{1} = m2{2} /\ r{1} = Some m{1} /\
   ! not_done{1} /\ ! not_done1{2} /\
   MakeInt.after_func_to_env func' r{1} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard').
call{1} (MakeInt.MI_after_func_to_env RealFunc Adv r').
call{2} (MakeInt.MI_after_func_to_env RealFunc DummyAdv r').
auto; smt().
rcondf{1} 1; first auto. rcondf{2} 1; first auto.
sp; inline{2} 1; sp 0 3.
rcondf{2} 1; first auto.
sp 0 1.
rcondt{2} 1; first auto; smt().
sp 0 2.
rcondf{2} 1; first auto.
auto.
(* MakeInt.after_func_to_adv func' r{1} *)
exlim r{1} => r'.
seq 1 1 :
  (={glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   term_rf (glob RealFunc){1} < n /\
   r{1} = r2{2} /\ m{1} = m2{2} /\ r{1} = Some m{1} /\
   not_done{1} /\ not_done1{2} /\
   m{1}.`1 = Adv /\ m{1}.`2.`1 = adv /\ 0 < m{1}.`2.`2 /\
   func' <= m{1}.`3.`1 /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard').
call{1} (MakeInt.MI_after_func_to_adv RealFunc Adv r').
call{2} (MakeInt.MI_after_func_to_adv RealFunc DummyAdv r').
auto; progress; smt().
rcondt{2} 1; first auto.
rcondf{2} 1; first auto; progress; smt(inc_nle_l).
inline{2} 1; sp 0 2.
match None {2} 1; auto; progress.
rewrite dest_pi_gt0_implies_dec_epdp_da_from_env_fails /#.
rcondt{2} 1; first auto; progress; smt().
sp; elim* => r2' r3'.
exlim r2{2} => r2''.
seq 0 1 :
  (={glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   term_rf (glob RealFunc){1} < n /\
   not_done{1} /\ ! not_done1{2} /\
   m{1}.`1 = Adv /\ m{1}.`2.`1 = adv /\ 0 < m{1}.`2.`2 /\
   func' <= m{1}.`3.`1 /\
   r2{2} = Some m2{2} /\ 
   m2{2} =
   epdp_da_to_env.`enc
   {|dte_n = m{1}.`2.`2; dte_pt = m{1}.`3;
     dte_tag = m{1}.`4; dte_u = m{1}.`5;|} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard').
call{2} (MakeInt.MI_after_adv_to_env RealFunc DummyAdv r2'').
auto; progress.
trivial.
rewrite oget_some /epdp_da_to_env /enc_da_to_env /=.
smt(exper_pre_func_nle_env_root_addr).
rewrite oget_some /epdp_da_to_env /enc_da_to_env /=.
smt(exper_pre_adv_nle_env_root_addr).
rewrite H10 /= in H11. by rewrite -H11.
rcondf{2} 1; first auto.
sp 0 2; inline{2} 1; sp 0 3.
rcondf{2} 1; first auto.
sp 0 1.
rcondf{2} 1; first auto.
sp 0 6.
conseq
  (_ :
   ={m, not_done, glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   term_rf (glob RealFunc){1} < n /\ not_done{1} /\
   m{1}.`1 = Adv /\ m{1}.`2.`1 = adv /\ adv_to_adv{2} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' ==>
   ={r, glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   MakeInt.MI.func{1} = func' /\ MakeInt.MI.in_guard{1} = in_guard' /\
   MakeInt.MI.func{2} = func' /\ MakeInt.MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard') => //.
progress; smt().
transitivity{1}
  {r <@ RealLeft.f(m);}
  (={m, glob RealFunc, glob Adv, glob MI, glob CombEnvAdv} /\ not_done{1} ==>
   ={r, glob RealFunc, glob Adv, glob MI, glob CombEnvAdv})
  (={m, glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   term_rf (glob RealFunc){1} < n /\ not_done{2} /\
   m{1}.`1 = Adv /\ m{1}.`2.`1 = adv /\ adv_to_adv{2} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' ==>
   ={r, glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   MakeInt.MI.func{1} = func' /\ MakeInt.MI.in_guard{1} = in_guard' /\
   MakeInt.MI.func{2} = func' /\ MakeInt.MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard') => //.
progress.
by exists (glob Adv){2} (glob RealFunc){2} MI.func{1} MI.in_guard{1}
          CombEnvAdv.func{1} CombEnvAdv.in_guard{1} m{2}.
inline{2} 1; sp. rcondt{1} 1; first auto. rcondt{2} 1; first auto. sim.
transitivity{2}
  {r <@ RealRight.f(m);}
  (={m, glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   term_rf (glob RealFunc){1} < n /\ not_done{2} /\
   m{1}.`1 = Adv /\ m{1}.`2.`1 = adv /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' ==>
   ={r, glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   MakeInt.MI.func{1} = func' /\ MakeInt.MI.in_guard{1} = in_guard' /\
   MakeInt.MI.func{2} = func' /\ MakeInt.MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard')
  (={m, glob RealFunc, glob Adv, glob MI, glob CombEnvAdv} /\
   not_done{2} /\ adv_to_adv{2} ==>
   ={r, glob RealFunc, glob Adv, glob MI, glob CombEnvAdv}) => //.
progress.
by exists (glob Adv){2} (glob RealFunc){2} MI.func{1} MI.in_guard{1}
          MI.func{1} MI.in_guard{1} m{2} true.
exlim (term_rf (glob RealFunc){1}) => tm.
case @[ambient] (0 <= tm < n) => [tm_ok | tm_not_ok].
have induct := IH tm _ => //.
call induct; first auto.
exfalso; smt(ge0_term_rf).
inline{1} 1; sp. rcondt{1} 1; first auto. rcondt{2} 1; first auto. sim => />.
qed.

local lemma bridge_real (func' : addr, in_guard' : int fset) &m :
  exper_pre func' =>
  Pr[Exper(MI(RealFunc, Adv), Env).main(func', in_guard') @ &m : res] =
  Pr[Exper(MI(RealFunc, DummyAdv), CombEnvAdv(Env, Adv))
       .main(func', in_guard') @ &m : res].
proof.
move => ep_func'.
byequiv => //; proc; inline*; sp; wp.
seq 2 10 :
  (={glob RealFunc, glob Adv, glob Env} /\ invar_rf (glob RealFunc){1} /\
   func{1} = func' /\ in_guard{1} = in_guard' /\
   func0{2} = func' /\ in_guard0{2} = in_guard' /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard').
swap{2} 6 4; swap{2} 1 8.
call (_ : true).
call RealFunc_init.
auto.
call
  (_ :
   ={glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard').
proc.
if => //.
inline{1} 1; inline{2} 1; sp 3 4.
case (m0{1}.`1 = Dir).
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
rcondt{1} 1; first auto; progress; smt(le_refl).
rcondf{2} 1; first auto; progress; smt(inc_ne_func_adv).
inline{2} 1; sp.
rcondt{2} 1; first auto.
inline{2} 1; sp 0 3.
rcondt{2} 1; first auto.
rcondt{2} 1; first auto; progress; smt(le_refl).
seq 1 1 :
  (={glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   r0{1} = r2{2} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard').
exlim (glob RealFunc){1} => grf.
call (RealFunc_invoke (term_rf grf)).
auto.
case (MakeInt.after_func_error func' r0{1}).
seq 1 1 :
  (={glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   r0{1} = r2{2} /\ r0{1} = None /\
   not_done{1} = not_done0{2} /\ not_done{1} = false /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard').
call{1} (MakeInt.MI_after_func_error RealFunc Adv).
call{2} (MakeInt.MI_after_func_error RealFunc DummyAdv).
auto; smt().
rcondf{1} 1; first auto. rcondf{2} 1; first auto.
sp; inline{2} 1; sp 0 3.
rcondt{2} 1; first auto.
sp 0 2.
rcondf{2} 1; first auto.
auto.
case (MakeInt.after_func_to_env func' r0{1}).
exlim r0{1} => r0'.
seq 1 1 :
  (={glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   r0{1} = r2{2} /\ m0{1} = m2{2} /\ r0{1} = Some m0{1} /\
   ! not_done{1} /\ ! not_done0{2} /\
   MakeInt.after_func_to_env func' r0{1} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard').
call{1} (MakeInt.MI_after_func_to_env RealFunc Adv r0').
call{2} (MakeInt.MI_after_func_to_env RealFunc DummyAdv r0').
auto; smt().
rcondf{1} 1; first auto. rcondf{2} 1; first auto.
sp; inline{2} 1; sp 0 3.
rcondf{2} 1; first auto.
sp 0 1.
rcondt{2} 1; first auto; smt().
sp 0 2.
rcondf{2} 1; first auto.
auto.
(* MakeInt.after_func_to_adv func' r0{1} *)
exlim r0{1} => r0'.
seq 1 1 :
  (={glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   r0{1} = r2{2} /\ m0{1} = m2{2} /\ r0{1} = Some m0{1} /\
   not_done{1} /\ not_done0{2} /\
   m0{1}.`1 = Adv /\ m0{1}.`2.`1 = adv /\ 0 < m0{1}.`2.`2 /\
   func' <= m0{1}.`3.`1 /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard').
call{1} (MakeInt.MI_after_func_to_adv RealFunc Adv r0').
call{2} (MakeInt.MI_after_func_to_adv RealFunc DummyAdv r0').
auto; progress; smt().
rcondt{2} 1; first auto.
rcondf{2} 1; first auto; progress; smt(inc_nle_l).
inline{2} 1; sp 0 2.
match None {2} 1; auto; progress.
rewrite dest_pi_gt0_implies_dec_epdp_da_from_env_fails /#.
rcondt{2} 1; first auto; progress; smt().
sp; elim* => r2' r3'.
exlim r2{2} => r2''.
seq 0 1 :
  (={glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   not_done{1} /\ ! not_done0{2} /\
   m0{1}.`1 = Adv /\ m0{1}.`2.`1 = adv /\ 0 < m0{1}.`2.`2 /\
   func' <= m0{1}.`3.`1 /\
   r2{2} = Some m2{2} /\ 
   m2{2} =
   epdp_da_to_env.`enc
   {|dte_n = m0{1}.`2.`2; dte_pt = m0{1}.`3;
     dte_tag = m0{1}.`4; dte_u = m0{1}.`5;|} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard').
call{2} (MakeInt.MI_after_adv_to_env RealFunc DummyAdv r2'').
auto; progress.
trivial.
rewrite oget_some /epdp_da_to_env /enc_da_to_env /=.
smt(exper_pre_func_nle_env_root_addr).
rewrite oget_some /epdp_da_to_env /enc_da_to_env /=.
smt(exper_pre_adv_nle_env_root_addr).
rewrite H9 /= in H10; by rewrite -H10.
rcondf{2} 1; first auto.
sp 0 2; inline{2} 1; sp 0 3.
rcondf{2} 1; first auto.
sp 0 1.
rcondf{2} 1; first auto.
sp 0 6.
conseq
  (_ :
   ={m0, not_done, glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   not_done{1} /\
   m0{1}.`1 = Adv /\ m0{1}.`2.`1 = adv /\ adv_to_adv{2} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' ==>
   ={r0, glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   MakeInt.MI.func{1} = func' /\ MakeInt.MI.in_guard{1} = in_guard' /\
   MakeInt.MI.func{2} = func' /\ MakeInt.MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard') => //.
progress; smt().
transitivity{1}
  {r0 <@ RealLeft.f(m0);}
  (={m0, glob RealFunc, glob Adv, glob MI, glob CombEnvAdv} /\ not_done{1} ==>
   ={r0, glob RealFunc, glob Adv, glob MI, glob CombEnvAdv})
  (={m0, glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   not_done{2} /\
   m0{1}.`1 = Adv /\ m0{1}.`2.`1 = adv /\ adv_to_adv{2} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' ==>
   ={r0, glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   MakeInt.MI.func{1} = func' /\ MakeInt.MI.in_guard{1} = in_guard' /\
   MakeInt.MI.func{2} = func' /\ MakeInt.MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard') => //.
progress.
by exists (glob Adv){2} (glob RealFunc){2} MI.func{1} MI.in_guard{1}
          CombEnvAdv.func{1} CombEnvAdv.in_guard{1} m0{2}.
inline{2} 1; sp. rcondt{1} 1; first auto. rcondt{2} 1; first auto. sim.
transitivity{2}
  {r0 <@ RealRight.f(m0);}
  (={m0, glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   not_done{2} /\
   m0{1}.`1 = Adv /\ m0{1}.`2.`1 = adv /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' ==>
   ={r0, glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   MakeInt.MI.func{1} = func' /\ MakeInt.MI.in_guard{1} = in_guard' /\
   MakeInt.MI.func{2} = func' /\ MakeInt.MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard')
  (={m0, glob RealFunc, glob Adv, glob MI, glob CombEnvAdv} /\
   not_done{2} /\ adv_to_adv{2} ==>
   ={r0, glob RealFunc, glob Adv, glob MI, glob CombEnvAdv}) => //.
progress.
by exists (glob Adv){2} (glob RealFunc){2} MI.func{1} MI.in_guard{1}
          MI.func{1} MI.in_guard{1} m0{2} true.
exlim (glob RealFunc){1} => grf.
have bri := bridge_real_induct func' in_guard' ep_func' (term_rf grf).
call bri; first auto.
inline{1} 1; sp. rcondt{1} 1; first auto. rcondt{2} 1; first auto. sim => />.
conseq
  (_ :
   ={m0, not_done, glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   not_done{1} /\
   m0{1}.`1 = Adv /\ m0{1}.`2.`1 = adv /\ adv_to_adv{2} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' ==>
   ={r, glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   MakeInt.MI.func{1} = func' /\ MakeInt.MI.in_guard{1} = in_guard' /\
   MakeInt.MI.func{2} = func' /\ MakeInt.MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard') => //.
progress; smt().
transitivity{1}
  {r <@ RealLeft.f(m0);}
  (={m0, glob RealFunc, glob Adv, glob MI, glob CombEnvAdv} /\ not_done{1} ==>
   ={r, glob RealFunc, glob Adv, glob MI, glob CombEnvAdv})
  (={m0, glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   not_done{2} /\
   m0{1}.`1 = Adv /\ m0{1}.`2.`1 = adv /\ adv_to_adv{2} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' ==>
   ={r, glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   MakeInt.MI.func{1} = func' /\ MakeInt.MI.in_guard{1} = in_guard' /\
   MakeInt.MI.func{2} = func' /\ MakeInt.MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard') => //.
progress.
by exists (glob Adv){2} (glob RealFunc){2} MI.func{1} MI.in_guard{1}
          CombEnvAdv.func{1} CombEnvAdv.in_guard{1} m0{2}.
inline{2} 1; sp. rcondt{1} 1; first auto. rcondt{2} 1; first auto. sim.
transitivity{2}
  {r <@ RealRight.f(m0);}
  (={m0, glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   not_done{2} /\
   m0{1}.`1 = Adv /\ m0{1}.`2.`1 = adv /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' ==>
   ={r, glob RealFunc, glob Adv} /\ invar_rf (glob RealFunc){1} /\
   MakeInt.MI.func{1} = func' /\ MakeInt.MI.in_guard{1} = in_guard' /\
   MakeInt.MI.func{2} = func' /\ MakeInt.MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard')
  (={m0, glob RealFunc, glob Adv, glob MI, glob CombEnvAdv} /\
   not_done{2} /\ adv_to_adv{2} ==>
   ={glob RealFunc, glob Adv, glob MI, glob CombEnvAdv, r}) => //.
progress.
by exists (glob Adv){2} (glob RealFunc){2} MI.func{1} MI.in_guard{1}
          MI.func{1} MI.in_guard{1} m0{2} true.
exlim (glob RealFunc){1} => grf.
have bri := bridge_real_induct func' in_guard' ep_func' (term_rf grf).
call bri; first auto.
inline{1} 1; sp. rcondt{1} 1; first auto. rcondt{2} 1; first auto. sim => />.
auto.
auto.
qed.

lemma dpi_ne_sim_adv_pi_suff_from_disj_mg (m : msg, ig : int fset, func : addr) :
  disjoint ig (fset1 sim_adv_pi) => main_guard func ig m =>
  m.`1 = Adv =>  m.`2.`2 <> sim_adv_pi.
proof.
move => disj_ig_sim_adv_pi mg m_adv.
case (m.`2.`2 = sim_adv_pi) => [m_dpi_eq_sap | //].
move : mg.
rewrite /main_guard => [[/# | [#] _ _ [| [#] _ m_dpi_in_ig _]]].
smt(sim_adv_pi_ge1).
rewrite m_dpi_eq_sap in m_dpi_in_ig.
rewrite disjointP in disj_ig_sim_adv_pi; have := disj_ig_sim_adv_pi sim_adv_pi.
by rewrite in_fset1 /=.
qed.

local lemma bridge_ideal (func' : addr, in_guard' : int fset) &m :
  exper_pre func' => disjoint in_guard' (fset1 sim_adv_pi) =>
  Pr[Exper(MI(IdealFunc, MS(SimCore, Adv)), Env)
       .main(func', in_guard') @ &m : res] =
  Pr[Exper(MI(IdealFunc, MS(SimCore, DummyAdv)), CombEnvAdv(Env, Adv))
       .main(func', in_guard') @ &m : res].
proof.
move => ep_func' disj_ig'.
byequiv => //; proc; inline*; sp; wp.
seq 4 12 :
  (={glob MS, glob IdealFunc, glob SimCore, glob Adv, glob Env} /\
   invar_if (glob IdealFunc){2} /\
   func{1} = func' /\ in_guard{1} = in_guard' /\
   func0{2} = func' /\ in_guard0{2} = in_guard' /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' /\
   MS.if_addr_opt{1} = None).
swap{1} 1 1; swap{2} 8 4; swap{2} 3 8; swap{2} 1 9.
call (_ : true).
call (_ : true).
call IdealFunc_init.
auto.
call
  (_ :
   ={glob IdealFunc, glob SimCore, glob MS, glob Adv} /\
   invar_if (glob IdealFunc){1} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' /\
   (* with our actual ideal functionalities, <= will actually be = *)
   (MS.if_addr_opt{1} <> None => func' <= oget MS.if_addr_opt{1})).
proc.
if => //.
inline{1} 1; inline{2} 1; sp 3 4.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
case (m0{1}.`1 = Dir).
rcondt{1} 1; first auto; progress; smt(le_refl).
rcondf{2} 1; first auto; progress; smt(inc_ne_func_adv).
inline{2} 1; sp.
rcondt{2} 1; first auto.
inline{2} 1; sp 0 3.
rcondt{2} 1; first auto.
rcondt{2} 1; first auto; progress; smt(le_refl).
seq 1 1 :
  (r0{1} = r2{2} /\
   (r0{1} <> None /\ (oget r0{1}).`1 = Adv =>
    (oget r0{1}).`2.`2 = sim_adv_pi /\ (oget r0{1}).`3.`2 = 1) /\
   ={glob IdealFunc, glob SimCore, glob MS, glob Adv} /\
   invar_if (glob IdealFunc){1} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' /\
   (MS.if_addr_opt{1} <> None => func' <= oget MS.if_addr_opt{1})).
exlim (term_if (glob IdealFunc){1}) => n.
call (IdealFunc_invoke n).
auto; progress; smt().
case (MakeInt.after_func_error func' r0{1}).
seq 1 1 :
  (={glob IdealFunc, glob SimCore, glob MS, glob Adv} /\
   invar_if (glob IdealFunc){1} /\
   r0{1} = r2{2} /\ r0{1} = None /\
   not_done{1} = not_done0{2} /\ not_done{1} = false /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' /\
   (MS.if_addr_opt{1} <> None => func' <= oget MS.if_addr_opt{1})).
call{1}
  (MakeInt.MI_after_func_error IdealFunc
   (MS(SimCore, Adv))).
call{2}
  (MakeInt.MI_after_func_error IdealFunc
   (MS(SimCore, DummyAdv))).
auto; smt().
rcondf{1} 1; first auto. rcondf{2} 1; first auto.
sp; inline{2} 1; sp 0 3.
rcondt{2} 1; first auto.
sp 0 2.
rcondf{2} 1; first auto.
auto.
case (MakeInt.after_func_to_env func' r0{1}).
exlim r0{1} => r0'.
seq 1 1 :
  (={glob IdealFunc, glob SimCore, glob MS, glob Adv} /\
   invar_if (glob IdealFunc){1} /\
   r0{1} = r2{2} /\ m0{1} = m2{2} /\ r0{1} = Some m0{1} /\
   ! not_done{1} /\ ! not_done0{2} /\
   MakeInt.after_func_to_env func' r0{1} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' /\
   (MS.if_addr_opt{1} <> None => func' <= oget MS.if_addr_opt{1})).
call{1}
  (MakeInt.MI_after_func_to_env IdealFunc
   (MS(SimCore, Adv)) r0').
call{2}
  (MakeInt.MI_after_func_to_env IdealFunc
   (MS(SimCore, DummyAdv)) r0').
auto; smt().
rcondf{1} 1; first auto. rcondf{2} 1; first auto.
sp; inline{2} 1; sp 0 3.
rcondf{2} 1; first auto.
sp 0 1.
rcondt{2} 1; first auto; smt().
sp 0 2.
rcondf{2} 1; first auto.
auto.
(* MakeInt.after_func_to_adv func' r0{1} *)
exlim r0{1} => r0'.
seq 1 1 :
  (={glob IdealFunc, glob SimCore, glob MS, glob Adv} /\
   invar_if (glob IdealFunc){1} /\
   r0{1} = r2{2} /\ m0{1} = m2{2} /\ r0{1} = Some m0{1} /\
   not_done{1} /\ not_done0{2} /\
   m0{1}.`1 = Adv /\ m0{1}.`2.`1 = adv /\ m0{1}.`2.`2 = sim_adv_pi /\
   func' <= m0{1}.`3.`1 /\ m0{1}.`3.`2 = 1 /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' /\
   (MS.if_addr_opt{1} <> None => func' <= oget MS.if_addr_opt{1})).
call{1}
  (MakeInt.MI_after_func_to_adv IdealFunc
   (MS(SimCore, Adv)) r0').
call{2}
  (MakeInt.MI_after_func_to_adv IdealFunc
   (MS(SimCore, DummyAdv)) r0').
auto; progress; smt().
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
rcondf{1} 1; first auto; progress; smt(inc_nle_l).
rcondf{2} 1; first auto; progress; smt(inc_nle_l).
inline{1} 1; inline{2} 1; sp.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
if => //.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sp; inline{1} 1; inline{2} 1; sp 3 3.
conseq
  (_ :
   ={glob IdealFunc, glob SimCore, MS.if_addr_opt, glob Adv} /\
   invar_if (glob IdealFunc){1} /\
   not_done0{1} /\ not_done1{2} /\ m2{1} = m4{2} /\
   m2{1}.`1 = Adv /\ m2{1}.`2.`1 = adv /\ m2{1}.`2.`2 = sim_adv_pi /\
   func' <= m2{1}.`3.`1 /\ m2{1}.`3.`2 = 1 /\
   MS.if_addr_opt{1} = Some m2{1}.`3.`1 /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' ==>
   ={r, glob IdealFunc, glob SimCore, MS.if_addr_opt, glob Adv} /\
   invar_if (glob IdealFunc){1} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' /\
   (MS.if_addr_opt{1} <> None => func' <= oget MS.if_addr_opt{1})) => //.
admit.
if => //.
inline{1} 1; inline{2} 1; sp.
conseq
  (_ :
   ={glob IdealFunc, glob SimCore, MS.if_addr_opt, glob Adv} /\
   invar_if (glob IdealFunc){1} /\
   not_done0{1} /\ not_done1{2} /\ m2{1} = m4{2} /\
   m2{1}.`1 = Adv /\ m2{1}.`2.`1 = adv /\ m2{1}.`2.`2 = sim_adv_pi /\
   func' <= m2{1}.`3.`1 /\ m2{1}.`3.`2 = 1 /\
   MS.if_addr_opt{1} = Some m2{1}.`3.`1 /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' ==>
   ={r, glob IdealFunc, glob SimCore, MS.if_addr_opt, glob Adv} /\
   invar_if (glob IdealFunc){1} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' /\
   (MS.if_addr_opt{1} <> None => func' <= oget MS.if_addr_opt{1})) => //.
progress; smt(oget_some).
admit.
sp.
seq 1 1 :
  (={glob IdealFunc, glob SimCore, glob MS, glob Adv} /\
   invar_if (glob IdealFunc){1} /\
   r0{1} = None /\ r2{2} = None /\ !not_done{1} /\ !not_done0{2} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' /\
   (MS.if_addr_opt{1} <> None => func' <= oget MS.if_addr_opt{1})).
call{1}
  (MakeInt.MI_after_adv_error IdealFunc
   (MS(SimCore, Adv))).
call{2}
  (MakeInt.MI_after_adv_error IdealFunc
   (MS(SimCore, DummyAdv))).
auto; smt().
rcondf{1} 1; first auto. rcondf{2} 1; first auto.
inline{2} 3; sp 0 5.
rcondt{2} 1; first auto. rcondf{2} 3; first auto.
auto.
rcondt{2} 1; first auto; progress; smt().
rcondf{1} 1; first auto; progress; smt(inc_nle_l).
inline{1} 1; sp.
rcondf{1} 1; first auto; progress; smt(dpi_ne_sim_adv_pi_suff_from_disj_mg).
inline{1} 1; sp.
rcondt{1} 1; first auto.
rcondt{1} 1; first auto; progress; smt().
rcondf{1} 1; first auto; progress; smt(dpi_ne_sim_adv_pi_suff_from_disj_mg).
seq 1 1 :
  (={glob IdealFunc, glob SimCore, glob MS, glob Adv} /\
   invar_if (glob IdealFunc){1} /\ r2{1} = r0{2} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' /\
   (MS.if_addr_opt{1} <> None => func' <= oget MS.if_addr_opt{1})).
call (_ : true); first auto.
inline{2} 1; sp 0 3.
case (after_adv_error r2{1}).
seq 1 0 :
  (={glob IdealFunc, glob SimCore, glob MS, glob Adv} /\
   invar_if (glob IdealFunc){1} /\ r2{1} = None /\ !not_done0{1} /\
   after_adv_error r1{2} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' /\
   (MS.if_addr_opt{1} <> None => func' <= oget MS.if_addr_opt{1})).
call{1} (MS_after_adv_error SimCore Adv); first auto.
rcondf{1} 1; first auto.
sp 2 0.
seq 1 0 :
  (={glob IdealFunc, glob SimCore, glob MS, glob Adv} /\
   invar_if (glob IdealFunc){1} /\ r0{1} = None /\ !not_done{1} /\
   after_adv_error r1{2} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' /\
   (MS.if_addr_opt{1} <> None => func' <= oget MS.if_addr_opt{1})).
call{1}
  (MakeInt.MI_after_adv_error IdealFunc
   (MS(SimCore, Adv))).
auto.
rcondf{1} 1; first auto.
if{2}.
sp 1 2.
rcondf{2} 1; first auto.
auto.
sp 0 1.
if{2}.
sp 1 3.
rcondf{2} 1; first auto.
auto.
if{2}.
rcondt{2} 1; first auto; progress.
rewrite !negb_or in H4.
case ((oget r1{hr}).`2.`1 <> env_root_addr) => [/# |].
smt(negb_or ge_nil le_trans inc_nle_l).
rcondf{2} 4; first auto.
auto.
sp 0 1.
rcondt{2} 1; first auto; progress; smt().
rcondf{2} 3; first auto.
auto.
case (after_adv_return MS.if_addr_opt{1} r2{1}).
seq 1 0 :
  (={glob IdealFunc, glob SimCore, glob MS, glob Adv} /\
   invar_if (glob IdealFunc){1} /\
   r2{1} = r1{2} /\ r2{1} = Some m2{1} /\ !not_done0{1} /\
   after_adv_return MS.if_addr_opt{1} r2{1} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' /\
   (MS.if_addr_opt{1} <> None => func' <= oget MS.if_addr_opt{1})).
exlim r2{1} => r2'.
call{1} (MS_after_adv_return SimCore Adv r2'); first auto.
rcondf{1} 1; first auto.
sp 2 0.
case (MakeInt.after_adv_to_env func' r0{1}).
seq 1 0 :
  (={glob IdealFunc, glob SimCore, glob MS, glob Adv} /\
   invar_if (glob IdealFunc){1} /\
   r0{1} = r1{2} /\ r0{1} = Some m0{1} /\ !not_done{1} /\
   after_adv_return MS.if_addr_opt{1} r0{1} /\
   MakeInt.after_adv_to_env func' r0{1} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' /\
   (MS.if_addr_opt{1} <> None => func' <= oget MS.if_addr_opt{1})).
exlim r0{1} => r0'.
call{1}
  (MakeInt.MI_after_adv_to_env IdealFunc
   (MS(SimCore, Adv)) r0').
auto; smt().
rcondf{1} 1; first auto.
rcondf{2} 1; first auto.
rcondf{2} 2; first auto; smt().
rcondf{2} 2; first auto; smt().
rcondf{2} 3; first auto; smt().
rcondf{2} 4; first auto.
auto.
conseq
  (_ :
   ={glob IdealFunc, glob SimCore, glob MS, glob Adv} /\
   invar_if (glob IdealFunc){1} /\
   r0{1} = r1{2} /\
   after_adv_return MS.if_addr_opt{1} r0{1} /\
   MakeInt.after_adv_to_func func' r0{1} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' /\
   (MS.if_addr_opt{1} <> None => func' <= oget MS.if_addr_opt{1}) ==>
   _).
progress [-delta].
have [error | //] :
  MakeInt.after_adv_error MakeInt.MI.func{1} (Some m2{1}) \/
  MakeInt.after_adv_to_func MakeInt.MI.func{1} (Some m2{1}).
  smt().
have // : false.
  move : error; rewrite /MakeInt.after_adv_error.
  smt(ge_nil le_trans inc_nle_l).  
seq 1 0 :
  (={glob IdealFunc, glob SimCore, glob MS, glob Adv} /\
   invar_if (glob IdealFunc){1} /\
   r0{1} = r1{2} /\ r0{1} = Some m0{1} /\ not_done{1} /\
   after_adv_return MS.if_addr_opt{1} r0{1} /\
   MakeInt.after_adv_to_func func' r0{1} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' /\
   (MS.if_addr_opt{1} <> None => func' <= oget MS.if_addr_opt{1})).
exlim r0{1} => r0'.
call{1}
  (MakeInt.MI_after_adv_to_func IdealFunc
   (MS(SimCore, Adv)) r0'); first auto.
rcondt{1} 1; first auto.
rcondt{1} 1; first auto; progress; smt().
rcondf{2} 1; first auto.
rcondf{2} 2; first auto; progress; smt(inc_le1_not_rl).
rcondt{2} 2; first auto; smt().
rcondf{2} 2; first auto; smt().
sp.
rcondt{2} 1; first auto.
rcondf{2} 1; first auto.
inline{2} 1; sp.
rcondt{2} 1; first auto.
inline{2} 1; sp.
rcondt{2} 1; first auto.
rcondf{2} 1; first auto; progress.
rewrite /epdp_da_from_env /enc_da_from_env /=.
smt(inc_nle_l).
inline{2} 1; sp.
rcondf{2} 1; first auto; progress.
rewrite /epdp_da_from_env /enc_da_from_env /=.
smt(sim_adv_pi_ge1).
inline{2} 1; sp.
rcondt{2} 1; first auto.
rcondt{2} 1; first auto.
rcondf{2} 1; first auto; progress.
rewrite /epdp_da_from_env /enc_da_from_env /=.
smt(sim_adv_pi_ge1).
inline{2} 1; sp.
elim* => r1_R.
match Some {2} 1; first auto; progress; smt().
rcondt{2} 1; first auto => /> &hr <- /=.
progress; smt(exper_pre_func_nle_env_root_addr inc_le1_not_rl).
sp; elim* => r5_R r6_R.
seq 0 1 :
  (={glob IdealFunc, glob SimCore, glob MS, glob Adv} /\
   invar_if (glob IdealFunc){1} /\
   m0{1} = m5{2} /\ r5{2} = Some m5{2} /\ !not_done2{2} /\
   after_adv_return MS.if_addr_opt{1} r5{2} /\
   MakeInt.after_adv_to_func func' r5{2} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' /\
   (MS.if_addr_opt{1} <> None => func' <= oget MS.if_addr_opt{1})).
exlim r5{2} => r5'.
call{2} (MS_after_adv_return SimCore DummyAdv r5'); first auto.
move => |> &1 &2 <- /=.
progress [-delta].
rewrite /after_adv_return /= /#.
rewrite H5 /= in H6. rewrite -H6 /#.
smt(). smt().
rcondf{2} 1; first auto.
sp.
seq 0 1 :
  (={glob IdealFunc, glob SimCore, glob MS, glob Adv} /\
   invar_if (glob IdealFunc){1} /\
   m0{1} = m3{2} /\ not_done1{2} /\
   MakeInt.after_adv_to_func func' (Some m3{2}) /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' /\
   (MS.if_addr_opt{1} <> None => func' <= oget MS.if_addr_opt{1})).
exlim r3{2} => r3'.
call{2}
  (MakeInt.MI_after_adv_to_func IdealFunc
   (MS(SimCore, DummyAdv)) r3'); first auto; smt().
rcondt{2} 1; first auto.
rcondt{2} 1; first auto; progress; smt().
admit.
seq 1 0 :
  (={glob IdealFunc, glob SimCore, glob MS, glob Adv} /\
   invar_if (glob IdealFunc){1} /\
   r2{1} = r1{2} /\ r2{1} = Some m2{1} /\ not_done0{1} /\
   after_adv_continue MS.if_addr_opt{1} r2{1} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' /\
   (MS.if_addr_opt{1} <> None => func' <= oget MS.if_addr_opt{1})).
exlim r2{1} => r2'.
call{1} (MS_after_adv_continue SimCore Adv r2');
  first auto; progress [-delta]; smt().
rcondf{2} 1; first auto.
rcondf{2} 2; first auto; progress; smt().
rcondt{2} 2; first auto; progress; smt(le_trans).
rcondf{2} 2; first auto; progress.
case (m2{m0}.`3.`2 = 0) => [eq0_spi | //].
have eq_nil_dest_addr : m2{m0}.`2.`1 = [] by smt().
have le_func_nil : MakeInt.MI.func{m0} <= [] by smt(le_trans).
have le_func_adv : MakeInt.MI.func{m0} <= adv.
  rewrite (le_trans []) 1:le_func_nil ge_nil.
smt(inc_nle_l).
sp; elim* => r1_R.
rcondt{2} 1; first auto.
rcondf{2} 1; first auto.
inline{2} 1; sp.
rcondt{2} 1; first auto.
inline{2} 1; sp.
rcondt{2} 1; first auto.
rcondf{2} 1; first auto; progress.
rewrite /epdp_da_from_env /enc_da_from_env /=.
smt(inc_nle_l).
inline{2} 1; sp.
rcondf{2} 1; first auto; progress.
rewrite /epdp_da_from_env /enc_da_from_env /=.
smt(sim_adv_pi_ge1).
inline{2} 1; sp.
rcondt{2} 1; first auto.
rcondt{2} 1; first auto.
rcondf{2} 1; first auto; progress.
rewrite /epdp_da_from_env /enc_da_from_env /=.
smt(sim_adv_pi_ge1).
inline{2} 1; sp.
match Some {2} 1; first auto; progress; smt().
rcondt{2} 1; first auto => /> &hr <- /=.
smt(inc_nle_l inc_le1_not_rl ge_nil le_trans).
sp; elim* => r5_R r6_R.
seq 0 1 :
  (={glob IdealFunc, glob SimCore, glob MS, glob Adv} /\
   invar_if (glob IdealFunc){1} /\
   m2{1} = m5{2} /\ r5{2} = Some m5{2} /\ not_done0{1} /\ not_done2{2} /\
   after_adv_continue MS.if_addr_opt{1} r5{2} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' /\
   (MS.if_addr_opt{1} <> None => func' <= oget MS.if_addr_opt{1})).
exlim r5{2} => r5'.
call{2} (MS_after_adv_continue SimCore DummyAdv r5'); first auto.
move => |> &1 &2 <- /=.
progress [-delta].
rewrite /after_adv_continue /= /#.
rewrite H4 /= in H5. rewrite -H5 /#.
smt().
conseq
  (_ :
   ={glob IdealFunc, glob SimCore, MS.if_addr_opt, glob Adv} /\
   invar_if (glob IdealFunc){1} /\
   not_done0{1} /\ not_done2{2} /\ m2{1} = m5{2} /\
   MS.if_addr_opt{1} <> None /\ func' <= oget MS.if_addr_opt{1} /\
   oget MS.if_addr_opt{1} <= m2{1}.`2.`1 /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' ==>
   ={r, glob IdealFunc, glob SimCore, MS.if_addr_opt, glob Adv} /\
   invar_if (glob IdealFunc){1} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MI.func{2} = func' /\ MI.in_guard{2} = in_guard' /\
   CombEnvAdv.func{2} = func' /\ CombEnvAdv.in_guard{2} = in_guard' /\
   (MS.if_addr_opt{1} <> None => func' <= oget MS.if_addr_opt{1})) => //.
progress; smt().
admit.
auto.
auto.
qed.

lemma dummy_adv (func' : addr, in_guard' : int fset, b : real) &m :
  exper_pre func' => disjoint in_guard' (fset1 sim_adv_pi) =>
  `|Pr[Exper(MI(RealFunc, DummyAdv), CombEnvAdv(Env, Adv))
         .main(func', in_guard') @ &m : res] -
    Pr[Exper(MI(IdealFunc, MS(SimCore, DummyAdv)), CombEnvAdv(Env, Adv))
         .main(func', in_guard') @ &m : res]| <= b =>
  `|Pr[Exper(MI(RealFunc, Adv), Env).main(func', in_guard') @ &m : res] -
    Pr[Exper(MI(IdealFunc, MS(SimCore, Adv)), Env)
         .main(func', in_guard') @ &m : res]| <= b.
proof.
move => ep_func' disj_ig' reduct.
by rewrite bridge_real // bridge_ideal.
qed.

end section.

lemma dummy_adversary
      (Env <: ENV{-MI, -MS, -CombEnvAdv})
      (Adv <: ADV{-MI, -MS, -CombEnvAdv, -Env})
      (RealFunc <: FUNC{-MI, -CombEnvAdv, -Env, -Adv})
      (IdealFunc <: FUNC{-MI, -MS, -CombEnvAdv, -Env, -Adv})
      (SimCore <: ADV{-MI, -MS, -CombEnvAdv, -Env, -Adv, -IdealFunc})
      (invar_rf : glob RealFunc -> bool, term_rf : glob RealFunc -> int,
       invar_if : glob IdealFunc -> bool, term_if : glob IdealFunc -> int,
       invar_sc : glob SimCore -> bool, term_sc : glob SimCore -> int,
       func' : addr, in_guard' : int fset, b : real) &m :
  (forall (gl : glob RealFunc), invar_rf gl => 0 <= term_rf gl) =>
  hoare [RealFunc.init : true ==> invar_rf (glob RealFunc)] =>
  (forall (n : int),
   hoare
   [RealFunc.invoke :
    invar_rf (glob RealFunc) /\ term_rf (glob RealFunc) = n ==>
    invar_rf (glob RealFunc) /\
    (res <> None => term_rf (glob RealFunc) < n)]) =>
  (forall (gl : glob IdealFunc), invar_if gl => 0 <= term_if gl) =>
  hoare [IdealFunc.init : true ==> invar_if (glob IdealFunc)] =>
  (forall (n : int),
   hoare
   [IdealFunc.invoke :
    invar_if (glob IdealFunc) /\ term_if (glob IdealFunc) = n ==>
    invar_if (glob IdealFunc) /\
    (res <> None =>
     term_if (glob IdealFunc) < n /\
     ((oget res).`1 = Adv =>
      (oget res).`2.`2 = sim_adv_pi /\ (oget res).`3.`2 = 1))]) =>
  (forall (gl : glob SimCore), invar_sc gl => 0 <= term_sc gl) =>
  hoare [SimCore.init : true ==> invar_sc (glob SimCore)] =>
  (forall (n : int),
   hoare
   [SimCore.invoke :
    invar_sc (glob SimCore) /\ term_sc (glob SimCore) = n ==>
    invar_sc (glob SimCore) /\
    (res <> None => term_sc (glob SimCore) < n)]) =>
  exper_pre func' => disjoint in_guard' (fset1 sim_adv_pi) =>
  `|Pr[Exper(MI(RealFunc, DummyAdv), CombEnvAdv(Env, Adv))
         .main(func', in_guard') @ &m : res] -
    Pr[Exper(MI(IdealFunc, MS(SimCore, DummyAdv)), CombEnvAdv(Env, Adv))
         .main(func', in_guard') @ &m : res]| <= b =>
  `|Pr[Exper(MI(RealFunc, Adv), Env).main(func', in_guard') @ &m : res] -
    Pr[Exper(MI(IdealFunc, MS(SimCore, Adv)), Env)
         .main(func', in_guard') @ &m : res]| <= b.
proof.
move =>
  ge0_term_rf rf_init rf_invoke
  ge0_term_if if_init if_invoke
  ge0_term_sc sc_init sc_invoke
  ep_func' disj_ig' reduct.
apply
  (dummy_adv
   Env Adv RealFunc IdealFunc SimCore
   invar_rf term_rf invar_if term_if invar_sc term_sc
   ge0_term_rf _ _ ge0_term_if _ _ ge0_term_sc _ _
   func' in_guard' b &m) => //.
by apply (init_invar_hoare_implies_equiv RealFunc).
move => n.
rewrite (invoke_term_metric_hoare_implies_equiv RealFunc) rf_invoke.
by apply (init_invar_hoare_implies_equiv IdealFunc).
move => n.
by rewrite
   (invoke_term_metric_adv_pi_hoare_implies_equiv IdealFunc _ _ _ sim_adv_pi)
   if_invoke.
by apply (adv_init_invar_hoare_implies_equiv SimCore).
move => n.
rewrite (adv_invoke_term_metric_hoare_implies_equiv SimCore) sc_invoke.
qed.

end Simulator.
