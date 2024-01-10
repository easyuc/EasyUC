(* UCCore.ec *)

(* Core UC Definitions and Lemmas *)

prover quorum=2 ["Z3" "Alt-Ergo"].

(* standard theories, encoding and partial decoding pairs (EPDPs), the
   type univ plus a number of EPDPs with target univ, addresses and
   ports *)

require export UCBasicTypes.

(* guard an optional message using predicate *)

op opt_msg_guard :
     (mode -> addr -> int -> addr -> int -> tag -> bool) ->
     msg option -> msg option =
  fun f : mode -> addr -> int -> addr -> int -> tag -> bool =>
  fun m_opt : msg option =>
    match m_opt with
    | None   => None
    | Some m =>
        if f m.`1 m.`2.`1 m.`2.`2 m.`3.`1 m.`3.`2 m.`4
        then m_opt
        else None
    end.

(* module type used for real protocols and ideal functionalities
   (collectively, "functionalities"), as well as adversaries and
   simulators *)

(* precondition for ordinary (non-adversary/simulator)
   functionalities: *)

op func_init_pre (self adv : addr) : bool = inc self adv.

(* envport0 self adv pt says that pt is part of the environment, not
   the functionality or adversary; it's allowed to be the root port,
   ([], 0) *)

op envport0 (self adv : addr, pt : port) : bool =
  ! self <= pt.`1 /\ ! adv <= pt.`1.

module type FUNC = {
  (* initialize functionality (or adversary, simulator), telling it
     its address (self) and the address of its adversary (adv)

     in the case of the adversary/simulator, the second argument will
     be [], the root address of the environment (so the
     adversary/simulator's "adversary" is the environment)

     precondition for ordinary (non-adversary/simulator)
     functionalties: func_init_pre self adv *)

  proc init(self adv : addr) : unit

  (* respond to an incoming message, producing an optional
     outgoing message (None means error)

     messages to a functionality should have addresses that are >=
     self (in the case of an adversary/simulator, = self)

     if Some m' is returned, then the destination address of m' should
     not be >= self, and the source address of m' should be >= self
     (in the case of an adversary/simulator, the source address should
     be = self) *)

  proc invoke(m : msg) : msg option
}.

(* module type of interfaces (to environment): consists of
   a functionality part and an adversary part *)

(* precondition: *)

op inter_init_pre (func adv : addr) : bool = inc func adv.

module type INTER = {
  (* initialize interface, telling it:

       * the address (func) of its functionality part;

       * the address (adv) of its adversary part;

       * an incoming message guard (in_guard)

     the interface will initialize its functionality and adversary
     parts; when calling the adversary part's init function, the
     second argument will be [], the root address of the environment

     precondition:

       inter_init_pre func adv *)

  proc init(func adv : addr, in_guard : int fset) : unit

  (* respond to an incoming message from the environment, producing an
     optional outgoing message (None means error) *)

  proc invoke(m : msg) : msg option
}.

(* module type of environments, parameterized by interfaces *)

pred env_init_pre (func adv : addr) = inter_init_pre func adv.

module type ENV (Inter : INTER) = {
  (* start environment, and let it interact with Inter (only via
     Inter.invoke, not via Inter.init), eventually returning a boolean
     judgment

     we have:

       * func is the address of interface's functionality part

       * adv is the address of interface's adversary part

     precondition : env_pre func adv *)

  proc main(func adv : addr, in_guard : int fset) : bool {Inter.invoke}
}.

abstract theory Experiment.

(* carry out experiment in which the environment is allowed to
   interact with, and issue a final boolean judgment about, an
   interface, which is first initialized *)

op exper_pre (func adv : addr) : bool = inter_init_pre func adv.

lemma exper_pre_ext1 (func adv ext : addr) :
  exper_pre func adv => exper_pre (func ++ ext) adv.
proof.
rewrite /exper_pre /inter_init_pre.
move => |> inc_fun_adv.
by apply inc_extl.
qed.

module Exper (Inter : INTER, Env : ENV) = {
  module E = Env(Inter)

  (* arguments to main:

       * func is address of interface's functionality part

       * adv is the address of the interface's adversary part

       * in_guard is the incoming message guard used by the interface
         and supplied to the environment

     precondition:

       exper_pre func adv *)

  proc main(func adv : addr, in_guard : int fset) : bool = {
    var b : bool;
    Inter.init(func, adv, in_guard);
    b <@ E.main(func, adv, in_guard);
    return b;
  }    
}.

end Experiment.

abstract theory MakeInterface.

(* make interface out of functionality and adversary parts *)

(* loop invariant for interface's while loop *)

op mi_loop_invar
     (func adv : addr, in_guard : int fset,
      r : msg option, m : msg, not_done : bool) : bool =
  inter_init_pre func adv /\
  (not_done =>
   (m.`1 = Dir /\ func = m.`2.`1 /\ envport func adv m.`3) \/
   (m.`1 = Adv /\ func <= m.`2.`1 /\ m.`3.`1 = adv /\ 0 < m.`3.`2) \/
   (m.`1 = Adv /\ m.`2.`1 = adv /\
    (func <= m.`3.`1 /\ 0 < m.`2.`2 \/
     m.`3 = ([], 0) /\ m.`2.`2 = 0 \/
     envport func adv m.`3 /\ 0 < m.`2.`2 /\
     m.`2.`2 \in in_guard))) /\
  (! not_done =>
   r = None \/
   (envport0 func adv (oget r).`2 /\
    ((oget r).`1 = Dir /\ (oget r).`2 <> ([], 0) /\
      func = (oget r).`3.`1 \/
     (oget r).`1 = Adv /\ adv = (oget r).`3.`1 /\ 0 <= (oget r).`3.`2 /\
      ((oget r).`2 = ([], 0) <=> (oget r).`3.`2 = 0)))).

lemma mi_loop_invar_not_done_imp_dest
      (func adv : addr, in_guard : int fset,
       m : msg, r : msg option) :
  mi_loop_invar func adv in_guard r m true =>
  func <= m.`2.`1 \/ m.`2.`1 = adv.
proof.
rewrite /mi_loop_invar; smt(le_refl).
qed.

(* guard for invoke procedure of interface *)

op main_guard (func adv : addr, in_guard : int fset, m : msg) : bool =
  m.`1 = Dir /\ func = m.`2.`1 /\ envport func adv m.`3 \/
  m.`1 = Adv /\ m.`2.`1 = adv /\
  (m.`2.`2 = 0 /\ m.`3 = ([], 0) \/
   0 < m.`2.`2 /\ m.`2.`2 \in in_guard /\ envport func adv m.`3).

module MI (Func : FUNC, Adv : FUNC) : INTER = {
  var func, adv : addr
  var in_guard : int fset

  proc init(func_ adv_ : addr, in_guard_ : int fset) : unit = {
    func <- func_; adv <- adv_; in_guard <- in_guard_;
    Func.init(func, adv);
    Adv.init(adv, []);
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
        if (adv <= m.`2.`1 \/ m.`2 = ([], 0) \/ func <> m.`3.`1) {
          r <- None;
        }
        (* else: envport func adv m.`2 *)
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
      else {  (* envport0 func adv m.`2 *)
        not_done <- false;
        if (! (m.`3.`2 = 0 <=> m.`2 = ([], 0))) {
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
    if (main_guard func adv in_guard m) {
      r <@ loop(m);
    }
    else {
      r <- None;
    }
    return r;
  }
}.

(* check that invariant is actually preserved: *)

lemma MI_after_func_hoare (Func <: FUNC{-MI}) (Adv <: FUNC{-Func, -MI}) :
  hoare
  [MI(Func, Adv).after_func :
   inter_init_pre MI.func MI.adv ==>
   mi_loop_invar MI.func MI.adv MI.in_guard res.`1 res.`2 res.`3].
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

lemma MI_after_adv_hoare (Func <: FUNC{-MI}) (Adv <: FUNC{-Func, -MI}) :
  hoare
  [MI(Func, Adv).after_adv :
   inter_init_pre MI.func MI.adv ==>
   mi_loop_invar MI.func MI.adv MI.in_guard res.`1 res.`2 res.`3].
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

lemma MI_invoke_hoare (Func <: FUNC{-MI}) (Adv <: FUNC{-Func, -MI}) :
  hoare
  [MI(Func, Adv).invoke :
   inter_init_pre MI.func MI.adv ==>
   res = None \/
   (envport0 MI.func MI.adv (oget res).`2 /\
    ((oget res).`1 = Dir /\ (oget res).`2 <> ([], 0) /\
      MI.func = (oget res).`3.`1 \/
     (oget res).`1 = Adv /\ MI.adv = (oget res).`3.`1 /\ 0 <= (oget res).`3.`2 /\
      ((oget res).`2 = ([], 0) <=> (oget res).`3.`2 = 0)))].
proof.
proc.
if.
inline MI(Func, Adv).loop.
wp; sp.
while (mi_loop_invar MI.func MI.adv MI.in_guard r0 m0 not_done).
if.
seq 1 : (inter_init_pre MI.func MI.adv /\ not_done).
call (_ : true); first auto => />.
call (MI_after_func_hoare Func Adv).
auto.
seq 1 : (inter_init_pre MI.func MI.adv /\ not_done).
call (_ : true); first auto => />.
call (MI_after_adv_hoare Func Adv).
auto.
auto => |> /#.
auto.
qed.

(* phoare lemmas for after_func and after_adv: *)

op after_func_to_env (func adv : addr, r : msg option) : bool =
  r <> None /\
  (oget r).`1 = Dir /\ envport func adv (oget r).`2 /\
  func = (oget r).`3.`1.

op after_func_to_adv (func adv : addr, r : msg option) : bool =
  r <> None /\
  (oget r).`1 = Adv /\ (oget r).`2.`1 = adv /\ 0 < (oget r).`2.`2 /\
  func <= (oget r).`3.`1.

op after_func_error (func adv : addr, r : msg option) : bool =
  r = None \/
  func <= (oget r).`2.`1 \/
  (oget r).`1 = Dir /\
  (adv <= (oget r).`2.`1 \/ (oget r).`2 = ([], 0) \/
   (oget r).`3.`1 <> func) \/
  (oget r).`1 = Adv /\
  ((oget r).`2.`1 <> adv \/ (oget r).`2.`2 <= 0 \/
   ! (func <= (oget r).`3.`1)).

lemma after_func_disj (func adv : addr, r : msg option) :
  after_func_to_env func adv r \/
  after_func_to_adv func adv r \/
  after_func_error func adv r.
proof.
rewrite /after_func_to_env /after_func_to_adv /after_func_error
        /envport /envport0.
case (r = None) => // _ /=.
case ((oget r).`1) => //=; smt().
qed.

lemma MI_after_func_to_env (Func <: FUNC{-MI}) (Adv <: FUNC{-Func, -MI})
      (r' : msg option) :
  phoare
  [MI(Func, Adv).after_func :
   inter_init_pre MI.func MI.adv /\ r = r' /\
   after_func_to_env MI.func MI.adv r ==>
   res.`1 = r' /\ res.`1 = Some res.`2 /\ !res.`3] = 1%r.
proof.
proc; auto; smt(some_oget le_refl).
qed.

lemma MI_after_func_to_adv (Func <: FUNC{-MI}) (Adv <: FUNC{-Func, -MI})
      (r' : msg option) :
  phoare
  [MI(Func, Adv).after_func :
   inter_init_pre MI.func MI.adv /\ r = r' /\
   after_func_to_adv MI.func MI.adv r ==>
   res.`1 = r' /\ res.`1 = Some res.`2 /\ res.`3] = 1%r.
proof.
proc; auto; smt(inc_nle_l some_oget).
qed.

lemma MI_after_func_error (Func <: FUNC{-MI}) (Adv <: FUNC{-Func, -MI}) :
  phoare
  [MI(Func, Adv).after_func :
   inter_init_pre MI.func MI.adv /\ after_func_error MI.func MI.adv r ==>
   res.`1 = None /\ !res.`3] = 1%r.
proof.
proc; auto; smt().
qed.

pred after_adv_to_env (func adv : addr, r : msg option) =
   r <> None /\
   (oget r).`1 = Adv /\ envport0 func adv (oget r).`2 /\
   adv = (oget r).`3.`1 /\ 0 <= (oget r).`3.`2 /\
   ((oget r).`2 = ([], 0) <=> (oget r).`3.`2 = 0).

pred after_adv_to_func (func adv : addr, r : msg option) =
  r <> None /\
  (oget r).`1 = Adv /\ func <= (oget r).`2.`1 /\
  (oget r).`3.`1 = adv /\ 0 < (oget r).`3.`2.

pred after_adv_error (func adv : addr, r : msg option) =
   (r = None \/
    (oget r).`1 = Dir \/
    adv <= (oget r).`2.`1 \/
    adv <> (oget r).`3.`1 \/ (oget r).`3.`2 < 0 \/
    (func <= (oget r).`2.`1 /\ (oget r).`3.`2 = 0) \/
    (! func <= (oget r).`2.`1 /\
     ! ((oget r).`3.`2 = 0 <=> (oget r).`2 = ([], 0)))).

lemma after_adv_disj (func adv : addr, r : msg option) :
  after_adv_to_env func adv r  \/
  after_adv_to_func func adv r \/
  after_adv_error func adv r.
proof.
rewrite /after_adv_to_env /after_adv_to_func /after_adv_error
        /envport /envport0.
case (r = None) => // _ /=.
case ((oget r).`1) => // /=.
smt().
qed.

lemma MI_after_adv_to_env (Func <: FUNC{-MI}) (Adv <: FUNC{-Func, -MI})
      (r' : msg option) :
  phoare
  [MI(Func, Adv).after_adv :
   inter_init_pre MI.func MI.adv /\ r = r' /\
   after_adv_to_env MI.func MI.adv r ==>
   res.`1 = r' /\ res.`1 = Some res.`2 /\ !res.`3] = 1%r.
proof.
proc; auto; smt(some_oget).
qed.

lemma MI_after_adv_to_func (Func <: FUNC{-MI}) (Adv <: FUNC{-Func, -MI})
      (r' : msg option) :
  phoare
  [MI(Func, Adv).after_adv :
   inter_init_pre MI.func MI.adv /\ r = r' /\
   after_adv_to_func MI.func MI.adv r ==>
   res.`1 = r' /\ res.`1 = Some res.`2 /\ res.`3] = 1%r.
proof.
proc; auto; smt(oget_some some_oget inc_le1_not_rl IntOrder.lerNgt).
qed.

lemma MI_after_adv_error (Func <: FUNC{-MI}) (Adv <: FUNC{-Func, -MI}) :
  phoare
  [MI(Func, Adv).after_adv :
   inter_init_pre MI.func MI.adv /\ after_adv_error MI.func MI.adv r ==>
   res.`1 = None /\ !res.`3] = 1%r.
proof.
proc; auto; smt().
qed.

end MakeInterface.

abstract theory DummyAdversary.

(* dummy adversary (DA) - completely controlled by environment *)

(* message from port ([], 0) of environment to port (dfe_da, 0) of
   dummy adversary, instructing dummy adversary to send message (Adv,
   dfe_pt, (dfe_da, dfe_n), dfe_tag, dfe_u); this instruction will
   only be obeyed if 0 < dfe_n and dfe_pt <> ([], 0), dfe_pt.`1 is
   not >= dfe_da, and dfe_tag is not TagNoInter *)

type da_from_env =
  {dfe_da  : addr;   (* address of dummy adversary *)
   (* data: *)
   dfe_pt  : port;   (* destination port of message to be sent by DA *)
   dfe_n   : int;    (* source port index of message to be sent by DA *)
   dfe_tag : tag;    (* tag of message to be sent by DA *)
   dfe_u   : univ}.  (* value of message to be sent by DA *)

op enc_da_from_env (x : da_from_env) : msg =  (* let SMT provers inspect *)
  (Adv, (x.`dfe_da, 0), ([], 0),
   TagNoInter,
   (epdp_tuple4_univ epdp_port_univ epdp_int_univ
    epdp_tag_univ epdp_id).`enc
    (x.`dfe_pt, x.`dfe_n, x.`dfe_tag, x.`dfe_u)).

op nosmt [opaque] dec_da_from_env (m : msg) : da_from_env option =
  let (mod, pt1, pt2, tag, v) = m
  in (mod = Dir \/ pt1.`2 <> 0 \/ pt2 <> ([], 0) \/ tag <> TagNoInter) ?
     None :
     match (epdp_tuple4_univ
            epdp_port_univ epdp_int_univ epdp_tag_univ epdp_id).`dec v with
     | None   => None
     | Some x =>
         let (pt, n, tag, u) = x
         in Some
            {|dfe_da = pt1.`1; dfe_pt = pt; dfe_n = n; dfe_tag = tag;
              dfe_u = u|}
     end.

op epdp_da_from_env_msg =
  {|enc = enc_da_from_env; dec = dec_da_from_env|}.

lemma valid_epdp_da_from_env_msg : valid_epdp epdp_da_from_env_msg.
proof.
apply epdp_intro.
move => x.
rewrite /epdp_da_from_env_msg /= /dec_da_from_env /enc_da_from_env /=.
rewrite !epdp.
by case x.
move => [mod pt1 pt2 tag u] v.
rewrite /epdp_da_from_env_msg /dec_da_from_env /enc_da_from_env /=.
case (mod = Dir \/ pt1.`2 <> 0 \/ pt2 <> ([], 0) \/ tag <> TagNoInter) => //.
rewrite !negb_or /= not_dir => [#] -> pt1_2 -> -> match_eq_some /=.
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
split; first move : pt1_2; by case pt1.
rewrite (epdp_dec_enc _ _ u) // !epdp.
qed.

hint simplify [eqtrue] valid_epdp_da_from_env_msg.
hint rewrite epdp : valid_epdp_da_from_env_msg.

lemma eq_of_valid_da_from_env (m : msg) :
  is_valid epdp_da_from_env_msg m =>
  m =
  let x = oget (epdp_da_from_env_msg.`dec m) in
  (Adv,
   (x.`dfe_da, 0),
   ([], 0),
   TagNoInter,
   (epdp_tuple4_univ epdp_port_univ epdp_int_univ epdp_tag_univ epdp_id).`enc
    (x.`dfe_pt, x.`dfe_n, x.`dfe_tag, x.`dfe_u)).
proof.
rewrite /is_valid.
move => val_m.
have [] x : exists (x : da_from_env), epdp_da_from_env_msg.`dec m = Some x.
  exists (oget (dec_da_from_env m)); by rewrite -some_oget.
case x => x1 x2 x3 x4 x5.
move => /(epdp_dec_enc _ _ _ valid_epdp_da_from_env_msg) <-.
by rewrite !epdp.
qed.

(*
(* message from port (dte_da, 0) of dummy adversary to port ([], 0) of
   environment, telling environment that dummy adversary received
   message (Adv, (dte_da, dte_n), dte_pt, dte_tag, dte_u), where
   0 < dtn_n and dte_pt <> ([], 0) *)

type da_to_env =
  {dte_da  : addr;   (* address of dummy adversary *)
   (* data: *)
   dte_n   : int;    (* destination port index of message sent to DA;
                        the port's address will be dte_da
                        (enforced by interface/simulator) *)
   dte_pt  : port;   (* source port of message sent to DA *)
   dte_tag : tag;    (* tag of message sent to DA *)
   dte_u   : univ}.  (* value of message sent to DA *)

op enc_da_to_env (x : da_to_env) : msg =  (* let SMT provers inspect *)
  (Adv, ([], 0), (x.`dte_da, 0), 
   TagNoInter,
   (epdp_tuple4_univ epdp_int_univ epdp_port_univ
    epdp_tag_univ epdp_id).`enc
    (x.`dte_n, x.`dte_pt, x.`dte_tag, x.`dte_u)).

op nosmt dec_da_to_env (m : msg) : da_to_env option =
  let (mod, pt1, pt2, tag, v) = m
  in (mod = Dir \/ pt1 <> ([], 0) \/ pt2.`2 <> 0 \/ tag <> 0) ?
     None :
     match (epdp_tuple4_univ
            epdp_int_univ epdp_port_univ epdp_int_univ
            epdp_id).`dec v with
     | None   => None
     | Some x =>
         let (n, pt, tag, u) = x
        in Some
           {|dte_da = pt2.`1; dte_n = n; dte_pt = pt; dte_tag = tag;
             dte_u = u|}
     end.

op epdp_da_to_env_msg =  (* let SMT provers inspect *)
  {|enc = enc_da_to_env; dec = dec_da_to_env|}.

lemma valid_epdp_da_to_env_msg : valid_epdp epdp_da_to_env_msg.
proof.
apply epdp_intro.
move => x.
rewrite /epdp_da_to_env_msg /= /dec_da_to_env /enc_da_to_env /=
        !(epdp, epdp_sub) /=.
by case x.
move => [mod pt1 pt2 tag u] v.
rewrite /epdp_da_to_env_msg /dec_da_to_env /enc_da_to_env /=.
case (mod = Dir \/ pt1 <> ([], 0) \/ pt2.`2 <> 0 \/ tag <> 0) => //.
rewrite !negb_or /= not_dir => [#] -> -> pt2_2 -> match_eq_some /=.
have val_u :
  (epdp_tuple4_univ epdp_int_univ epdp_port_univ
   epdp_int_univ epdp_id).`dec u =
  Some (v.`dte_n, v.`dte_pt, v.`dte_tag, v.`dte_u).
  move : match_eq_some.
  case ((epdp_tuple4_univ epdp_int_univ epdp_port_univ
         epdp_int_univ epdp_id).`dec u) => //.
  by case.
move : match_eq_some.
rewrite val_u /= => <- /=.
split; first move : pt2_2; by case pt2.
by rewrite (epdp_dec_enc _ _ u) // epdp_sub.
qed.

hint simplify [eqtrue] valid_epdp_da_to_env_msg.
hint rewrite epdp : valid_epdp_da_to_env_msg.

lemma eq_of_valid_da_to_env (m : msg) :
  is_valid epdp_da_to_env_msg m =>
  m =
  let x = oget (epdp_da_to_env_msg.`dec m) in
  (Adv,
   ([], 0),
   (x.`dte_da, 0),
   0,
   (epdp_tuple4_univ epdp_int_univ epdp_port_univ
    epdp_int_univ epdp_id).`enc
    (x.`dte_n, x.`dte_pt, x.`dte_tag, x.`dte_u)).
proof.
rewrite /is_valid.
move => val_m.
have [] x : exists (x : da_to_env), epdp_da_to_env_msg.`dec m = Some x.
  exists (oget (dec_da_to_env m)); by rewrite -some_oget.
case x => x1 x2 x3 x4 x5.
move => /(epdp_dec_enc _ _ _ valid_epdp_da_to_env_msg) <-.
by rewrite !epdp.
qed.

module DummyAdv : FUNC = {
  var self, env : addr

  proc init(self_ env_ : addr) = {
    self <- self_; env <- env_;
  }

  proc invoke(m : msg) : msg option = {
    var r : msg option <- None;

    match (epdp_da_from_env_msg.`dec m) with
      Some x => {  (* from interface/simulator, we know x.`dfe_da = self *)
        if (0 < x.`dfe_n /\ x.`dfe_pt <> ([], 0) /\
            ! self <= x.`dfe_pt.`1 ) {
          r <-
            Some
            (Adv, x.`dfe_pt, (self, x.`dfe_n), x.`dfe_tag, x.`dfe_u);
        }
      }
    | None   => {
        (* message from functionality or environment;
           interface/simulator will enforce that m.`1 = Adv /\ m.`2.`1
           = self /\ 0 <= m.`2.`2 /\ ! self <= m.`3.`1 /\
           (m.`3 = ([], 0) <=> m.`2.`2 = 0) *)
        if (0 < m.`2.`2) {
          r <-
            Some
            (enc_da_to_env
             {|dte_da = self; dte_n = m.`2.`2; dte_pt = m.`3;
               dte_tag = m.`4; dte_u = m.`5|});
        }
      }
    end;
    return r;
  }
}.

end DummyAdversary.

abstract theory MakeSimulator.

(* begin theory parameters *)

op core_pi : int.

axiom core_pi_gt0 :
  0 < core_pi.

(* end theory parameters *)

(* loop invariant for simulator's while loop *)

op ms_loop_invar
     (self : addr, if_addr_opt : addr option,
      m : msg, r : msg option, not_done : bool) : bool =
  self <> [] /\ m.`1 = Adv /\
  (not_done =>
   (m.`2 = (self, 0) /\ m.`3 = ([], 0) \/

    m.`2.`1 = self /\ m.`2.`2 = core_pi /\ if_addr_opt <> None /\
    oget if_addr_opt = m.`3.`1 /\ m.`3.`2 = 0 \/

    m.`2.`1 = self /\ 0 < m.`2.`2 < core_pi /\ ! self <= m.`3.`1 \/

    if_addr_opt <> None /\ oget if_addr_opt <= m.`2.`1 /\
    m.`3.`1 = self /\ 0 < m.`3.`2 < core_pi)) /\
  (! not_done =>
   r = None \/
   ((oget r).`1 = Adv /\ (oget r).`3.`1 = self /\ 
    ((oget r).`2 = ([], 0) /\ (oget r).`3.`2 = 0 \/

     if_addr_opt <> None /\ (oget r).`2 = (oget if_addr_opt, 0) /\
     (oget r).`3.`2 = core_pi \/

     ! self <= (oget r).`2.`1 /\ (oget r).`2 <> ([], 0) /\
     (if_addr_opt <> None => ! oget if_addr_opt <= (oget r).`2.`1) /\
     0 < (oget r).`3.`2 < core_pi))).

module MS (Core : FUNC, Adv : FUNC) : FUNC = {
  var self : addr

  (* address of ideal functionality; only known after first message
     received with destination port index core_pi *)

  var if_addr_opt : addr option

  (* adv_ will be [] *)

  proc init(self_ adv_ : addr) : unit = {
    self <- self_; if_addr_opt <- None;
    Core.init(self, []);
    Adv.init(self, []);
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
      elif (m.`2.`1 = self) {
        if (0 < m.`2.`2 /\ m.`2.`2 < core_pi /\ if_addr <= m.`3.`1) {
          not_done <- true;
        }
        else {
          r <- None; not_done <- false;
        }
      }
      elif (m.`2.`1 = if_addr) {
        if (m.`2.`2 = 0 /\ m.`3 = (self, core_pi)) {
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
      if (m.`1 = Dir \/ m.`2.`1 = self \/ m.`3.`1 <> self \/
          m.`3.`2 < 0 \/ core_pi <= m.`3.`2) {
        r <- None; not_done <- false;
      }
      elif (if_addr_opt = None) {
        not_done <- false;
      }
      elif (oget if_addr_opt <= m.`2.`1) {
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
      if (m.`2.`2 = core_pi) {
        if (if_addr_opt = None) {
          if_addr_opt <- Some m.`3.`1;  (* m.`3.`2 should be 0 *)
        }
        r <@ Core.invoke(m);
        (r, m, not_done) <@ after_core(r);
      }
      elif (if_addr_opt <> None /\ oget if_addr_opt <= m.`2.`1) {
        r <@ Core.invoke(m);
        (r, m, not_done) <@ after_core(r);
      }
      else {
        r <@ Adv.invoke(m);
        (r, m, not_done) <@ after_adv(r);
      }
    }
    return r;
  }

  (* m.`1 = Adv /\ m.`2.`1 = self /\ 0 <= m.`2.`2 /\
     ! self <= m.`3.`1 *)

  proc invoke(m : msg) : msg option = {
    var r : msg option <- None;
    if (m.`2.`2 = core_pi) {
      if (if_addr_opt = None) {
        if (m.`3.`2 = 0) {  (* ideal functionality's internal port index *)
          if_addr_opt <- Some m.`3.`1;
          r <@ loop(m);
        }
      }
      elif (m.`3 = (oget if_addr_opt, 0)) {
        r <@ loop(m);
      }
    }
    elif (0 < m.`2.`2) {
      if (if_addr_opt = None \/ ! oget if_addr_opt <= m.`3.`1) {
        r <@ loop(m);
      }
    }
    else {
      r <@ loop(m);
    }
    return r;
  }
}.

end MakeSimulator.
*)
