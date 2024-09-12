(* UCCore.ec *)

(* Core UC Definitions and Lemmas *)

prover quorum=2 ["Z3" "Alt-Ergo"].

(* standard theories, encoding and partial decoding pairs (EPDPs), the
   type univ plus a number of EPDPs with target univ, addresses and
   ports *)

require export UCBasicTypes.
require import UCListAux.

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

pred env_init_pre (func : addr) = inter_init_pre func.

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

abstract theory MakeInterface.

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

lemma MI_after_func_hoare (Func <: FUNC{-MI}) (Adv <: ADV{-Func, -MI}) :
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

lemma MI_after_adv_hoare (Func <: FUNC{-MI}) (Adv <: ADV{-Func, -MI}) :
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

lemma MI_invoke_hoare (Func <: FUNC{-MI}) (Adv <: ADV{-Func, -MI}) :
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

lemma MI_after_func_to_env (Func <: FUNC{-MI}) (Adv <: ADV{-Func, -MI})
      (r' : msg option) :
  phoare
  [MI(Func, Adv).after_func :
   inter_init_pre MI.func /\ r = r' /\
   after_func_to_env MI.func r ==>
   res.`1 = r' /\ res.`1 = Some res.`2 /\ !res.`3] = 1%r.
proof.
proc; auto; smt(some_oget le_refl).
qed.

lemma MI_after_func_to_adv (Func <: FUNC{-MI}) (Adv <: ADV{-Func, -MI})
      (r' : msg option) :
  phoare
  [MI(Func, Adv).after_func :
   inter_init_pre MI.func /\ r = r' /\
   after_func_to_adv MI.func r ==>
   res.`1 = r' /\ res.`1 = Some res.`2 /\ res.`3] = 1%r.
proof.
proc; auto; smt(inc_nle_l some_oget).
qed.

lemma MI_after_func_error (Func <: FUNC{-MI}) (Adv <: ADV{-Func, -MI}) :
  phoare
  [MI(Func, Adv).after_func :
   inter_init_pre MI.func /\ after_func_error MI.func r ==>
   res.`1 = None /\ !res.`3] = 1%r.
proof.
proc; auto; smt().
qed.

pred after_adv_to_env (func : addr, r : msg option) =
   r <> None /\
   (oget r).`1 = Adv /\ envport0 func (oget r).`2 /\
   adv = (oget r).`3.`1 /\ 0 <= (oget r).`3.`2 /\
   ((oget r).`2 = env_root_port <=> (oget r).`3.`2 = 0).

pred after_adv_to_func (func : addr, r : msg option) =
  r <> None /\
  (oget r).`1 = Adv /\ func <= (oget r).`2.`1 /\
  (oget r).`3.`1 = adv /\ 0 < (oget r).`3.`2.

pred after_adv_error (func : addr, r : msg option) =
   (r = None \/
    (oget r).`1 = Dir \/
    adv <= (oget r).`2.`1 \/
    adv <> (oget r).`3.`1 \/ (oget r).`3.`2 < 0 \/
    (func <= (oget r).`2.`1 /\ (oget r).`3.`2 = 0) \/
    (! func <= (oget r).`2.`1 /\
     ! ((oget r).`3.`2 = 0 <=> (oget r).`2 = env_root_port))).

lemma after_adv_disj (func adv : addr, r : msg option) :
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

lemma MI_after_adv_to_env (Func <: FUNC{-MI}) (Adv <: ADV{-Func, -MI})
      (r' : msg option) :
  phoare
  [MI(Func, Adv).after_adv :
   inter_init_pre MI.func /\ r = r' /\
   after_adv_to_env MI.func r ==>
   res.`1 = r' /\ res.`1 = Some res.`2 /\ !res.`3] = 1%r.
proof.
proc; auto; smt(some_oget).
qed.

lemma MI_after_adv_to_func (Func <: FUNC{-MI}) (Adv <: ADV{-Func, -MI})
      (r' : msg option) :
  phoare
  [MI(Func, Adv).after_adv :
   inter_init_pre MI.func /\ r = r' /\
   after_adv_to_func MI.func r ==>
   res.`1 = r' /\ res.`1 = Some res.`2 /\ res.`3] = 1%r.
proof.
proc; auto; smt(oget_some some_oget inc_le1_not_rl IntOrder.lerNgt).
qed.

lemma MI_after_adv_error (Func <: FUNC{-MI}) (Adv <: ADV{-Func, -MI}) :
  phoare
  [MI(Func, Adv).after_adv :
   inter_init_pre MI.func /\ after_adv_error MI.func r ==>
   res.`1 = None /\ !res.`3] = 1%r.
proof.
proc; auto; smt().
qed.

end MakeInterface.

(* the top-level interface in theorems *)

clone MakeInterface as MakeInt
proof *.

module MI = MakeInt.MI.

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
   
(* index from 1: *)

op nth1_adv_pi_begin_params (rfi : rf_info, pari) : int =
  nth 0 rfi.`rfi_adv_pi_begin_params (pari - 1).

op nth1_adv_pi_end_params (rfi : rf_info, pari) : int =
  nth 0 rfi.`rfi_adv_pi_end_params (pari - 1).

op rf_info_valid (rfi : rf_info) : bool =
  1 <= rfi.`rfi_num_parties /\
  0 <= rfi.`rfi_num_subfuns /\
  0 <= rfi.`rfi_num_params /\
  1 <= rfi.`rfi_adv_pi_begin /\
  (* includes adv pi of ideal functionality of unit *)
  rfi.`rfi_adv_pi_begin < rfi.`rfi_adv_pi_main_end /\
  size rfi.`rfi_adv_pi_begin_params = rfi.`rfi_num_params /\
  size rfi.`rfi_adv_pi_end_params   = rfi.`rfi_num_params /\
  (1 <= rfi.`rfi_num_params =>
   nth1_adv_pi_begin_params rfi 1 = rfi.`rfi_adv_pi_main_end + 1 /\
   (forall (pari : int),
    1 <= pari <= rfi.`rfi_num_params =>
    nth1_adv_pi_begin_params rfi pari < nth1_adv_pi_end_params rfi pari) /\
   (forall (pari : int),
    1 <= pari <= rfi.`rfi_num_params - 1 =>
    nth1_adv_pi_begin_params rfi (pari + 1) =
    nth1_adv_pi_end_params rfi pari + 1)).

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
    var m : msg <- witness; var pari : int;
    var not_done <- true;
    if (r = None) {
      not_done <- false;
    }
    else {
      m <- oget r;  (* next iteration, if any, will use m *)
      if (m.`3.`1 <> orig_dest_addr) {
        not_done <- false; r <- None;
      }
      elif (m.`1 = Dir) {
        if (m.`3.`1 = self) {
          if (envport self m.`2) {
            not_done <- false;
          }
          elif (! (addr_eq_param rf_info self m.`2.`1 \/
                   addr_eq_subfun rf_info self m.`2.`1)) {
            not_done <- false; r <- None;
          }
        }
        elif (addr_eq_param  rf_info self m.`3.`1 \/
              addr_eq_subfun rf_info self m.`3.`1) {
          if (m.`2.`1 <> self) {
            not_done <- false; r <- None;
          }
        }
        else {  (* should not happen *)
          not_done <- false; r <- None;
        }
      }
      else {  (* m.`1 = Adv *)
        not_done <- false;
        if (m.`2.`1 <> adv) {
          r <- None;
        }
        elif (m.`3.`1 = self \/
              addr_eq_subfun rf_info self m.`3.`1) {
          if (! rf_info.`rfi_adv_pi_begin < m.`2.`2 <=
                rf_info.`rfi_adv_pi_main_end) {
            r <- None;
          }
        }
        elif (addr_ge_param rf_info self m.`3.`1) {
          pari <- head_of_drop_size_first 0 self m.`3.`1;
          if (! (nth1_adv_pi_begin_params rf_info pari <= m.`2.`2 <=
                 nth1_adv_pi_end_params rf_info pari)) {
            r <- None;
          }
        }
        else {  (* should not happen *)
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

lemma MakeRF_init_invar (Core <: FUNC{-MakeRF})
      (core_invar : glob Core -> bool) :
  equiv
  [Core.init ~ Core.init :
   ={self} ==> ={glob Core} /\ core_invar (glob Core){1}] =>
  equiv
  [MakeRF(Core).init ~ MakeRF(Core).init :
   ={_self} ==>
   ={glob MakeRF, glob Core} /\ core_invar (glob Core){1}].
proof.
move => Core_init.
proc; sp.
call Core_init.
auto.
qed.

lemma MakeRF_invoke_term_metric (Core <: FUNC{-MakeRF})
      (invar_Core : glob Core -> bool, tm_Core : glob Core -> int,
       n : int) :
  (forall (n : int),
   equiv
   [Core.invoke ~ Core.invoke :
    ={glob Core, m} /\ invar_Core (glob Core){1} /\
    tm_Core (glob Core){1} = n ==>
    ={glob Core, res} /\ invar_Core (glob Core){1} /\
    (res{1} <> None => tm_Core (glob Core){1} < n)]) =>
  equiv
  [MakeRF(Core).invoke ~ MakeRF(Core).invoke :
   ={glob MakeRF, glob Core, m} /\ invar_Core (glob Core){1} /\
   tm_Core (glob Core){1} = n ==>
   ={glob MakeRF, glob Core, res} /\ invar_Core (glob Core){1} /\
   (res{1} <> None => tm_Core (glob Core){1} < n)].
proof.
move => Core_invoke_invar_tm.
proc; sp 1 1; if => //.
inline MakeRF(Core).loop; wp; sp.
conseq
  (_ :
   ={MakeRF.self, glob Core, m0, not_done} /\ not_done{1} /\
   invar_Core (glob Core){1} /\ tm_Core (glob Core){1} = n ==>
   _) => //.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
seq 1 1 :
  (={MakeRF.self, glob Core, m0, r0} /\ invar_Core (glob Core){1} /\
   (r0{1} <> None => tm_Core (glob Core){1} < n)).
call (Core_invoke_invar_tm n); first auto; smt().
seq 1 1 : 
  (={MakeRF.self, glob Core, m0, r0, not_done} /\ invar_Core (glob Core){1} /\
   (r0{1} = None  => ! not_done{1}) /\
   (r0{1} <> None => tm_Core (glob Core){1} < n)).
inline*; auto; progress; smt().
while
  (={MakeRF.self, glob Core, m0, r0, not_done} /\ invar_Core (glob Core){1} /\
   (r0{1} = None  => ! not_done{1}) /\
   (r0{1} <> None => tm_Core (glob Core){1} < n)).
conseq
  (_ :
   (={MakeRF.self, glob Core, m0, r0, not_done} /\ invar_Core (glob Core){1} /\
    tm_Core (glob Core){1} < n) ==>
   _); first smt().
exlim (tm_Core (glob Core){1}) => n'.
seq 1 1 :
  (={MakeRF.self, glob Core, m0, r0} /\ invar_Core (glob Core){1} /\
   (r0{1} <> None => tm_Core (glob Core){1} < n)).
call (Core_invoke_invar_tm n'); first auto; smt().
inline*; auto; progress; smt().
auto.
qed.

end RealFunctionality.

abstract theory DummyAdversary.

(* dummy adversary (DA) - completely controlled by environment *)

(* message from port env_root_port of environment to port (dfe_da, 0) of
   dummy adversary, instructing dummy adversary to send message (Adv,
   dfe_pt, (dfe_da, dfe_n), dfe_tag, dfe_u); this instruction will
   only be obeyed if 0 < dfe_n and dfe_pt <> env_root_port, dfe_pt.`1 is
   not >= dfe_da, and dfe_tag is not TagNoInter *)

type da_from_env =
  {dfe_da  : addr;   (* address of dummy adversary *)
   (* data: *)
   dfe_pt  : port;   (* destination port of message to be sent by DA *)
   dfe_n   : int;    (* source port index of message to be sent by DA *)
   dfe_tag : tag;    (* tag of message to be sent by DA *)
   dfe_u   : univ}.  (* value of message to be sent by DA *)

op enc_da_from_env (x : da_from_env) : msg =  (* let SMT provers inspect *)
  (Adv, (x.`dfe_da, 0), env_root_port,
   TagNoInter,
   (epdp_tuple4_univ epdp_port_univ epdp_int_univ
    epdp_tag_univ epdp_id).`enc
    (x.`dfe_pt, x.`dfe_n, x.`dfe_tag, x.`dfe_u)).

op [opaque smt_opaque] dec_da_from_env (m : msg) : da_from_env option =
  let (mod, pt1, pt2, tag, v) = m
  in (mod = Dir \/ pt1.`2 <> 0 \/ pt2 <> env_root_port \/ tag <> TagNoInter) ?
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
case
  (mod = Dir \/ pt1.`2 <> 0 \/ pt2 <> env_root_port \/ tag <> TagNoInter) => //.
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
   env_root_port,
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

(* message from port (dte_da, 0) of dummy adversary to port env_root_port of
   environment, telling environment that dummy adversary received
   message (Adv, (dte_da, dte_n), dte_pt, dte_tag, dte_u), where
   0 < dtn_n and dte_pt <> env_root_port *)

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
  (Adv, env_root_port, (x.`dte_da, 0), 
   TagNoInter,
   (epdp_tuple4_univ epdp_int_univ epdp_port_univ
    epdp_tag_univ epdp_id).`enc
    (x.`dte_n, x.`dte_pt, x.`dte_tag, x.`dte_u)).

op [opaque smt_opaque] dec_da_to_env (m : msg) : da_to_env option =
  let (mod, pt1, pt2, tag, v) = m
  in (mod = Dir \/ pt1 <> env_root_port \/ pt2.`2 <> 0 \/ tag <> TagNoInter) ?
     None :
     match (epdp_tuple4_univ
            epdp_int_univ epdp_port_univ epdp_tag_univ
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
rewrite /epdp_da_to_env_msg /= /dec_da_to_env /enc_da_to_env /= !epdp.
by case x.
move => [mod pt1 pt2 tag u] v.
rewrite /epdp_da_to_env_msg /dec_da_to_env /enc_da_to_env /=.
case (mod = Dir \/ pt1 <> env_root_port \/ pt2.`2 <> 0 \/ tag <> TagNoInter) => //.
rewrite !negb_or /= not_dir => [#] -> -> pt2_2 -> match_eq_some /=.
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
split; first move : pt2_2; by case pt2.
rewrite (epdp_dec_enc _ _ u) // !epdp.
qed.

hint simplify [eqtrue] valid_epdp_da_to_env_msg.
hint rewrite epdp : valid_epdp_da_to_env_msg.

lemma eq_of_valid_da_to_env (m : msg) :
  is_valid epdp_da_to_env_msg m =>
  m =
  let x = oget (epdp_da_to_env_msg.`dec m) in
  (Adv,
   env_root_port,
   (x.`dte_da, 0),
   TagNoInter,
   (epdp_tuple4_univ epdp_int_univ epdp_port_univ
    epdp_tag_univ epdp_id).`enc
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

module DummyAdv : ADV = {
  proc init() : unit = {
  }

  proc invoke(m : msg) : msg option = {
    var r : msg option <- None;

    match (epdp_da_from_env_msg.`dec m) with
      Some x => {  (* from interface/simulator, we know x.`dfe_da = self *)
        if (0 < x.`dfe_n /\ x.`dfe_pt <> env_root_port /\
            ! adv <= x.`dfe_pt.`1 /\ x.`dfe_tag <> TagNoInter) {
          r <- Some (Adv, x.`dfe_pt, (adv, x.`dfe_n), x.`dfe_tag, x.`dfe_u);
        }
      }
    | None   => {
        (* message from functionality or environment;
           interface/simulator will enforce that m.`1 = Adv /\ m.`2.`1
           = self /\ 0 <= m.`2.`2 /\ ! self <= m.`3.`1 /\
           (m.`3 = env_root_port <=> m.`2.`2 = 0) *)
        if (0 < m.`2.`2) {
          r <-
            Some
            (enc_da_to_env
             {|dte_da = adv; dte_n = m.`2.`2; dte_pt = m.`3;
               dte_tag = m.`4; dte_u = m.`5|});
        }
      }
    end;
    return r;
  }
}.

end DummyAdversary.

abstract theory MakeSimulator.

(* construct a simulator from a core *)

(* begin theory parameters *)

op core_pi : int.

axiom core_pi_gt0 :
  0 < core_pi.

(* end theory parameters *)

(* loop invariant for simulator's while loop *)

(* TODO - this is out of date: *)

op ms_loop_invar
     (if_addr_opt : addr option,
      m : msg, r : msg option, not_done : bool) : bool =
  m.`1 = Adv /\
  (not_done =>
   (m.`2 = (adv, 0) /\ m.`3 = env_root_port \/

    m.`2.`1 = adv /\ m.`2.`2 = core_pi /\ if_addr_opt <> None /\
    oget if_addr_opt = m.`3.`1 /\ m.`3.`2 = 1 \/

    m.`2.`1 = adv /\ 0 < m.`2.`2 /\ m.`2.`2 <> core_pi /\ ! adv <= m.`3.`1 \/

    if_addr_opt <> None /\ oget if_addr_opt <= m.`2.`1 /\
    m.`3.`1 = adv /\ 0 < m.`3.`2 < core_pi)) /\
  (! not_done =>
   r = None \/
   ((oget r).`1 = Adv /\ (oget r).`3.`1 = adv /\ 
    ((oget r).`2 = env_root_port /\ (oget r).`3.`2 = 0 \/

     if_addr_opt <> None /\ (oget r).`2 = (oget if_addr_opt, 0) /\
     (oget r).`3.`2 = core_pi \/

     ! adv <= (oget r).`2.`1 /\ (oget r).`2 <> env_root_port /\
     (if_addr_opt <> None => ! oget if_addr_opt <= (oget r).`2.`1) /\
     0 < (oget r).`3.`2 < core_pi))).

module MS (Core : ADV) (Adv : ADV) : ADV = {
  (* address of ideal functionality; only known after first message
     received with destination port index core_pi *)

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
        if (0 < m.`2.`2 /\ if_addr <= m.`3.`1) {
          not_done <- true;
        }
        else {
          r <- None; not_done <- false;
        }
      }
      elif (m.`2.`1 = if_addr) {
        if (m.`2.`2 = 1 /\ m.`3 = (adv, core_pi)) {
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
      if (m.`1 = Dir \/ m.`2.`1 = adv \/ m.`3.`1 <> adv \/
          m.`3.`2 < 0) {
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

  (* m.`1 = Adv /\ m.`2.`1 = self /\
     (m.`2.`2 = 0 /\ m.`3 = env_root_port \/
      0 < m.`2.`2 /\ m.`3 <> env_root_port) *)

  proc invoke(m : msg) : msg option = {
    var r : msg option <- None;
    if (m.`2.`2 = core_pi) {  (* so m.`3 <> env_root_port *)
      if (if_addr_opt = None) {
        if (m.`3.`2 = 1) {  (* ideal functionality's port index *)
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

end MakeSimulator.
