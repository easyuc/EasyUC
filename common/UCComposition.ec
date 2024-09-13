(* Composition Theorem Definitions and Proofs *)

require import UCCore UCListAux.

abstract theory CompBridge.

(* begin theory parameters *)

op rf_info : rf_info.

axiom rf_info_valid : rf_info_valid rf_info.

op change_pari : int.  (* parameter being changed from real to ideal *)

axiom change_pari_valid : 1 <= change_pari <= rf_info.`rfi_num_params.

(* end theory parameters *)

module MakeRFComp (Rest : FUNC, Par : FUNC) : FUNC = {
  var self : addr

  proc init(_self : addr) : unit = {
    self <- _self;
    Rest.init(_self);
    Par.init(_self ++ [change_pari]);
  }

  (* the same as after_core from MakeRF: *)

  proc after_par_or_rest(r : msg option, orig_dest_addr)
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
        elif (addr_eq_param rf_info self m.`3.`1 \/
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
      if (self ++ [change_pari] <= m.`2.`1) {
        r <@ Par.invoke(m);
      }
      else {
        r <@ Rest.invoke(m);
      }
      (r, m, not_done) <@ after_par_or_rest(r, m.`2.`1);
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

op after_par_or_rest_return
   (func : addr, r : msg option, orig_dest_addr : addr) : bool =
  r <> None /\ (oget r).`3.`1 = orig_dest_addr /\
  (((oget r).`1 = Dir /\ (oget r).`3.`1 = func /\
    envport func (oget r).`2) \/
   ((oget r).`1 = Adv /\ (oget r).`2.`1 = adv /\
    ((((oget r).`3.`1 = func \/
       addr_eq_subfun rf_info func (oget r).`3.`1) /\
      rf_info.`rfi_adv_pi_begin < (oget r).`2.`2 <=
      rf_info.`rfi_adv_pi_main_end) \/
     (addr_ge_param rf_info func (oget r).`3.`1 /\
      let pari = head_of_drop_size_first 0 func (oget r).`3.`1 in
      nth1_adv_pi_begin_params rf_info pari <= (oget r).`2.`2 <=
      nth1_adv_pi_end_params rf_info pari)))).

op after_par_or_rest_continue
   (func : addr, r : msg option, orig_dest_addr : addr) : bool =
  r <> None /\ (oget r).`3.`1 = orig_dest_addr /\ (oget r).`1 = Dir /\
  (((oget r).`3.`1 = func /\ 
    (addr_eq_param rf_info func (oget r).`2.`1 \/
     addr_eq_subfun rf_info func (oget r).`2.`1)) \/
   ((addr_eq_param rf_info func (oget r).`3.`1 \/
     addr_eq_subfun rf_info func (oget r).`3.`1) /\
    (oget r).`2.`1 = func)).

op after_par_or_rest_error
   (func : addr, r : msg option, orig_dest_addr : addr) : bool =
  r = None \/
  (oget r).`3.`1 <> orig_dest_addr \/
  ((oget r).`1 = Dir /\ (oget r).`3.`1 = func /\
   ! envport func (oget r).`2 /\
   ! addr_eq_param rf_info func (oget r).`2.`1 /\
   ! addr_eq_subfun rf_info func (oget r).`2.`1) \/
  ((oget r).`1 = Dir /\
   (addr_eq_param rf_info func (oget r).`3.`1 \/
    addr_eq_subfun rf_info func (oget r).`3.`1) /\
   (oget r).`2.`1 <> func) \/
  ((oget r).`1 = Dir /\
   (oget r).`3.`1 <> func /\
   ! addr_eq_param rf_info func (oget r).`3.`1 /\
   ! addr_eq_subfun rf_info func (oget r).`3.`1) \/
  ((oget r).`1 = Adv /\ (oget r).`2.`1 <> adv) \/
  ((oget r).`1 = Adv /\
   ((oget r).`3.`1 = func \/
    addr_eq_subfun rf_info func (oget r).`3.`1) /\
   ! rf_info.`rfi_adv_pi_begin < (oget r).`2.`2 <=
     rf_info.`rfi_adv_pi_main_end) \/
  ((oget r).`1 = Adv /\
   addr_ge_param rf_info func (oget r).`3.`1 /\
   let pari = head_of_drop_size_first 0 func (oget r).`3.`1 in
   ! (nth1_adv_pi_begin_params rf_info pari <= (oget r).`2.`2 <=
      nth1_adv_pi_end_params rf_info pari)) \/
  ((oget r).`1 = Adv /\
   (oget r).`3.`1 <> func /\
   ! addr_eq_subfun rf_info func (oget r).`3.`1 /\
   ! addr_ge_param rf_info func (oget r).`3.`1).

lemma after_par_or_rest_disj (func adv : addr, r : msg option,
      orig_dest_addr : addr) :
  after_par_or_rest_return func r orig_dest_addr \/
  after_par_or_rest_continue func r orig_dest_addr \/
  after_par_or_rest_error func r orig_dest_addr.
proof.
rewrite /after_par_or_rest_return /after_par_or_rest_continue
        /after_par_or_rest_error.
case (r = None) => // _ /=.
case ((oget r).`2.`1 = UCBasicTypes.adv) => // _ /= /#.
qed.

lemma MakeRFComp_after_par_or_rest_return
      (Rest <: FUNC{-MI}) (Par <: FUNC{-Rest, -MakeRFComp})
      (r' : msg option) :
  phoare
  [MakeRFComp(Rest, Par).after_par_or_rest :
   r = r' /\
   after_par_or_rest_return MakeRFComp.self r orig_dest_addr ==>
   res.`1 = r' /\ res.`1 = Some res.`2 /\ !res.`3] = 1%r.
proof.
proc => /=.
sp 2.
rcondf 1; first auto; smt().
sp 1; elim* => m0.
rcondf 1; first auto; smt().
if.
auto; smt().
sp 1; elim* => not_done0.
rcondf 1; first auto; smt().
auto;
  smt(not_addr_ge_param_self disjoint_addr_ge_param_eq_subfun).
qed.

lemma MakeRFComp_after_par_or_rest_continue
      (Rest <: FUNC{-MI}) (Par <: FUNC{-Rest, -MakeRFComp})
      (r' : msg option) :
  phoare
  [MakeRFComp(Rest, Par).after_par_or_rest :
   r = r' /\
   after_par_or_rest_continue MakeRFComp.self r orig_dest_addr ==>
   res.`1 = r' /\ res.`1 = Some res.`2 /\ res.`3] = 1%r.
proof.
proc => /=.
auto;
  smt(disjoint_addr_eq_param_envport disjoint_addr_eq_subfun_envport).
qed.

lemma MakeRFComp_after_par_or_rest_error
      (Rest <: FUNC{-MI}) (Par <: FUNC{-Rest, -MakeRFComp}) :
  phoare
  [MakeRFComp(Rest, Par).after_par_or_rest :
   after_par_or_rest_error MakeRFComp.self r orig_dest_addr ==>
   res.`1 = None /\ ! res.`3] = 1%r.
proof.
proc => /=.
sp 2.
if; first auto.
sp 1; elim* => m0.
if; first auto.
if.
auto; smt(not_addr_eq_param_self not_addr_eq_subfun_self).
sp 1; elim* => not_done0.
if; first auto.
if.
rcondt 1; first auto => &hr [#] _ H1 _ _ H2 H3 H4 H5 H6 H7.
smt(not_addr_ge_param_self disjoint_addr_ge_param_eq_subfun).
auto.
if.
sp 1.
rcondt 1; first auto => &hr [#] H1 _ H2 _ _ H3 H4 H5 H6 H7.
smt(not_addr_ge_param_self disjoint_addr_ge_param_eq_subfun).
auto.
auto.
qed.

clone MakeInterface as MakeInt'
proof *.

module MI' = MakeInt'.MI.

module CompEnv (Rest : FUNC, Env : ENV, Inter : INTER) = {
  var stub_st : msg option
  var func : addr
  var in_guard_low : int fset

  module StubPar : FUNC = {
    proc init(func : addr) : unit = { }

    proc invoke(m : msg) : msg option = {
      var r : msg option;
      if (stub_st <> None) {
        r <- stub_st; stub_st <- None;
      }
      else {
        r <@ Inter.invoke(m);
        if (r <> None) {
          m <- oget r;
          if (m.`1 = Adv) {
            stub_st <- Some m;
            (* only mode and destination port matter (destination port id
               must simply be > 0) *)
            r <-
              Some
              (Adv, (adv, 1), (func ++ [change_pari], 1), TagNoInter, []);
          }
        }
      }
      return r;
    }
  }

  module StubAdv : ADV = {
    proc init() : unit = { }

    proc invoke(m : msg) : msg option = {
      var r : msg option;
      if (stub_st <> None) {
        r <- stub_st; stub_st <- None;
      }
      else {
        r <@ Inter.invoke(m);
        if (r <> None) {
          m <- oget r;
          if (m.`1 = Dir) {
            stub_st <- Some m;
            (* only mode and destination address matter *)
            r <-
              Some
              (Adv, (func ++ [change_pari], 1), (adv, 1), TagNoInter, []);
          }
        }
      }
      return r;
    }
  }

  (* func_ will end with change_pari *)

  proc main(func_ : addr, in_guard : int fset) : bool = {
    var b : bool;
    stub_st <- None;
    func <- take (size func_ - 1) func_;
    b <@ Exper(MI'(MakeRFComp(Rest, StubPar), StubAdv), Env)
           .main(func, in_guard_low);
    return b;
  }
}.

op rest_adv_pi_ok (guard : int fset) : bool =
  (forall (advpi : int),
   rf_info.`rfi_adv_pi_begin < advpi <= rf_info.`rfi_adv_pi_main_end =>
   advpi \in guard) /\
  (forall (advpi pari : int),
   (1 <= pari < change_pari \/
    change_pari < pari <= rf_info.`rfi_num_params) =>
   (nth1_adv_pi_begin_params rf_info pari <= advpi <=
    nth1_adv_pi_end_params rf_info pari) =>
   advpi \in guard).

section.

declare module Env  <: ENV{-MI, -CompEnv}.
declare module Adv  <: ADV{-MI, -CompEnv, -Env}.
declare module Rest <: FUNC{-MI, -CompEnv, -Env, -Adv}.
declare module Par  <: FUNC{-MI, -CompEnv, -Env, -Adv, -Rest}.

declare op invar_rest : glob Rest -> bool.
declare op term_rest  : glob Rest -> int.

declare op invar_par  : glob Par  -> bool.
declare op term_par   : glob Par  -> int.

declare axiom ge0_term_rest (gl : glob Rest) :
  0 <= term_rest gl.

declare axiom Rest_init :
   equiv
   [Rest.init ~ Rest.init :
    ={self} ==>
    ={glob Rest} /\ invar_rest (glob Rest){1}].

declare axiom Rest_invoke (n : int) :
   equiv
   [Rest.invoke ~ Rest.invoke :
    ={m, glob Rest} /\ invar_rest (glob Rest){1} /\
    term_rest (glob Rest){1} = n ==>
    ={res, glob Rest} /\ invar_rest (glob Rest){1} /\
    (res{1} <> None => term_rest (glob Rest){1} < n)].

declare axiom ge0_term_par (gl : glob Par) :
  0 <= term_par gl.

declare axiom Par_init :
   equiv
   [Par.init ~ Par.init :
    ={self} ==>
    ={glob Par} /\ invar_par (glob Par){1}].

declare axiom Par_invoke (n : int) :
   equiv
   [Par.invoke ~ Par.invoke :
    ={m, glob Par} /\ invar_par (glob Par){1} /\
    term_par (glob Par){1} = n ==>
    ={res, glob Par} /\ invar_par (glob Par){1} /\
    (res{1} <> None => term_par (glob Par){1} < n)].

lemma comp_bridge
      (func' : addr, in_guard_low' in_guard_hi' : int fset) &m :
  exper_pre func' =>
  in_guard_low' \subset in_guard_hi' =>
  rest_adv_pi_ok in_guard_hi' =>
  CompEnv.in_guard_low{m} = in_guard_low' =>
  Pr[Exper(MI(MakeRFComp(Rest, Par), Adv), Env)
       .main(func', in_guard_low') @ &m : res] =
  Pr[Exper(MI(Par, Adv), CompEnv(Rest, Env))
       .main(func' ++ [change_pari], in_guard_hi') @ &m : res].
proof.
move =>
  ep_func' sub_in_guard_low'_in_guard_high' rest_adv_pi_ok_in_guard_hi'
  eq_in_guard_low_ce_in_guard_low'.
byequiv => //.
proc; inline *; wp.
swap{2} 6 14; swap{2} 5 14; swap{2} 17 1; sp.
seq 3 3 :
  (={glob Env, glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   _self{1} = func' /\ _self{1} = func{1} /\
   _self{1} = MI.func{1} /\ _self{1} = MakeRFComp.self{1} /\
   in_guard{1} = in_guard_low' /\ in_guard{1} = MI.in_guard{1} /\
   _self{2} = func' /\ _self{2} = func0{2} /\ _self{2} = MI'.func{2} /\
   _self{2} = MakeRFComp.self{2} /\ _self{2} = CompEnv.func{2} /\
   MI.func{2} = func' ++ [change_pari] /\
   in_guard1{2} = CompEnv.in_guard_low{2} /\
   in_guard1{2} = MI'.in_guard{2} /\
   in_guard1{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_hi' /\
   CompEnv.stub_st{2} = None).
call (_ : true).
call Par_init.
call Rest_init.
auto; progress;
  by rewrite size_cat /= take_size_cat.
call
  (_ :
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ MakeRFComp.self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   MI'.func{2} = func' /\ MakeRFComp.self{2} = func' /\
   CompEnv.func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnv.in_guard_low{2} = in_guard_low' /\
   MI'.in_guard{2} = in_guard_low' /\ MI.in_guard{2} = in_guard_hi' /\
   CompEnv.stub_st{2} = None).
proc.
if => //.
inline loop.
sp 3 3.
admit.
auto.
auto.
qed.

end section.

lemma compos_bridge
      (Env <: ENV{-MI, -CompEnv}) (Adv <: ADV{-MI, -CompEnv, -Env})
      (Rest <: FUNC{-MI, -CompEnv, -Env, -Adv})
      (Par <: FUNC{-MI, -CompEnv, -Env, -Adv, -Rest})
      (invar_rest : glob Rest -> bool, term_rest : glob Rest -> int,
       invar_par : glob Par -> bool, term_par : glob Par -> int)
      (func' : addr, in_guard_low' in_guard_hi' : int fset) &m :
  (forall (gl : glob Rest), 0 <= term_rest gl) =>
  equiv
  [Rest.init ~ Rest.init :
   ={self} ==>
   ={glob Rest} /\ invar_rest (glob Rest){1}] =>
  (forall (n : int),
   equiv
   [Rest.invoke ~ Rest.invoke :
    ={m, glob Rest} /\ invar_rest (glob Rest){1} /\
    term_rest (glob Rest){1} = n ==>
    ={res, glob Rest} /\ invar_rest (glob Rest){1} /\
    (res{1} <> None => term_rest (glob Rest){1} < n)]) =>
  (forall (gl : glob Par), 0 <= term_par gl) =>
  equiv
  [Par.init ~ Par.init :
   ={self} ==>
   ={glob Par} /\ invar_par (glob Par){1}] =>
  (forall (n : int),
   equiv
   [Par.invoke ~ Par.invoke :
    ={m, glob Par} /\ invar_par (glob Par){1} /\
    term_par (glob Par){1} = n ==>
    ={res, glob Par} /\ invar_par (glob Par){1} /\
    (res{1} <> None => term_par (glob Par){1} < n)]) =>
  exper_pre func' =>
  in_guard_low' \subset in_guard_hi' =>
  rest_adv_pi_ok in_guard_hi' =>
  CompEnv.in_guard_low{m} = in_guard_low' =>
  Pr[Exper(MI(MakeRFComp(Rest, Par), Adv), Env)
       .main(func', in_guard_low') @ &m : res] =
  Pr[Exper(MI(Par, Adv), CompEnv(Rest, Env))
       .main(func' ++ [change_pari], in_guard_hi') @ &m : res].
proof.
move =>
  ge0_term_rest rest_init rest_invoke
  ge0_term_par  par_init  par_invoke
  ep_func' sub_in_guard_low'_in_guard_high' rest_adv_pi_ok_in_guard_hi'
  eq_in_guard_low_ce_in_guard_low'.
apply
  (comp_bridge Env Adv Rest Par
   invar_rest term_rest invar_par term_par
   ge0_term_rest rest_init rest_invoke
   ge0_term_par par_init par_invoke
   _ _ _ &m) => //.
qed.

end CompBridge.
