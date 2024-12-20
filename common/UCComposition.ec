(* Theory for Composition Theorem Definitions and Proofs *)

prover quorum=2 ["Z3" "Alt-Ergo"].

require import UCCore UCListAux.

(* in the abstract theory, Composition, below, we'll use both the
   top-level INTER MI, but also the following one inside the composed
   environment, CompEnv *)

clone MakeInterface as CompEnvMakeInt
proof *.
module CompEnvMI = CompEnvMakeInt.MI.

(* global variables of all instances of abstract theory *)

module CompGlobs = {
  (* global of instances of MakeRFComp *)

  var mrfc_self : addr

  (* globals of instances of CompEnv *)

  var ce_stub_st : msg option
  var ce_func    : addr

  (* force inclusion in `glob CompGlobs` of `glob CompEnvMI` *)

  proc comp_env_mi_dummy() : unit = {
    var func : addr; var in_guard : int fset;
    func <- CompEnvMI.func; in_guard <- CompEnvMI.in_guard;
  }
}.

(*
print glob CompGlobs.

Globals [# = 0]:

Prog. variables [# = 5]:
  CompGlobs.ce_func : addr
  CompGlobs.ce_stub_st : msg option
  CompGlobs.mrfc_self : addr
  CompEnvMakeInt.MI.func : addr
  CompEnvMakeInt.MI.in_guard : int fset
*)

(* abstract theory for composition theorem

   each instance shares the same globals, which simplifies
   module restrictions *)

abstract theory Composition.

(* begin theory parameters *)

op rf_info : rf_info.

axiom rf_info_valid : rf_info_valid rf_info.

op change_pari : int.  (* parameter being changed from real to ideal *)

axiom change_pari_valid : 1 <= change_pari <= rf_info.`rfi_num_params.

(* end theory parameters *)

module MakeRFComp (Rest : FUNC, Par : FUNC) : FUNC = {
  proc init(_self : addr) : unit = {
    CompGlobs.mrfc_self <- _self;
    Rest.init(_self);
    Par.init(_self ++ [change_pari]);
  }

  (* the same as after_core from MakeRF: *)

  proc after_par_or_rest(r : msg option, orig_dest_addr : addr)
         : msg option * msg * bool = {
    var m : msg <- witness;
    var not_done <- true;
    if (r = None) {
      not_done <- false;
    }
    else {
      m <- oget r;  (* next iteration, if any, will use m *)
      if (m.`1 = Dir) {
        if (m.`3.`1 = CompGlobs.mrfc_self /\
            CompGlobs.mrfc_self = orig_dest_addr) {
          if (envport CompGlobs.mrfc_self m.`2) {
            not_done <- false;
          }
          elif (addr_eq_subfun rf_info CompGlobs.mrfc_self m.`2.`1 \/
                addr_eq_param rf_info CompGlobs.mrfc_self m.`2.`1) {
          }
          else {
            not_done <- false; r <- None;
          }
        }
        elif (addr_eq_subfun rf_info CompGlobs.mrfc_self m.`3.`1 /\
              m.`3.`1 = orig_dest_addr /\ m.`2.`1 = CompGlobs.mrfc_self) {
        }
        elif (addr_eq_param rf_info CompGlobs.mrfc_self m.`3.`1 /\
              CompGlobs.mrfc_self ++
              [next_of_addr CompGlobs.mrfc_self m.`3.`1] <= orig_dest_addr /\
              m.`2.`1 = CompGlobs.mrfc_self) {
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
        elif ((m.`3.`1 = CompGlobs.mrfc_self \/
               addr_eq_subfun rf_info CompGlobs.mrfc_self m.`3.`1) /\
              m.`3.`1 = orig_dest_addr) {
        }
        elif (addr_ge_param rf_info CompGlobs.mrfc_self m.`3.`1 /\
              CompGlobs.mrfc_self ++
              [next_of_addr CompGlobs.mrfc_self m.`3.`1] <= orig_dest_addr) {
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
      if (CompGlobs.mrfc_self ++ [change_pari] <= m.`2.`1) {
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
    (* we can assume m.`3.`1 is not >= CompGlobs.mrfc_self *)
    if ((m.`1 = Dir /\ m.`2.`1 = CompGlobs.mrfc_self) \/
        (m.`1 = Adv /\
         (m.`2.`1 = CompGlobs.mrfc_self \/
          addr_ge_param rf_info CompGlobs.mrfc_self m.`2.`1 \/
          addr_eq_subfun rf_info CompGlobs.mrfc_self m.`2.`1))) {
      r <@ loop(m);
    }
    return r;
  }
}.

op after_par_or_rest_return
   (func : addr, r : msg option, orig_dest_addr : addr) : bool =
  r <> None /\
  (((oget r).`1 = Dir /\ (oget r).`3.`1 = func /\ func = orig_dest_addr /\
    envport func (oget r).`2) \/
   ((oget r).`1 = Adv /\ (oget r).`2.`1 = adv /\ 0 < (oget r).`2.`2 /\
    ((((oget r).`3.`1 = func \/ addr_eq_subfun rf_info func (oget r).`3.`1) /\
       (oget r).`3.`1 = orig_dest_addr) \/
     (addr_ge_param rf_info func (oget r).`3.`1 /\
      func ++ [next_of_addr func (oget r).`3.`1] <= orig_dest_addr)))).

op after_par_or_rest_continue
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

op after_par_or_rest_error
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
      (Rest <: FUNC) (Par <: FUNC) (r' : msg option) :
  phoare
  [MakeRFComp(Rest, Par).after_par_or_rest :
   r = r' /\
   after_par_or_rest_return CompGlobs.mrfc_self r orig_dest_addr ==>
   res.`1 = r' /\ res.`1 = Some res.`2 /\ !res.`3] = 1%r.
proc; auto; smt().
qed.

lemma MakeRFComp_after_par_or_rest_continue
      (Rest <: FUNC) (Par <: FUNC) (r' : msg option) :
  phoare
  [MakeRFComp(Rest, Par).after_par_or_rest :
   r = r' /\
   after_par_or_rest_continue CompGlobs.mrfc_self r orig_dest_addr ==>
   res.`1 = r' /\ res.`1 = Some res.`2 /\ res.`3] = 1%r.
proof.
proc => /=.
auto;
  smt(disjoint_addr_eq_param_envport
      disjoint_addr_eq_subfun_envport).
qed.

lemma MakeRFComp_after_par_or_rest_error (Rest <: FUNC) (Par <: FUNC) :
  phoare
  [MakeRFComp(Rest, Par).after_par_or_rest :
   after_par_or_rest_error CompGlobs.mrfc_self r orig_dest_addr ==>
   res.`1 = None /\ ! res.`3] = 1%r.
proof.
proc => /=.
auto;
  smt(not_addr_eq_param_self not_addr_eq_subfun_self
      not_addr_eq_param_self not_addr_eq_subfun_self
      not_addr_ge_param_self disjoint_addr_ge_param_eq_subfun).
qed.

(* we prove that the after_par_or_rest operators are equivalent on
   original destination addresses that are >= func ++ [change_pari] *)

lemma cond_equiv_ge_param_test
      (func : addr, m : msg, oda1 oda2 : addr) :
  func ++ [change_pari] <= oda1 => func ++ [change_pari] <= oda2 =>
  (addr_ge_param rf_info func m.`3.`1 /\
   func ++ [next_of_addr func m.`3.`1] <= oda1) =
  (addr_ge_param rf_info func m.`3.`1 /\
   func ++ [next_of_addr func m.`3.`1] <= oda2).
proof.
move => le_oda1 le_oda2.
smt(next_of_addr_ge_self_plus not_le_other_branch).
qed.

lemma pari_cond_after_par_or_rest_return_equiv
      (func : addr, r : msg option, oda1 oda2 : addr) :
  func ++ [change_pari] <= oda1 => func ++ [change_pari] <= oda2 =>
  after_par_or_rest_return func r oda1 <=>
  after_par_or_rest_return func r oda2.
proof.
move => le_oda1 le_oda2.
rewrite /after_par_or_rest_return.
rewrite (cond_equiv_ge_param_test func (oget r) oda1 oda2) //.
have -> : func <> oda1 by smt(not_le_ext_nonnil_l).
have -> /= : func <> oda2 by smt(not_le_ext_nonnil_l).
smt(rf_info_valid change_pari_valid next_of_addr_ge_self_plus).
qed.

lemma pari_cond_after_par_or_rest_continue_equiv
      (func : addr, r : msg option, oda1 oda2 : addr) :
  func ++ [change_pari] <= oda1 => func ++ [change_pari] <= oda2 =>
  after_par_or_rest_continue func r oda1 <=>
  after_par_or_rest_continue func r oda2.
proof.
move => le_oda1 le_oda2.
rewrite /after_par_or_rest_continue.
have -> : func <> oda1 by smt(not_le_ext_nonnil_l).
have -> /= : func <> oda2 by smt(not_le_ext_nonnil_l).
smt(le_pre le_cons rf_info_valid change_pari_valid
    not_le_other_branch).
qed.

lemma pari_cond_after_par_or_rest_error_equiv
      (func : addr, r : msg option, oda1 oda2 : addr) :
  func ++ [change_pari] <= oda1 => func ++ [change_pari] <= oda2 =>
  after_par_or_rest_error func r oda1 <=>
  after_par_or_rest_error func r oda2.
proof.
move => le_oda1 le_oda2.
smt(pari_cond_after_par_or_rest_continue_equiv
    pari_cond_after_par_or_rest_return_equiv
    after_par_or_rest_disj).
qed.

lemma after_par_or_rest_return_intro_adv_from_param
      (func : addr, r : msg option, orig_dest_addr : addr) :
 r <> None => (oget r).`1 = Adv => (oget r).`2.`1 = adv =>
 0 < (oget r).`2.`2 =>
 addr_ge_param rf_info func (oget r).`3.`1 =>
 func ++ [next_of_addr func (oget r).`3.`1] <= orig_dest_addr =>
 after_par_or_rest_return func r orig_dest_addr.
proof.
move => non_None mod dest_adv gt0_dest_pi src_ge_param oda_ge_par.
rewrite /after_par_or_rest_return.
rewrite non_None /=.
right; smt().
qed.

lemma after_par_or_rest_return_intro_adv_from_rest
      (func : addr, r : msg option, orig_dest_addr : addr) :
 r <> None => (oget r).`1 = Adv => (oget r).`2.`1 = adv =>
 0 < (oget r).`2.`2 =>
 ((oget r).`3.`1 = func \/ addr_eq_subfun rf_info func (oget r).`3.`1) =>
 (oget r).`3.`1 = orig_dest_addr =>
 after_par_or_rest_return func r orig_dest_addr.
proof.
move => non_None mod dest_adv gt0_dest_pi src_eq_func_or_eq_sf src_eq_oda.
rewrite /after_par_or_rest_return.
rewrite non_None /=.
right; smt().
qed.

(* specialization of addr_eq and addr_ge operators to rest / changed
   parameter *)

op addr_ge_param_change (self addr : addr) : bool =
  self ++ [change_pari] <= addr.

op addr_ge_param_rest (rfi : rf_info, self addr : addr) : bool =
  exists (k : int),
  (1 <= k < change_pari \/ change_pari < k <= rfi.`rfi_num_params) /\
  self ++ [k] <= addr.

op addr_eq_param_change (self addr : addr) : bool =
  addr = self ++ [change_pari].

op addr_eq_param_rest (rfi : rf_info, self addr : addr) : bool =
  exists (k : int),
  (1 <= k < change_pari \/ change_pari < k <= rfi.`rfi_num_params) /\
  addr = self ++ [k].

(* lemmas relating the MakeInt.after_func_... lemmas and the
   after_par_or_rest_... lemmas *)

lemma after_func_to_adv_ch_pari_implies_after_par_or_rest_return_and_adv
      (func : addr, r : msg option, orig_dest_addr : addr) :
  func ++ [change_pari] <= orig_dest_addr =>
  MakeInt.after_func_to_adv (func ++ [change_pari]) r =>
  (after_par_or_rest_return func r orig_dest_addr /\
   (oget r).`1 = Adv).
proof.
move => oda_ge_addr_ch_pari.
rewrite /after_func_to_adv /after_par_or_rest_return.
smt(change_pari_valid next_of_addr_ge_self_plus).
qed.

lemma after_par_or_rest_return_implies_to_env_or_adv
      (func : addr, r : msg option, orig_dest_addr : addr) :
  after_par_or_rest_return func r orig_dest_addr =>
  MakeInt.after_func_to_env func r \/
  MakeInt.after_func_to_adv func r.
proof.
rewrite /after_par_or_rest_return /after_func_to_env
        /after_func_to_adv.
move => [] r_ne_None [] [#].
move => -> -> _ ep //.
move => -> -> gt0_advpi [[] [] |].
move => -> _ //.
rewrite /addr_eq_subfun => [[k]] [#] _ _ -> //.
rewrite /addr_ge_param => [] [] [k] [#] _ _ src_ge_func_k _ /=.
rewrite r_ne_None gt0_advpi /=.
by rewrite (le_trans (func ++ [k])) 1:le_ext_r.
qed.

lemma after_par_or_rest_return_from_change_pari
      (func : addr, r : msg option, orig_dest_addr : addr) :
  func ++ [change_pari] <= orig_dest_addr =>
  after_par_or_rest_return func r orig_dest_addr =>
  (oget r).`1 = Adv =>
  r <> None /\ (oget r).`2.`1 = adv /\ 0 < (oget r).`2.`2 /\
  func ++ [change_pari] <= (oget r).`3.`1.
proof.
move => oda_ge_addr_ch_pari.
rewrite /after_par_or_rest_return.
smt(next_of_addr_ge_self_plus).
qed.

lemma after_par_or_rest_return_from_rest
      (func : addr, r : msg option, orig_dest_addr : addr) :
  ! func ++ [change_pari] <= orig_dest_addr => (oget r).`1 = Adv =>
  after_par_or_rest_return func r orig_dest_addr =>
  r <> None /\ (oget r).`2.`1 = adv /\ 0 < (oget r).`2.`2 /\
  func <= (oget r).`3.`1 /\ ! func ++ [change_pari] <= (oget r).`3.`1.
proof.
move => oda_nge_addr_ch_pari.
rewrite /after_par_or_rest_return.
move => -> /= [#] -> -> -> /= [[] [] |].
move => -> _; smt(not_le_ext_nonnil_l le_refl).
rewrite /addr_eq_subfun => [[k]] [] rng_k -> func_plus_k_eq_oda.
split; first rewrite le_ext_r.
move : oda_nge_addr_ch_pari.
by rewrite func_plus_k_eq_oda.
rewrite /addr_ge_param => [] [] [k] [] k_rng src_ge_func_plus_k.
have -> : next_of_addr func (oget r).`3.`1 = k
  by smt(next_of_addr_ge_self_plus).
move => func_plus_k_le_oda.
split; first by rewrite (le_trans (func ++ [k])) 1:le_ext_r.
have k_ne_change_pari : k <> change_pari by smt().
smt(not_le_other_branch).
qed.

lemma after_func_error_ch_pari_implies_after_par_or_rest_error
      (func : addr, r : msg option, orig_dest_addr : addr) :
  inc func adv => func ++ [change_pari] <= orig_dest_addr =>
  MakeInt.after_func_error (func ++ [change_pari]) r =>
  after_par_or_rest_error func r orig_dest_addr.
proof.
move => inc_func_adv oda_ge_addr_ch_pari.
rewrite /after_func_error /after_par_or_rest_error.
move => [// | [dest_ge_par |]].
smt(not_le_ext_nonnil_l inc_extl inc_nle_l).
move => [[] -> [#] [| [| src_ne_par]] |].
smt(inc_nle_r  not_le_ext_nonnil_l).
smt(inc_non_nil not_le_ext_nonnil_l).
right; right => /=; split; [idtac | split].
smt(not_le_ext_nonnil_l).
smt(le_refl next_of_addr_ge_self_plus).
case (addr_eq_param rf_info func (oget r).`3.`1) => [/= | //].
rewrite /addr_eq_param => [[k]] [#] _ _ src_eq.
rewrite src_eq.
have -> :
  next_of_addr func (func ++ [k]) = k
  by apply next_of_addr_ge_self_plus.
case (k = change_pari) => [// | k_ne_change_pari].
smt(not_le_other_branch).
smt(next_of_addr_ge_self_plus).
qed.

lemma after_func_to_env_ch_pari_implies_after_par_or_rest_cont_or_error
      (func : addr, r : msg option, orig_dest_addr : addr) :
  MakeInt.after_func_to_env (func ++ [change_pari]) r =>
  after_par_or_rest_continue func r orig_dest_addr \/
  after_par_or_rest_error func r orig_dest_addr.
proof.
rewrite /after_func_to_env /after_par_or_rest_continue
        /after_par_or_rest_error => [#] -> -> ep_par <- /= /#.
qed.

lemma after_par_or_rest_continue_from_change_pari
      (func : addr, r : msg option, orig_dest_addr : addr) :
  func ++ [change_pari] <= orig_dest_addr =>
  after_par_or_rest_continue func r orig_dest_addr =>
  r <> None /\ (oget r).`1 = Dir /\ (oget r).`2.`1 = func /\
  (oget r).`3.`1 = func ++ [change_pari].
proof.
move => oda_ge_addr_ch_pari.
rewrite /after_par_or_rest_continue.
smt(le_refl le_pre le_cons not_le_ext_nonnil_l
    rf_info_valid change_pari_valid
    next_of_addr_ge_self_plus).
qed.

(* adv pis as fset for parameter being changed *)

op change_par_adv_pis : int fset =
  rangeset (nth1_adv_pi_begin_params rf_info change_pari)
  (nth1_adv_pi_end_params rf_info change_pari + 1).

lemma in_change_par_adv_pis (z : int) :
  z \in change_par_adv_pis <=>
  nth1_adv_pi_begin_params rf_info change_pari <= z <=
  nth1_adv_pi_end_params rf_info change_pari.
proof.
rewrite /change_par_adv_pis.
by rewrite mem_rangeset ltzS.
qed.

(* adv pis as fset for rest *)

op union_map (f : 'a -> 'b fset, xs : 'a list) : 'b fset =
  foldr (`|`) fset0 (map f xs).

lemma in_union_map (f : 'a -> 'b fset, xs : 'a list, z : 'b) :
  z \in union_map f xs <=>
  has (fun ys => FSet.mem ys z) (map f xs).
proof.
elim xs => [/= |].
by rewrite /union_map /= in_fset0.
move => x xs IH.
rewrite /union_map /= in_fsetU.
congr; by rewrite -IH.
qed.

op rest_adv_pis : int fset =
  rangeset rf_info.`rfi_adv_pi_begin
  (rf_info.`rfi_adv_pi_main_end + 1) `|`
  union_map
  (fun pari =>
    rangeset (nth1_adv_pi_begin_params rf_info pari)
    (nth1_adv_pi_end_params rf_info pari + 1))
  (range 1 change_pari) `|`
  union_map
  (fun pari =>
    rangeset (nth1_adv_pi_begin_params rf_info pari)
    (nth1_adv_pi_end_params rf_info pari + 1))
  (range (change_pari + 1) (rf_info.`rfi_num_params + 1)).

lemma in_rest_adv_pis (z : int) :
  z \in rest_adv_pis <=>
  rf_info.`rfi_adv_pi_begin <= z <= rf_info.`rfi_adv_pi_main_end \/
  (exists pari,
   1 <= pari < change_pari /\
   nth1_adv_pi_begin_params rf_info pari <= z <=
   nth1_adv_pi_end_params rf_info pari) \/
  (exists pari,
   change_pari < pari <= rf_info.`rfi_num_params /\
   nth1_adv_pi_begin_params rf_info pari <= z <=
   nth1_adv_pi_end_params rf_info pari).
proof.
have rfi_valid := rf_info_valid.
have change_pari_valid := change_pari_valid.
rewrite /rest_adv_pis.
rewrite !in_fsetU mem_rangeset ltzS !in_union_map !has_map !hasP
        !/preim.
split =>
  [[[-> // | [pari] []] | [pari]] |
   [-> // |
    [[pari] [] pari_range z_range |
     [pari] [] pari_range z_range]]].
rewrite mem_range => x_range.
rewrite mem_rangeset ltzS => z_range.
right; left; exists pari; smt().
rewrite mem_range ltzS => [[pari_range]].
rewrite mem_rangeset ltzS => z_range.
right; right; exists pari; smt().
left; right; exists pari.
rewrite mem_range mem_rangeset /#.
right; exists pari.
rewrite mem_range mem_rangeset /#.
qed.

lemma union_change_rest_eq_all_adv_pis_of_rf_info :
  change_par_adv_pis `|` rest_adv_pis = adv_pis_rf_info rf_info.
proof.
rewrite fsetP => x.
rewrite /adv_pis_rf_info.
have -> /= : rf_info.`rfi_num_params <> 0 by smt(change_pari_valid).
rewrite mem_rangeset in_fsetU in_change_par_adv_pis in_rest_adv_pis ltzS.
split =>
  [[[A1 A2] |
    [[B1 B2] | [[pari] [#] C1 C2 C3 C4 | [pari] [#] D1 D2 D3 D4]]] |
   [] E1 E2].
split => [| _].
smt(rf_info_valid change_pari_valid
    rfi_valid_adv_pi_main_end_lt_adv_pi_param_begin).
smt(rf_info_valid change_pari_valid
    rfi_valid_lt_par_indices_implies_lt_param_adv_pi_begins).
smt(rf_info_valid change_pari_valid
    rfi_valid_adv_pi_main_end_lt_adv_pi_param_begin).
split => [| _].
smt(rf_info_valid change_pari_valid
    rfi_valid_adv_pi_main_end_lt_adv_pi_param_begin).
smt(rf_info_valid change_pari_valid
    rfi_valid_lt_par_indices_implies_lt_param_adv_pi_begins).
split => [| _].
smt(rf_info_valid change_pari_valid
    rfi_valid_adv_pi_main_end_lt_adv_pi_param_begin).
smt(rf_info_valid change_pari_valid
    rfi_valid_lt_par_indices_implies_lt_param_adv_pi_begins).
case (x <= rf_info.`rfi_adv_pi_main_end) => [/# | gt_main_end /=].
rewrite lezNgt /= in gt_main_end.
have ge_begin_1 : nth1_adv_pi_begin_params rf_info 1 <= x.
smt(rf_info_valid change_pari_valid).
clear E1 gt_main_end.
have [pari] [] pari_range x_pari_adv_pi_range /#
    := rfi_valid_param_adv_pi_in_range_for_pari
       rf_info x _ _ _ => //.
  apply rf_info_valid.
  smt(rf_info_valid change_pari_valid).
qed.

lemma disjoint_change_rest :
  disjoint change_par_adv_pis rest_adv_pis.
proof.
have rfi_valid := rf_info_valid.
have change_pari_valid := change_pari_valid.
rewrite disjointP => k.
rewrite /change_par_adv_pis mem_rangeset ltzS => k_range.
rewrite in_rest_adv_pis !negb_or.
split; last split.
smt(rfi_valid_adv_pi_main_end_lt_adv_pi_param_begin).
smt(mem_range rfi_valid_lt_par_indices_implies_lt_param_adv_pi_begins).
smt(mem_range rfi_valid_lt_par_indices_implies_lt_param_adv_pi_begins).
qed.

(* composed environment, made out of Rest and Env *)

(* dummy messages between stubs of CompEnv *)

op dummy_msg_to_stub_adv (func : addr) : msg =
  (Adv, (adv, 1), (func ++ [change_pari], 1), TagNoInter, []).

op dummy_msg_to_stub_par (func : addr) : msg =
  (Adv, (func ++ [change_pari], 1), (adv, 1), TagNoInter, []).

module CompEnv (Rest : FUNC, Env : ENV, Inter : INTER) = {
  module StubPar : FUNC = {
    proc init(func : addr) : unit = { }

    proc invoke(m : msg) : msg option = {
      var r : msg option;
      if (CompGlobs.ce_stub_st <> None) {
        r <- CompGlobs.ce_stub_st; CompGlobs.ce_stub_st <- None;
      }
      else {
        r <@ Inter.invoke(m);
        if (r <> None) {
          m <- oget r;
          if (m.`1 = Adv) {
            CompGlobs.ce_stub_st <- Some m;
            r <- Some (dummy_msg_to_stub_adv CompGlobs.ce_func);
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
      if (CompGlobs.ce_stub_st <> None) {
        r <- CompGlobs.ce_stub_st; CompGlobs.ce_stub_st <- None;
      }
      else {
        r <@ Inter.invoke(m);
        if (r <> None) {
          m <- oget r;
          if (m.`1 = Dir) {
            CompGlobs.ce_stub_st <- Some m;
            r <- Some (dummy_msg_to_stub_par CompGlobs.ce_func);
          }
        }
      }
      return r;
    }
  }

  (* func_ will end with change_pari *)

  proc main(func_ : addr, in_guard : int fset) : bool = {
    var b : bool;
    CompGlobs.ce_stub_st <- None;
    CompGlobs.ce_func <- take (size func_ - 1) func_;
    b <@ Exper(CompEnvMI(MakeRFComp(Rest, StubPar), StubAdv), Env)
           .main(CompGlobs.ce_func, in_guard `\` rest_adv_pis);
    return b;
  }
}.

section.

declare module Env  <: ENV{-MI, -CompGlobs}.
declare module Adv  <: ADV{-MI, -CompGlobs, -Env}.
declare module Rest <: FUNC{-MI, -CompGlobs, -Env, -Adv}.
declare module Par  <: FUNC{-MI, -CompGlobs, -Env, -Adv, -Rest}.

declare op invar_rest : glob Rest -> bool.
declare op term_rest  : glob Rest -> int.

declare op invar_par  : glob Par  -> bool.
declare op term_par   : glob Par  -> int.

declare axiom ge0_term_rest (gl : glob Rest) :
  invar_rest gl => 0 <= term_rest gl.

declare axiom Rest_init :
   equiv
   [Rest.init ~ Rest.init :
    ={self, glob Rest} ==>
    ={glob Rest} /\ invar_rest (glob Rest){1}].

declare axiom Rest_invoke (n : int) :
   equiv
   [Rest.invoke ~ Rest.invoke :
    ={m, glob Rest} /\ invar_rest (glob Rest){1} /\
    term_rest (glob Rest){1} = n ==>
    ={res, glob Rest} /\ invar_rest (glob Rest){1} /\
    (res{1} <> None =>
     term_rest (glob Rest){1} < n /\
     ((oget res{1}).`1 = Adv => (oget res{1}).`2.`2 \in rest_adv_pis))].

declare axiom ge0_term_par (gl : glob Par) :
  invar_par gl => 0 <= term_par gl.

declare axiom Par_init :
   equiv
   [Par.init ~ Par.init :
    ={self, glob Par} ==>
    ={glob Par} /\ invar_par (glob Par){1}].

declare axiom Par_invoke (n : int) :
   equiv
   [Par.invoke ~ Par.invoke :
    ={m, glob Par} /\ invar_par (glob Par){1} /\
    term_par (glob Par){1} = n ==>
    ={res, glob Par} /\ invar_par (glob Par){1} /\
    (res{1} <> None =>
     term_par (glob Par){1} < n /\
     ((oget res{1}).`1 = Adv => (oget res{1}).`2.`2 \in change_par_adv_pis))].

local module CompEnvStubPar : FUNC =
  CompEnv(Rest, Env, MakeInt.MI(Par, Adv)).StubPar.
local module CompEnvStubAdv : ADV  =
  CompEnv(Rest, Env, MakeInt.MI(Par, Adv)).StubAdv.

(* code blocks from the left / right sides of equational judgements *)

local module LeftMI = {
  proc f(m : msg) : msg option = {
    var not_done : bool <- true; var r : msg option <- None;
    while (not_done) {
      if (MI.func <= m.`2.`1) {
        r <@ MakeRFComp(Rest, Par).invoke(m);
        (r, m, not_done) <@ MI(MakeRFComp(Rest, Par), Adv).after_func(r);
      }
      else {
        r <@ Adv.invoke(m);
        (r, m, not_done) <@ MI(MakeRFComp(Rest, Par), Adv).after_adv(r);
      }
    }
    return r;
  }
}.

local module LeftMFRC = {
  proc f(m : msg) : msg option = {
    var not_done : bool <- true; var r : msg option <- None;
    while (not_done) {
      if (CompGlobs.mrfc_self ++ [change_pari] <= m.`2.`1) {
        r <@ Par.invoke(m);
      }
      else {
        r <@ Rest.invoke(m);
      }
      (r, m, not_done) <@
        MakeRFComp(Rest, Par).after_par_or_rest(r, m.`2.`1);
    }
    (r, m, not_done) <@ MI(MakeRFComp(Rest, Par), Adv).after_func(r);
    while (not_done) {
      if (MI.func <= m.`2.`1) {
        r <@ MakeRFComp(Rest, Par).invoke(m);
        (r, m, not_done) <@ MI(MakeRFComp(Rest, Par), Adv).after_func(r);
      }
      else {
        r <@ Adv.invoke(m);
        (r, m, not_done) <@ MI(MakeRFComp(Rest, Par), Adv).after_adv(r);
      }
    }
    return r;
  }
}.

local module RightMFRC = {
  proc f(m : msg) : msg option = {
    var not_done : bool <- true; var r : msg option <- None;
    while (not_done) {
      if (CompGlobs.mrfc_self ++ [change_pari] <= m.`2.`1) {
        r <@ CompEnvStubPar.invoke(m);
      }
      else {
        r <@ Rest.invoke(m);
      }
      (r, m, not_done) <@
        MakeRFComp(Rest, CompEnvStubPar).after_par_or_rest(r, m.`2.`1);
    }
    (r, m, not_done) <@
        CompEnvMI
        (MakeRFComp(Rest, CompEnvStubPar), CompEnvStubAdv).after_func(r);
    while (not_done) {
      if (CompEnvMI.func <= m.`2.`1) {
        r <@ MakeRFComp(Rest, CompEnvStubPar).invoke(m);
        (r, m, not_done) <@
          CompEnvMI
          (MakeRFComp(Rest, CompEnvStubPar), CompEnvStubAdv).after_func(r);
      }
      else {
        r <@ CompEnvStubAdv.invoke(m);
        (r, m, not_done) <@
          CompEnvMI
          (MakeRFComp(Rest, CompEnvStubPar), CompEnvStubAdv).after_adv(r);
      }
    }
    return r;
  }
}.

local module RightMIFromAdv = {
  proc f(m : msg) : msg option = {
    var not_done : bool <- true; var r : msg option <- None;

    while (not_done) {
      if (MI.func <= m.`2.`1) {
        r <@ Par.invoke(m);
        (r, m, not_done) <@ MI(Par, Adv).after_func(r);
      }
      else {
        r <@ Adv.invoke(m);
        (r, m, not_done) <@ MI(Par, Adv).after_adv(r);
      }
    }
    if (r <> None) {
      m <- oget r;
      if (m.`1 = Dir) {
        CompGlobs.ce_stub_st <- Some m;
        r <- Some (dummy_msg_to_stub_par CompGlobs.ce_func);
      }
    }
    (r, m, not_done) <@
       CompEnvMI
       (MakeRFComp
        (Rest, CompEnvStubPar), CompEnvStubAdv).after_adv(r);
    while (not_done) {
      if (CompEnvMI.func <= m.`2.`1) {
        r <@ MakeRFComp(Rest, CompEnvStubPar).invoke(m);
        (r, m, not_done) <@
          CompEnvMI
          (MakeRFComp(Rest, CompEnvStubPar),
           CompEnvStubAdv).after_func(r);
      }
      else {
        r <@ CompEnvStubAdv.invoke(m);
       (r, m, not_done) <@
         CompEnvMI
         (MakeRFComp(Rest, CompEnvStubPar),
          CompEnvStubAdv).after_adv(r);
      }
    }
    return r;
  }
}.

local module RightMIFromPar = {
  proc f(m : msg, m_orig : msg) : msg option = {
    var not_done : bool <- true; var r : msg option <- None;

    while (not_done) {
      if (MI.func <= m.`2.`1) {
        r <@ Par.invoke(m);
        (r, m, not_done) <@ MI(Par, Adv).after_func(r);
      }
      else {
        r <@ Adv.invoke(m);
        (r, m, not_done) <@ MI(Par, Adv).after_adv(r);
      }
    }
    if (r <> None) {
      m <- oget r;
      if (m.`1 = Adv) {
        CompGlobs.ce_stub_st <- Some m;
        r <- Some (dummy_msg_to_stub_adv CompGlobs.ce_func);
      }
    }
    (r, m, not_done) <@
      MakeRFComp(Rest, CompEnvStubPar).after_par_or_rest(r, m_orig.`2.`1);
    while (not_done) {
      if (CompGlobs.mrfc_self ++ [change_pari] <= m.`2.`1) {
        r <@ CompEnvStubPar.invoke(m);
      }
      else {
        r <@ Rest.invoke(m);
      }
      (r, m, not_done) <@
        MakeRFComp(Rest, CompEnvStubPar).after_par_or_rest(r, m.`2.`1);
    }
    (r, m, not_done) <@
       CompEnvMI
       (MakeRFComp
        (Rest, CompEnvStubPar), CompEnvStubAdv).after_func(r);
    while (not_done) {
      if (CompEnvMI.func <= m.`2.`1) {
        r <@ MakeRFComp(Rest, CompEnvStubPar).invoke(m);
        (r, m, not_done) <@
          CompEnvMI
          (MakeRFComp(Rest, CompEnvStubPar),
           CompEnvStubAdv).after_func(r);
      }
      else {
        r <@ CompEnvStubAdv.invoke(m);
       (r, m, not_done) <@
         CompEnvMI
         (MakeRFComp(Rest, CompEnvStubPar),
          CompEnvStubAdv).after_adv(r);
      }
    }
    return r;
  }
}.

lemma main_guard_ext
      (func : addr, i : int, in_guard : int fset, xs : int fset,
       m : msg) :
  MakeInt.main_guard func in_guard m => ! func <= m.`2.`1 =>
  MakeInt.main_guard (func ++ [i]) (in_guard `|` xs) m.
proof.
move => mg_in_guard_m dest_not_ge_func.
rewrite /main_guard.
right.
smt(in_fsetU not_le_ext le_refl).
qed.

lemma main_guard_ext_adv_advpi_in_new
      (func : addr, i : int, in_guard : int fset, xs : int fset,
       m : msg, orig_dest_addr : addr) :
  inc func adv => m.`1 = Adv => m.`2.`1 = adv =>
  0 < m.`2.`2 => m.`2.`2 \in xs =>
  func <= m.`3.`1 => ! func ++ [i] <= m.`3.`1 =>
  MakeInt.main_guard (func ++ [i]) (in_guard `|` xs) m.
proof.
move =>
  inc_func_adv mode_eq_Adv dest_adv dest_pi_gt0
  dest_advpi_in_xs src_ge_func src_nge_func_plus_i.
rewrite /MakeInt.main_guard /=.
right.
split; first trivial.
split; first trivial.
right.
split; first trivial.
split; first smt(in_fsetU).
rewrite /envport.
split; first smt(inc_le1_not_rl).
split; first smt(inc_le1_not_rl).
case (m.`3 = ([], 0)) => [src_eq | //].
move : src_ge_func.
rewrite src_eq /=.
case (func <= []) => [le_nil_func | //].
have le_func_adv : func <= adv.
  rewrite (le_trans []) // ge_nil.
smt(inc_nle_l).
qed.

lemma after_adv_to_func_not_guard_contrad (func : addr, r : msg option) :
  MakeInt.after_adv_to_func (func ++ [change_pari]) r =>
  ! (((oget r).`1 = Dir /\ (oget r).`2.`1 = func) \/
     ((oget r).`1 = Adv /\
      ((oget r).`2.`1 = func \/
       addr_ge_param rf_info func (oget r).`2.`1 \/
       addr_eq_subfun rf_info func (oget r).`2.`1))) =>
  false.
proof.
move => aatf not_guard.
rewrite negb_or !negb_and !negb_or not_dir not_adv /= in not_guard.
elim not_guard => _.
move => [/# | [#] _ not_ge_param _].
smt(rf_info_valid change_pari_valid).
qed.

lemma after_par_or_rest_continue_implies_pre_cond_equiv1 self m oda :
  inc self adv =>
  after_par_or_rest_continue self (Some m) oda =>
  (m.`2.`1 = self \/
   addr_eq_subfun rf_info self m.`2.`1 \/
   m.`1 = Dir /\ addr_eq_param_rest rf_info self m.`2.`1 \/
   m.`1 = Dir /\ m.`2.`1 = self ++ [change_pari] /\
   envport (self ++ [change_pari]) m.`3).
proof.
move => inc_self_adv.
rewrite /after_par_or_rest_continue /= => [[]] is_dir.
move => [[#] src_eq_self _ [/# |] | /#].
rewrite /addr_eq_param => [[k] [#] ge1_k le_np_k ->].
case (k = change_pari) => [-> | /#].
right; right; right => /=.
rewrite is_dir /= /envport src_eq_self.
split; first by rewrite not_le_ext_nonnil_l.
split; first smt(inc_nle_r).
case (m.`3 = ([], 0)) => [src_eq_env_root_port | //].
have self_nil : self = [] by rewrite -src_eq_self /#.
smt(not_inc_nil_left).
qed.

(* this lemma assumes the first and second equiv's from
   comp_bridge_induct with the same termination metric as
   the conclusion *)

local lemma LeftMI_RightMIFromAdv
      (n : int, func': addr, in_guard_low': int fset) :
  exper_pre func' =>
  equiv
  [LeftMFRC.f ~ RightMFRC.f :
   ={m} /\
   (m{1}.`2.`1 = CompGlobs.mrfc_self{1} \/
    addr_eq_subfun rf_info CompGlobs.mrfc_self{1} m{1}.`2.`1 \/
    (m{1}.`1 = Dir /\
     addr_eq_param_rest rf_info CompGlobs.mrfc_self{1} m{1}.`2.`1) \/
    (m{1}.`1 = Adv /\
     addr_ge_param_rest rf_info CompGlobs.mrfc_self{1} m{1}.`2.`1) \/
    (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{2} /\ envport MI.func{2} m{1}.`3)) /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={res, glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None] =>
  equiv
  [LeftMFRC.f ~ RightMIFromAdv.f :
   ={m} /\ m{1}.`1 = Adv /\ MI.func{2} <= m{1}.`2.`1 /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={res, glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None] =>
  equiv
  [LeftMI.f ~ RightMIFromAdv.f :
   ={m} /\ m{1}.`1 = Adv /\ m{1}.`2.`1 = adv /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={res, glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None].
proof.
move => ep_func' first second.
proc; sp 2 2.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
rcondf{1} 1; first auto; smt(inc_nle_l).
rcondf{2} 1; first auto; smt(inc_extl inc_nle_l).
seq 1 1 :
  (={r} /\ ={glob Adv, glob Rest, glob Par} /\
  term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
  invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
  MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
  MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
  CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
  MI.func{2} = func' ++ [change_pari] /\
  CompEnvMI.in_guard{2} = in_guard_low' /\
  MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
  CompGlobs.ce_stub_st{2} = None).
call (_ : true); first auto.
case (MakeInt.after_adv_to_env MI.func{1} r{1}).
seq 1 0 :
  (={r} /\ r{1} = Some m{1} /\ !not_done{1} /\
   MakeInt.after_adv_to_env MI.func{1} r{1} /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
exlim r{1} => r_L.
call{1} (MakeInt.MI_after_adv_to_env (MakeRFComp(Rest, Par)) Adv r_L).
auto.
rcondf{1} 1; first auto.
wp.
conseq
  (_ :
   ={r} /\
   MakeInt.after_adv_to_env MI.func{1} r{1} /\
   MakeInt.after_adv_to_env MI.func{2} r{1} /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
    invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   _); first smt(MakeInt.after_adv_to_env_ext).
seq 0 1 :
  (={r} /\ r{1} <> None /\ !not_done{2} /\
   MakeInt.after_adv_to_env MI.func{1} r{1} /\
   MakeInt.after_adv_to_env MI.func{2} r{1} /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
exlim r{2} => r'.
call{2} (MakeInt.MI_after_adv_to_env Par Adv r').
auto; smt(inc_extl).
rcondf{2} 1; first auto. rcondt{2} 1; first auto.
rcondf{2} 2; first auto; smt().
sp 0 1.
seq 0 1 :
  (={r} /\ !not_done{2} /\
   MakeInt.after_adv_to_env MI.func{1} r{1} /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
exlim r{2} => r'.
call{2}
  (CompEnvMakeInt.MI_after_adv_to_env (MakeRFComp(Rest, CompEnvStubPar))
   CompEnvStubAdv r').
auto; smt(inc_extl).
rcondf{2} 1; first auto.
auto.
case (MakeInt.after_adv_to_func MI.func{1} r{1}).
conseq
  (_ :
    ={r} /\ ={glob Adv, glob Rest, glob Par} /\
    term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
    invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
    MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
    MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
    CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
    MI.func{2} = func' ++ [change_pari] /\
    CompEnvMI.in_guard{2} = in_guard_low' /\
    MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
    CompGlobs.ce_stub_st{2} = None /\
    ! MakeInt.after_adv_to_env MI.func{1} r{1} /\
    MakeInt.after_adv_to_func MI.func{1} r{1} /\
    (MakeInt.after_adv_to_func MI.func{2} r{1} \/
     MakeInt.after_adv_to_env MI.func{2} r{1}) ==>
    _); first smt(inc_extl MakeInt.after_adv_to_func_ext_to_func_or_env).
seq 1 0 :
  (={r} /\ r{1} = Some m{1} /\ not_done{1} /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None /\
   ! MakeInt.after_adv_to_env MI.func{1} r{1} /\
   MakeInt.after_adv_to_func MI.func{1} r{1} /\
   (MakeInt.after_adv_to_func MI.func{2} r{1} \/
    MakeInt.after_adv_to_env MI.func{2} r{1})).
exlim r{1} => r'.
call{1} (MakeInt.MI_after_adv_to_func (MakeRFComp(Rest, Par)) Adv r').
auto.
rcondt{1} 1; first auto.
rcondt{1} 1; first auto; smt(oget_some).
inline{1} 1.
sp 2 0.
if{1}.
inline{1} 1.
sp 3 0.
case (MakeInt.after_adv_to_func MI.func{2} r{2}).
seq 0 1 :
  (m1{1} = m{2} /\ not_done0{1} /\ not_done{2} /\
   r{2} = Some m{2} /\ m{2}.`1 = Adv /\ MI.func{2} <= m{2}.`2.`1 /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
exlim r{2} => r'.
call{2} (MakeInt.MI_after_adv_to_func Par Adv r').
auto; smt(inc_extl oget_some).
wp.
(* start of reduction to second *)
conseq
  (_ :
   m1{1} = m{2} /\ not_done0{1} /\ not_done{2} /\
   m1{1}.`1 = Adv /\ MI.func{2} <= m1{1}.`2.`1 /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   _) => //.
transitivity{1}
  {r <@ LeftMFRC.f(m1);}
  (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={m1} /\ not_done0{1} ==>
   ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={r})
  (m1{1} = m{2} /\ not_done{2} /\
   m1{1}.`1 = Adv /\ MI.func{2} <= m1{1}.`2.`1 /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={glob Adv, glob Rest, glob Par} /\ ={r} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None) => //.
progress.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       CompGlobs.ce_func{1} CompGlobs.ce_stub_st{1}
       MakeInt.MI.func{1} CompEnvMakeInt.MI.func{1}
       CompEnvMakeInt.MI.in_guard{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} m{2} => //.
inline{2} 1; sp 0 3.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
transitivity{2}
  {r <@ RightMIFromAdv.f(m);}
  (m1{1} = m{2} /\ m1{1}.`1 = Adv /\ MI.func{2} <= m1{1}.`2.`1 /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={r} /\ ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None)
  (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   not_done{2} /\ ={m} ==>
   ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={r}) => //.
progress.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       MakeInt.MI.func{1} None MakeInt.MI.func{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} (MakeInt.MI.func{1} ++ [change_pari])
       (MakeInt.MI.in_guard{1} `|` rest_adv_pis) m{2} => //.
call second; first auto.
inline{1} 1; sp 3 0.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
(* end of reduction to second *)
seq 0 1 :
  (r{2} = Some m1{1} /\ not_done0{1} /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None /\
   MakeInt.after_adv_to_func MI.func{1} r{2} /\
   ! (m1{1}.`1 = Adv /\ MI.func{2} <= m1{1}.`2.`1) /\
   (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = CompGlobs.mrfc_self{1} \/
    m1{1}.`1 = Adv /\
    (m1{1}.`2.`1 = CompGlobs.mrfc_self{1} \/
     addr_ge_param rf_info CompGlobs.mrfc_self{1} m1{1}.`2.`1 \/
     addr_eq_subfun rf_info CompGlobs.mrfc_self{1} m1{1}.`2.`1))).
exlim r{2} => r'.
call{2} (MakeInt.MI_after_adv_to_env Par Adv r').
auto; smt(inc_extl oget_some).
rcondf{2} 1; first auto. rcondt{2} 1; first auto.
rcondf{2} 2; first auto; smt().
sp 0 1.
seq 0 1 :
  (m1{1} = m{2} /\ not_done0{1} /\ not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None /\
   MakeInt.after_adv_to_func MI.func{1} (Some m{2}) /\
   ! (m1{1}.`1 = Adv /\ MI.func{2} <= m1{1}.`2.`1) /\
   (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = CompGlobs.mrfc_self{1} \/
    m1{1}.`1 = Adv /\
    (m1{1}.`2.`1 = CompGlobs.mrfc_self{1} \/
     addr_ge_param rf_info CompGlobs.mrfc_self{1} m1{1}.`2.`1 \/
     addr_eq_subfun rf_info CompGlobs.mrfc_self{1} m1{1}.`2.`1))).
exlim r{2} => r'.
call{2}
  (CompEnvMakeInt.MI_after_adv_to_func (MakeRFComp(Rest, CompEnvStubPar))
   CompEnvStubAdv r').
auto; smt(inc_extl).
rcondt{2} 1; first auto.
rcondt{2} 1; first auto; smt(oget_some).
inline{2} 1; sp 0 2.
rcondt{2} 1; first auto.
inline{2} 1. sp 0 3; wp.
(* start of reduction to first *)
conseq
  (_ :
   ={m1} /\ not_done0{1} /\ not_done0{2} /\
   (m1{1}.`2.`1 = CompGlobs.mrfc_self{1} \/
    addr_eq_subfun rf_info CompGlobs.mrfc_self{1} m1{1}.`2.`1 \/
    (m1{1}.`1 = Dir /\
     addr_eq_param_rest rf_info CompGlobs.mrfc_self{1} m1{1}.`2.`1) \/
    (m1{1}.`1 = Adv /\
     addr_ge_param_rest rf_info CompGlobs.mrfc_self{1} m1{1}.`2.`1) \/
    (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = MI.func{2} /\
     envport MI.func{2} m1{1}.`3)) /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   _); first smt().
transitivity{1}
  {r <@ LeftMFRC.f(m1);}
  (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={m1} /\ not_done0{1} ==>
   ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={r})
  (={m1} /\ not_done0{2} /\
   (m1{1}.`2.`1 = CompGlobs.mrfc_self{1} \/
    addr_eq_subfun rf_info CompGlobs.mrfc_self{1} m1{1}.`2.`1 \/
    (m1{1}.`1 = Dir /\
     addr_eq_param_rest rf_info CompGlobs.mrfc_self{1} m1{1}.`2.`1) \/
    (m1{1}.`1 = Adv /\
     addr_ge_param_rest rf_info CompGlobs.mrfc_self{1} m1{1}.`2.`1) \/
    (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = MI.func{2} /\
     envport MI.func{2} m1{1}.`3)) /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={glob Adv, glob Rest, glob Par} /\ ={r} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None) => //.
progress.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       CompGlobs.ce_func{1} CompGlobs.ce_stub_st{1}
       MakeInt.MI.func{1} CompEnvMakeInt.MI.func{1}
       CompEnvMakeInt.MI.in_guard{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} m1{2} => //.
inline{2} 1; sp 0 3.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
transitivity{2}
  {r <@ RightMFRC.f(m1);}
  (={m1} /\
   (m1{1}.`2.`1 = CompGlobs.mrfc_self{1} \/
    addr_eq_subfun rf_info CompGlobs.mrfc_self{1} m1{1}.`2.`1 \/
    (m1{1}.`1 = Dir /\
     addr_eq_param_rest rf_info CompGlobs.mrfc_self{1} m1{1}.`2.`1) \/
    (m1{1}.`1 = Adv /\
     addr_ge_param_rest rf_info CompGlobs.mrfc_self{1} m1{1}.`2.`1) \/
    (m1{1}.`1 = Dir /\ m1{1}.`2.`1 = MI.func{2} /\
     envport MI.func{2} m1{1}.`3)) /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={r} /\ ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None)
   (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
    not_done0{2} /\ ={m1} ==>
    ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
    ={r}) => //.
progress.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       MakeInt.MI.func{1} None MakeInt.MI.func{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} (MakeInt.MI.func{1} ++ [change_pari])
       (MakeInt.MI.in_guard{1} `|` rest_adv_pis) m1{2} => //.
call first; first auto.
inline{1} 1; sp 3 0.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
(* end of reduction to first *)
sp 1 0; elim* => r0_L.
seq 1 0 :
  (r{1} = None /\ !not_done{1} /\ r{2} <> None /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None /\
   MakeInt.after_adv_to_func MI.func{1} r{2} /\
   (MakeInt.after_adv_to_func MI.func{2} r{2} \/
    MakeInt.after_adv_to_env MI.func{2} r{2}) /\
   ! ((oget r{2}).`1 = Dir /\ (oget r{2}).`2.`1 = CompGlobs.mrfc_self{1} \/
      (oget r{2}).`1 = Adv /\
      ((oget r{2}).`2.`1 = CompGlobs.mrfc_self{1} \/
       addr_ge_param rf_info CompGlobs.mrfc_self{1} (oget r{2}).`2.`1 \/
       addr_eq_subfun rf_info CompGlobs.mrfc_self{1} (oget r{2}).`2.`1))).
call{1} (MakeInt.MI_after_func_error (MakeRFComp(Rest, Par)) Adv).
auto; smt(inc_extl).
rcondf{1} 1; first auto.
wp.
case (MakeInt.after_adv_to_func MI.func{2} r{2}).
exfalso; smt(after_adv_to_func_not_guard_contrad).
seq 0 1 :
  (r{1} = None /\ !not_done{1} /\ r{2} <> None /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None /\
   MakeInt.after_adv_to_func MI.func{1} r{2} /\
   ! ((oget r{2}).`1 = Dir /\ (oget r{2}).`2.`1 = CompGlobs.mrfc_self{1} \/
      (oget r{2}).`1 = Adv /\
      ((oget r{2}).`2.`1 = CompGlobs.mrfc_self{1} \/
       addr_ge_param rf_info CompGlobs.mrfc_self{1} (oget r{2}).`2.`1 \/
       addr_eq_subfun rf_info CompGlobs.mrfc_self{1} (oget r{2}).`2.`1))).
exlim r{2} => r'.
call{2} (MakeInt.MI_after_adv_to_env Par Adv r').
auto; smt(inc_extl).
rcondf{2} 1; first auto. rcondt{2} 1; first auto.
rcondf{2} 2; first auto; smt().
sp 0 1.
seq 0 1 :
  (r{1} = None /\ r{2} = Some m{2} /\ not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None /\
   MakeInt.after_adv_to_func MI.func{1} r{2} /\
   ! ((oget r{2}).`1 = Dir /\ (oget r{2}).`2.`1 = CompGlobs.mrfc_self{1} \/
      (oget r{2}).`1 = Adv /\
      ((oget r{2}).`2.`1 = CompGlobs.mrfc_self{1} \/
       addr_ge_param rf_info CompGlobs.mrfc_self{1} (oget r{2}).`2.`1 \/
       addr_eq_subfun rf_info CompGlobs.mrfc_self{1} (oget r{2}).`2.`1))).
exlim r{2} => r'.
call{2}
  (CompEnvMakeInt.MI_after_adv_to_func (MakeRFComp(Rest, CompEnvStubPar))
   CompEnvStubAdv r').
auto; smt(inc_extl).
rcondt{2} 1; first auto.
rcondt{2} 1; first auto; smt().
inline{2} 1; sp 0 2.
rcondf{2} 1; first auto.
sp 0 1.
seq 0 1 :
  (r{1} = None /\ r{2} = None /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{2}
  (CompEnvMakeInt.MI_after_func_error (MakeRFComp(Rest, CompEnvStubPar))
   CompEnvStubAdv).
auto; smt().
rcondf{2} 1; first auto.
auto.
seq 1 0 :
  (r{1} = None /\ !not_done{1} /\
   ={glob Adv, glob Rest, glob Par} /\
   MakeInt.after_adv_error MI.func{1} r{2} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{1} (MakeInt.MI_after_adv_error (MakeRFComp(Rest, Par)) Adv).
auto; smt().
rcondf{1} 1; first auto.
wp.
conseq
  (_ :
   r{1} = None /\ ={glob Adv, glob Rest, glob Par} /\
   MakeInt.after_adv_error MI.func{1} r{2} /\
   (MakeInt.after_adv_error MI.func{2} r{2} \/
    MakeInt.after_adv_to_env MI.func{2} r{2}) /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   _).
auto; smt(MakeInt.after_adv_error_ext_error_or_to_env).
case (MakeInt.after_adv_error MI.func{2} r{2}).
seq 0 1 :
  (r{1} = None /\ r{2} = None /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   MakeInt.after_adv_error MI.func{1} r{2} /\
   (MakeInt.after_adv_error MI.func{2} r{2} \/
    MakeInt.after_adv_to_env MI.func{2} r{2}) /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{2} (MakeInt.MI_after_adv_error Par Adv).
auto; smt(inc_extl).
rcondf{2} 1; first auto. rcondf{2} 1; first auto.
seq 0 1 :
  (r{1} = None /\ r{2} = None /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   MakeInt.after_adv_error MI.func{1} r{2} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{2}
  (CompEnvMakeInt.MI_after_adv_error (MakeRFComp(Rest, CompEnvStubPar))
   CompEnvStubAdv).
auto; smt().
rcondf{2} 1; first auto.
auto.
seq 0 1 :
  (r{1} = None /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   MakeInt.after_adv_error MI.func{1} r{2} /\
   MakeInt.after_adv_to_env MI.func{2} r{2} /\
   (MakeInt.after_adv_error MI.func{2} r{2} \/
    MakeInt.after_adv_to_env MI.func{2} r{2}) /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
exlim r{2} => r'.
call{2} (MakeInt.MI_after_adv_to_env Par Adv r').
auto; smt(inc_extl).
rcondf{2} 1; first auto.
rcondt{2} 1; first auto; smt().
rcondf{2} 2; first auto; smt().
sp 0 1.
seq 0 1 :
  (r{1} = None /\ r{2} = None /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{2}
  (CompEnvMakeInt.MI_after_adv_error (MakeRFComp(Rest, CompEnvStubPar))
   CompEnvStubAdv).
auto.
rcondf{2} 1; first auto; smt().
auto.
qed.

(* this lemma assumes the first and third equiv's from
   comp_bridge_induct with the same termination metric as the
   conclusion *)

local lemma LeftMI_RightMIFromPar
      (n : int, func': addr, in_guard_low': int fset) :
  exper_pre func' =>
  equiv
  [LeftMFRC.f ~ RightMFRC.f :
   ={m} /\
   (m{1}.`2.`1 = CompGlobs.mrfc_self{1} \/
    addr_eq_subfun rf_info CompGlobs.mrfc_self{1} m{1}.`2.`1 \/
    (m{1}.`1 = Dir /\
     addr_eq_param_rest rf_info CompGlobs.mrfc_self{1} m{1}.`2.`1) \/
    (m{1}.`1 = Adv /\
     addr_ge_param_rest rf_info CompGlobs.mrfc_self{1} m{1}.`2.`1) \/
    (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{2} /\ envport MI.func{2} m{1}.`3)) /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={res, glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None] =>
  equiv
  [LeftMFRC.f ~ RightMIFromPar.f :
   ={m} /\ m{1}.`1 = Adv /\ MI.func{2} <= m{1}.`2.`1 /\
   MI.func{2} <= m_orig{2}.`2.`1 /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={res, glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None] =>
  equiv
  [LeftMI.f ~ RightMIFromPar.f :
   ={m} /\ m{1}.`1 = Adv /\ m{1}.`2.`1 = adv /\
   MI.func{2} <= m_orig{2}.`2.`1 /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={res, glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None].
proof.
move => ep_func' first third.
proc => /=; sp 2 2.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
rcondf{1} 1; first auto; smt(inc_nle_l).
rcondf{2} 1; first auto; smt(inc_extl inc_nle_l).
seq 1 1 :
  (={r} /\ ={glob Adv, glob Rest, glob Par} /\
  MI.func{2} <= m_orig{2}.`2.`1 /\
  term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
  invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
  MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
  MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
  CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
  MI.func{2} = func' ++ [change_pari] /\
  CompEnvMI.in_guard{2} = in_guard_low' /\
  MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
  CompGlobs.ce_stub_st{2} = None).
call (_ : true); first auto.
case (MakeInt.after_adv_error MI.func{1} r{1}).
seq 1 0 :
  (r{1} = None /\ !not_done{1} /\
   MI.func{1} ++ [change_pari] <= m_orig{2}.`2.`1 /\
   MakeInt.after_adv_error MI.func{1} r{2} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{1} (MakeInt.MI_after_adv_error (MakeRFComp(Rest, Par)) Adv).
auto; smt().
rcondf{1} 1; auto.
case (MakeInt.after_adv_error MI.func{2} r{2}).
seq 0 1 :
  (r{1} = None /\ r{2} = None /\ !not_done{2} /\
   MI.func{1} ++ [change_pari] <= m_orig{2}.`2.`1 /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{2} (MakeInt.MI_after_adv_error Par Adv).
auto; smt(inc_extl).
rcondf{2} 1; first auto. rcondf{2} 1; first auto.
seq 0 1 :
  (r{1} = None /\ r{2} = None /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{2}
  (MakeRFComp_after_par_or_rest_error
   Rest CompEnvStubPar); first auto; smt().
rcondf{2} 1; first auto.
seq 0 1 :
  (r{1} = None /\ r{2} = None /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{2}
  (CompEnvMakeInt.MI_after_func_error
   (MakeRFComp(Rest, CompEnvStubPar)) CompEnvStubAdv).
auto.
rcondf{2} 1; first auto.
auto.
exlim r{2} => r2'.
seq 0 1 :
  (r{1} = None /\ r{2} = Some m{2} /\ !not_done{2} /\
   MakeInt.MI.func{1} ++ [change_pari] <= m_orig{2}.`2.`1 /\
   MakeInt.after_adv_error MakeInt.MI.func{1} r{2} /\
   ! MakeInt.after_adv_error MI.func{2} r{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{2} (MakeInt.MI_after_adv_to_env Par Adv r2').
auto;
  smt(inc_extl
      MakeInt.after_adv_error_ext_error_or_to_env).
rcondf{2} 1; first auto. rcondt{2} 1; first auto.
rcondt{2} 2; first auto; smt().
sp 0 3; elim* => r_R ce_stub_st_R m_R.
seq 0 1 :
  (r{1} = None /\ r{2} = Some m{2} /\ !not_done{2} /\
   m{2} = dummy_msg_to_stub_adv MI.func{1} /\
   MakeInt.after_adv_error MakeInt.MI.func{1} (Some m_R) /\
   CompGlobs.ce_stub_st{2} = Some m_R /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis).
exlim r{2} => r2''.
call{2}
  (MakeRFComp_after_par_or_rest_return
   Rest CompEnvStubPar r2'').
auto => |> &2 _ dst_ge_par aae_top not_aae_bot _ _.
split => [| /#].
apply after_par_or_rest_return_intro_adv_from_param.
trivial.
by rewrite oget_some /dummy_msg_to_stub_adv.
by rewrite oget_some /dummy_msg_to_stub_adv.
by rewrite oget_some /dummy_msg_to_stub_adv.
rewrite oget_some /dummy_msg_to_stub_adv /=.
smt(le_refl rf_info_valid change_pari_valid).
rewrite oget_some /dummy_msg_to_stub_adv /=.
rewrite
  (next_of_addr_ge_self_plus func' (func' ++ [change_pari])
   change_pari) 1:le_refl //.
rcondf{2} 1; first auto.
seq 0 1 :
  (r{1} = None /\ r{2} = Some m{2} /\ not_done{2} /\
   m{2} = dummy_msg_to_stub_adv MI.func{1} /\
   MakeInt.after_adv_error MakeInt.MI.func{1} (Some m_R) /\
   CompGlobs.ce_stub_st{2} = Some m_R /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis).
exlim r{2} => r'.
call{2}
  (CompEnvMakeInt.MI_after_func_to_adv
   (MakeRFComp(Rest, CompEnvStubPar)) CompEnvStubAdv r').
auto; progress [-delta]; smt(inc_extl).
rcondt{2} 1; first auto.
rcondf{2} 1; first auto; smt(inc_nle_l).
inline{2} 1.
rcondt{2} 2; first auto.
sp 0 4.
seq 0 1 :
  (r{1} = None /\ r{2} = None /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{2}
  (CompEnvMakeInt.MI_after_adv_error
   (MakeRFComp(Rest, CompEnvStubPar)) CompEnvStubAdv).
auto.
rcondf{2} 1; first auto.
auto.
case (MakeInt.after_adv_to_func MI.func{1} r{1}).
seq 1 0 :
  (={r} /\ r{1} = Some m{1} /\ not_done{1} /\
   MI.func{1} ++ [change_pari] <= m_orig{2}.`2.`1 /\
   MakeInt.after_adv_to_func MI.func{1} r{1} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
exlim r{1} => r'.
call{1} (MakeInt.MI_after_adv_to_func (MakeRFComp(Rest, Par)) Adv r').
auto.
rcondt{1} 1; first auto.
rcondt{1} 1; first auto; smt(oget_some).
inline{1} 1.
case (MakeInt.after_adv_to_func MI.func{2} r{2}).
sp 2 0.
rcondt{1} 1; first auto; progress [-delta].
right; split; [smt() | smt(rf_info_valid change_pari_valid)].
inline{1} 1.
sp 3 0.
seq 0 1 :
  (not_done0{1} /\ m1{1} = m{2} /\
   r{2} = Some m{2} /\ not_done{2} /\
   MI.func{1} ++ [change_pari] <= m_orig{2}.`2.`1 /\
   MakeInt.after_adv_to_func MI.func{2} r{2} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
exlim r{2} => r2'.
call{2} (MakeInt.MI_after_adv_to_func Par Adv r2').
auto; smt(inc_extl).
conseq
  (_ :
   m1{1} = m{2} /\ not_done0{1} /\ not_done{2} /\
   m1{1}.`1 = Adv /\ MI.func{2} <= m1{1}.`2.`1 /\
   MI.func{1} ++ [change_pari] <= m_orig{2}.`2.`1 /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   _); first progress; smt().
(* beginning of reduction third *)
transitivity{1}
  {r <@ LeftMFRC.f(m1);}
  (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={m1} /\ not_done0{1} ==>
   ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={r})
  (m1{1} = m{2} /\ not_done{2} /\
   m1{1}.`1 = Adv /\ MI.func{2} <= m1{1}.`2.`1 /\
   MI.func{1} ++ [change_pari] <= m_orig{2}.`2.`1 /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={glob Adv, glob Rest, glob Par} /\ ={r} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None) => //.
progress.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       CompGlobs.ce_func{1} CompGlobs.ce_stub_st{1}
       MakeInt.MI.func{1} CompEnvMakeInt.MI.func{1}
       CompEnvMakeInt.MI.in_guard{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} m{2} => //.
inline{2} 1; sp 0 3.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
transitivity{2}
  {r <@ RightMIFromPar.f(m, m_orig);}
  (m1{1} = m{2} /\
   m1{1}.`1 = Adv /\ MI.func{2} <= m1{1}.`2.`1 /\
   MI.func{1} ++ [change_pari] <= m_orig{2}.`2.`1 /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={r} /\ ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None)
  (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   not_done{2} /\ ={m, m_orig} ==>
   ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={r}); progress.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       MakeInt.MI.func{1} None MakeInt.MI.func{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} (MakeInt.MI.func{1} ++ [change_pari])
       (MakeInt.MI.in_guard{1} `|` rest_adv_pis) m{2} m_orig{2} => //.
exlim (term_rest (glob Rest){1} + term_par (glob Par){1}) => tm.
call third; first auto.
inline{1} 1; sp 4 0.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
(* end of reduction to third conjunct of IH *)
sp 2 0.
seq 0 1 :
  (r0{1} = None /\ m0{1} = m{2} /\
   r{2} = Some m{2} /\ !not_done{2} /\
   MI.func{1} ++ [change_pari] <= m_orig{2}.`2.`1 /\
   MakeInt.after_adv_to_func MI.func{1} r{2} /\
   MakeInt.after_adv_to_env MI.func{2} r{2} /\
   ! MakeInt.after_adv_to_func MI.func{2} r{2} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
exlim r{2} => r2'.
call{2} (MakeInt.MI_after_adv_to_env Par Adv r2').
auto;
  smt(inc_extl
      MakeInt.after_adv_to_func_ext_to_func_or_env).
rcondf{2} 1; first auto. rcondt{2} 1; first auto.
rcondt{2} 2; first auto; smt().
sp 0 3; elim* => r_R ce_stub_st_R m_R.
seq 0 1 :
  (r0{1} = None /\ r{2} = Some m{2} /\ !not_done{2} /\
   m{2} = dummy_msg_to_stub_adv MI.func{1} /\
   CompGlobs.ce_stub_st{2} = Some m0{1} /\
   MakeInt.after_adv_to_func MI.func{1} (Some m0{1}) /\
   ! MakeInt.after_adv_to_func MI.func{2} (Some m0{1}) /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis).
exlim r{2} => r2''.
call{2}
  (MakeRFComp_after_par_or_rest_return
   Rest CompEnvStubPar r2'').
auto; progress [-delta].
apply after_par_or_rest_return_intro_adv_from_param.
trivial.
by rewrite oget_some /dummy_msg_to_stub_adv.
by rewrite oget_some /dummy_msg_to_stub_adv.
by rewrite oget_some /dummy_msg_to_stub_adv.
rewrite oget_some /dummy_msg_to_stub_adv /=.
smt(le_refl rf_info_valid change_pari_valid).
rewrite oget_some /dummy_msg_to_stub_adv /=.
rewrite
  (next_of_addr_ge_self_plus MakeInt.MI.func{1}
   (MakeInt.MI.func{1} ++ [change_pari])
   change_pari) 1:le_refl //.
smt().
rcondf{2} 1; first auto.
seq 0 1 :
  (r0{1} = None /\ r{2} = Some m{2} /\ not_done{2} /\
   m{2} = dummy_msg_to_stub_adv MI.func{1} /\
   CompGlobs.ce_stub_st{2} = Some m0{1} /\
   MakeInt.after_adv_to_func MI.func{1} (Some m0{1}) /\
   ! MakeInt.after_adv_to_func MI.func{2} (Some m0{1}) /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\  CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\  CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis).
exlim r{2} => r'.
call{2}
  (CompEnvMakeInt.MI_after_func_to_adv
   (MakeRFComp(Rest, CompEnvStubPar)) CompEnvStubAdv r').
auto; progress; smt().
rcondt{2} 1; first auto.
rcondf{2} 1; first auto; smt(inc_nle_l).
inline{2} 1.
rcondt{2} 2; first auto.
sp 0 4; elim* => r_R0.
seq 0 1 :
  (r0{1} = None /\ r{2} = Some m{2} /\ m{2} = m0{1} /\ not_done{2} /\
   MakeInt.after_adv_to_func MI.func{1} (Some m0{1}) /\
   ! MakeInt.after_adv_to_func MI.func{2} (Some m0{1}) /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\  CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\  CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
exlim r{2} => r'.
call{2}
  (CompEnvMakeInt.MI_after_adv_to_func
   (MakeRFComp(Rest, CompEnvStubPar)) CompEnvStubAdv r').
auto; smt(inc_extl).
rcondt{2} 1; first auto.
rcondt{2} 1; first auto; smt(oget_some).
inline{2} 1; sp 0 2.
if => //.
inline{1} 1; inline{2} 1; sp 3 3.
conseq
  (_ :
   not_done0{1} /\ not_done0{2} /\ m1{1} = m2{2} /\
   m1{1}.`1 = Adv /\
   (m1{1}.`2.`1 = CompGlobs.mrfc_self{1} \/
    addr_eq_subfun rf_info CompGlobs.mrfc_self{1} m1{1}.`2.`1 \/
    addr_ge_param_rest rf_info CompGlobs.mrfc_self{1} m1{1}.`2.`1) /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\  CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\  CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   _) => //.
progress [-delta]; smt().
(* beginning of reduction to first *)
transitivity{1}
  {r <@ LeftMFRC.f(m1);}
  (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={m1} /\ not_done0{1} ==>
   ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={r})
  (m1{1} = m2{2} /\ not_done0{2} /\
   m1{1}.`1 = Adv /\
   (m1{1}.`2.`1 = CompGlobs.mrfc_self{1} \/
    addr_eq_subfun rf_info CompGlobs.mrfc_self{1} m1{1}.`2.`1 \/
    addr_ge_param_rest rf_info CompGlobs.mrfc_self{1} m1{1}.`2.`1) /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={glob Adv, glob Rest, glob Par} /\ ={r} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None) => //.
progress.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       CompGlobs.ce_func{1} CompGlobs.ce_stub_st{1}
       MakeInt.MI.func{1} CompEnvMakeInt.MI.func{1}
       CompEnvMakeInt.MI.in_guard{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} m2{2} => //.
inline{2} 1; sp 0 3.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
transitivity{2}
  {r <@ RightMFRC.f(m2);}
  (m1{1} = m2{2} /\ m1{1}.`1 = Adv /\
   (m1{1}.`2.`1 = CompGlobs.mrfc_self{1} \/
    addr_eq_subfun rf_info CompGlobs.mrfc_self{1} m1{1}.`2.`1 \/
    addr_ge_param_rest rf_info CompGlobs.mrfc_self{1} m1{1}.`2.`1) /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={r} /\ ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None)
  (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={m2} /\ not_done0{2} ==>
   ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={r}) => //.
progress.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       MakeInt.MI.func{1} None MakeInt.MI.func{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} (MakeInt.MI.func{1} ++ [change_pari])
       (MakeInt.MI.in_guard{1} `|` rest_adv_pis) m2{2} => //.
call first; first auto; smt().
inline{1} 1; sp 3 0.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
(* end of reduction to first conjunct of IH *)
sp 1 1; elim* => r_R1.
seq 1 1 :
  (r{1} = None /\ r{2} = None /\ !not_done{1} /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\  CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\  CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{1} (MakeInt.MI_after_func_error (MakeRFComp(Rest, Par)) Adv).
call{2}
  (CompEnvMakeInt.MI_after_func_error
   (MakeRFComp(Rest, CompEnvStubPar)) CompEnvStubAdv).
auto.
rcondf{1} 1; first auto. rcondf{2} 1; first auto.
auto.
seq 1 1 :
  (={r, m} /\ r{1} = Some m{1} /\ !not_done{1} /\ !not_done{2} /\
   MakeInt.after_adv_to_env MI.func{1} r{1} /\
   MI.func{1} ++ [change_pari] <= m_orig{2}.`2.`1 /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\  CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\  CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
exlim r{1} => r'.
call{1}
  (MakeInt.MI_after_adv_to_env (MakeRFComp(Rest, Par)) Adv r').
call{2} (MakeInt.MI_after_adv_to_env Par Adv r').
auto; smt(inc_extl MakeInt.after_adv_to_env_ext).
rcondf{1} 1; first auto. rcondf{2} 1; first auto.
rcondt{2} 1; first auto. rcondt{2} 2; first auto; smt().
sp 0 3; elim* => r_R ce_stub_st_R m_R.
seq 0 1 :
  (r{1} = Some m{1} /\ r{2} = Some m{2} /\ !not_done{2} /\
   m{2} = dummy_msg_to_stub_adv MI.func{1} /\
   CompGlobs.ce_stub_st{2} = Some m{1} /\
   MakeInt.after_adv_to_env MI.func{1} r{1} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis).
exlim r{2} => r2''.
call{2}
  (MakeRFComp_after_par_or_rest_return
   Rest CompEnvStubPar r2'').
auto; progress [-delta].
apply after_par_or_rest_return_intro_adv_from_param.
trivial.
by rewrite oget_some /dummy_msg_to_stub_adv.
by rewrite oget_some /dummy_msg_to_stub_adv.
by rewrite oget_some /dummy_msg_to_stub_adv.
rewrite oget_some /dummy_msg_to_stub_adv /=.
smt(le_refl rf_info_valid change_pari_valid).
rewrite oget_some /dummy_msg_to_stub_adv /=.
rewrite
  (next_of_addr_ge_self_plus MakeInt.MI.func{1}
   (MakeInt.MI.func{1} ++ [change_pari]) change_pari) 1:le_refl //.
smt().
rcondf{2} 1; first auto.
seq 0 1 :
  (r{1} = Some m{1} /\ r{2} = Some m{2} /\ not_done{2} /\
   m{2} = dummy_msg_to_stub_adv MI.func{1} /\
   CompGlobs.ce_stub_st{2} = Some m{1} /\
   MakeInt.after_adv_to_env MI.func{1} r{1} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\  CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\  CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis).
exlim r{2} => r'.
call{2}
  (CompEnvMakeInt.MI_after_func_to_adv
   (MakeRFComp(Rest, CompEnvStubPar)) CompEnvStubAdv r').
auto; progress; smt().
rcondt{2} 1; first auto.
rcondf{2} 1; first auto; progress; smt(inc_nle_l).
inline{2} 1.
rcondt{2} 2; first auto.
sp 0 4.
exlim r{1} => r'.
seq 0 1 :
  (={r} /\ r{1} = Some m{1} /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\  CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\  CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{2}
  (CompEnvMakeInt.MI_after_adv_to_env
   (MakeRFComp(Rest, CompEnvStubPar)) CompEnvStubAdv r').
auto; smt().
rcondf{2} 1; first auto.
auto.
qed.

(* the main strong induction on the sum of the termination metrics of
   Rest and Par of the conjunction of three mutually recursive equivs *)

local lemma comp_bridge_induct
      (func' : addr, in_guard_low' : int fset) :
  exper_pre func' => disjoint in_guard_low' rest_adv_pis =>
  forall (n : int),
  equiv
  [LeftMFRC.f ~ RightMFRC.f :
   ={m} /\
   (m{1}.`2.`1 = CompGlobs.mrfc_self{1} \/
    addr_eq_subfun rf_info CompGlobs.mrfc_self{1} m{1}.`2.`1 \/
    (m{1}.`1 = Dir /\
     addr_eq_param_rest rf_info CompGlobs.mrfc_self{1} m{1}.`2.`1) \/
    (m{1}.`1 = Adv /\
     addr_ge_param_rest rf_info CompGlobs.mrfc_self{1} m{1}.`2.`1) \/
    (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{2} /\ envport MI.func{2} m{1}.`3)) /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={res, glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None] /\
  equiv
  [LeftMFRC.f ~ RightMIFromAdv.f :
   ={m} /\ m{1}.`1 = Adv /\ MI.func{2} <= m{1}.`2.`1 /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={res, glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None] /\
  equiv
  [LeftMFRC.f ~ RightMIFromPar.f :
   ={m} /\ m{1}.`1 = Adv /\ MI.func{2} <= m{1}.`2.`1 /\
   MI.func{2} <= m_orig{2}.`2.`1 /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} = n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={res, glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None].
proof.
move => ep_func' disj_igl'_rest_adv_pis n.
case (n < 0) => [lt0_n | ge0_n].
split; first exfalso; smt(ge0_term_rest ge0_term_par).
split; first exfalso; smt(ge0_term_rest ge0_term_par).
exfalso; smt(ge0_term_rest ge0_term_par).
rewrite -lezNgt in ge0_n.
move : n ge0_n.
elim /Int.sintind => n ge0_n IH.
split.
(* start of first equiv: LeftMFRC.f ~ RightMFRC.f *)
proc.
sp 2 2. rcondt{1} 1; first auto. rcondt{2} 1; first auto.
if => //.
inline{2} 1.
rcondf{2} 2; first auto.
inline{2} 2; sp 0 2.
rcondt{2} 1; first auto.
smt(le_pre le_cons not_le_other_branch not_le_ext_nonnil_l
    rf_info_valid change_pari_valid).
inline{2} 1.
rcondt{2} 4; first auto.
rcondt{2} 4; first auto.
sp 0 3.
seq 1 1 :
  (r{1} = r2{2} /\ ={glob Adv, glob Rest, glob Par} /\
   CompGlobs.mrfc_self{1} ++ [change_pari] <= m{1}.`2.`1 /\
   CompGlobs.mrfc_self{1} ++ [change_pari] <= m{2}.`2.`1 /\
   (r{1} = None \/
    term_rest (glob Rest){1} + term_par (glob Par){1} < n) /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
exlim (term_par (glob Par){1}) => tp.
call (Par_invoke tp).
auto; smt().
case (r{1} = None).
seq 1 1 :
  (r{1} = r2{2} /\ r{1} = None /\ !not_done{1} /\ !not_done0{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{1} (MakeRFComp_after_par_or_rest_error Rest Par).
call{2} (MakeInt.MI_after_func_error Par Adv).
auto; smt(inc_extl).
rcondf{1} 1; first auto. rcondf{2} 1; first auto.
sp 0 2.
rcondf{2} 1; first auto; smt().
sp 0 1.
seq 1 1 :
  (={r} /\ r{1} = None /\ !not_done{1} /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{1}
  (MakeInt.MI_after_func_error (MakeRFComp(Rest, Par)) Adv).
call{2} (MakeRFComp_after_par_or_rest_error Rest CompEnvStubPar).
auto; smt().
rcondf{1} 1; first auto. rcondf{2} 1; first auto.
seq 1 1 :
  (={r} /\ !not_done{1} /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{2}
  (CompEnvMakeInt.MI_after_func_error (MakeRFComp(Rest, CompEnvStubPar))
   CompEnvStubAdv).
auto; smt(inc_extl).
rcondf{2} 1; first auto.
auto.
conseq
  (_ :
   r{1} = r2{2} /\
   CompGlobs.mrfc_self{1} ++ [change_pari] <= m{1}.`2.`1 /\
   CompGlobs.mrfc_self{1} ++ [change_pari] <= m{2}.`2.`1 /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   _); first smt().
case (MakeInt.after_func_error MI.func{2} r2{2}).
seq 1 1 :
  (r{1} = None /\ r2{2} = None /\ !not_done{1} /\ !not_done0{2} /\
  ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{1} (MakeRFComp_after_par_or_rest_error Rest Par).
call{2} (MakeInt.MI_after_func_error Par Adv).
auto;
  smt(inc_extl
      after_func_error_ch_pari_implies_after_par_or_rest_error).
rcondf{1} 1; first auto. rcondf{2} 1; first auto.
rcondf{2} 3; first auto.
sp 0 3.
seq 1 1 :
  (r{1} = None /\ r{2} = None /\ !not_done{1} /\ !not_done{2} /\
  ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{1} (MakeInt.MI_after_func_error (MakeRFComp(Rest, Par)) Adv).
call{2} (MakeRFComp_after_par_or_rest_error Rest CompEnvStubPar).
auto.
rcondf{1} 1; first auto. rcondf{2} 1; first auto.
seq 0 1 :
  (r{1} = None /\ r{2} = None /\ !not_done{1} /\ !not_done{2} /\
  ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{2}
  (CompEnvMakeInt.MI_after_func_error
   (MakeRFComp(Rest, CompEnvStubPar)) CompEnvStubAdv); first auto.
rcondf{2} 1; first auto.
auto.
case (MakeInt.after_func_to_adv MI.func{2} r2{2}).
seq 1 1 :
  (r{1} = r2{2} /\ m{1} = m2{2} /\ r{1} = Some m{1} /\
   ! not_done{1} /\ not_done0{2} /\
   CompGlobs.mrfc_self{1} ++ [change_pari] <= m{2}.`2.`1 /\
   MakeInt.after_func_to_adv MI.func{2} r2{2} /\
   ! (MakeInt.after_func_error MI.func{2} r2{2}) /\
   m{1}.`1 = Adv /\ m{1}.`2.`1 = adv /\
   0 < m{1}.`2.`2 /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
exlim r{1} => r1.
call{1} (MakeRFComp_after_par_or_rest_return Rest Par r1).
call{2} (MakeInt.MI_after_func_to_adv Par Adv r1).
auto; progress [-delta];
  smt(inc_extl oget_some
      after_func_to_adv_ch_pari_implies_after_par_or_rest_return_and_adv).
rcondf{1} 1; first auto.
seq 1 0 :
  (r{1} = r2{2} /\ m{1} = m2{2} /\ r{1} = Some m{1} /\
   not_done{1} /\ not_done0{2} /\
   MakeInt.after_func_to_adv MI.func{2} r2{2} /\
   ! MakeInt.after_func_error MI.func{2} r2{2} /\
   m{1}.`1 = Adv /\ m{1}.`2.`1 = adv /\
   0 < m{1}.`2.`2 /\
   MI.func{1} ++ [change_pari] <= m{2}.`2.`1 /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
exlim r{1} => r1.
call{1}
  (MakeInt.MI_after_func_to_adv (MakeRFComp(Rest, Par)) Adv r1).
auto; smt(inc_extl le_trans le_ext_r).
conseq
  (_ :
   m{1} = m2{2} /\ not_done{1} /\ not_done0{2} /\
   m{1}.`1 = Adv /\ m{1}.`2.`1 = adv /\
   MI.func{1} ++ [change_pari] <= m{2}.`2.`1 /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   _) => //.
(* start of reduction to LeftMI_RightMIFromPar *)
transitivity{1}
  {r <@ LeftMI.f(m);}
  (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={m} /\ not_done{1} ==>
   ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={r})
  (m{1} = m2{2} /\ not_done0{2} /\
   m{1}.`1 = Adv /\ m{1}.`2.`1 = adv /\
   MI.func{1} ++ [change_pari] <= m{2}.`2.`1 /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={glob Adv, glob Rest, glob Par} /\ ={r} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None) => //.
progress.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       CompGlobs.ce_func{1} CompGlobs.ce_stub_st{1}
       MakeInt.MI.func{1} CompEnvMakeInt.MI.func{1}
       CompEnvMakeInt.MI.in_guard{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} m2{2} => //.
inline{2} 1; sp 0 3.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
transitivity{2}
  {r <@ RightMIFromPar.f(m2, m);}
  (m{1} = m2{2} /\ MI.func{1} ++ [change_pari] <= m{2}.`2.`1 /\
   m{1}.`1 = Adv /\ m{1}.`2.`1 = adv /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={r} /\ ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None)
   (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
    not_done0{2} /\ ={m2, m} ==>
    ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
    ={r}) => //.
progress.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       MakeInt.MI.func{1} None MakeInt.MI.func{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} (MakeInt.MI.func{1} ++ [change_pari])
       (MakeInt.MI.in_guard{1} `|` rest_adv_pis) m{2} m2{2} => //.
exlim (term_rest (glob Rest){1} + term_par (glob Par){1}) => tm.
case @[ambient] (0 <= tm < n) => [tm_ok | tm_not_ok].
call (LeftMI_RightMIFromPar tm func' in_guard_low').
have [#] first _ _ := IH tm _ => //.
have [#] _ _ third := IH tm _ => //.
auto.
exfalso; smt(ge0_term_rest ge0_term_par).
inline{1} 1; sp 4 0.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
(* end of reduction to LeftMI_RightMIFromPar *)
exlim r2{2} => r2'.
seq 0 1 :
  (r{1} = r2{2} /\ r2{2} = Some m2{2} /\
   !not_done0{2} /\
   CompGlobs.mrfc_self{1} ++ [change_pari] <= m{1}.`2.`1 /\
   CompGlobs.mrfc_self{1} ++ [change_pari] <= m{2}.`2.`1 /\
   MakeInt.after_func_to_env MI.func{2} r2{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{2} (MakeInt.MI_after_func_to_env Par Adv r2').
auto; smt(inc_extl MakeInt.after_func_disj).
rcondf{2} 1; first auto.
rcondt{2} 3; first auto.
rcondf{2} 4; first auto; smt().
sp 0 4.
case (after_par_or_rest_error MI.func{1} r{1} m{1}.`2.`1).
seq 1 1 :
  (r{1} = None /\ r{2} = None /\ !not_done{1} /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{1} (MakeRFComp_after_par_or_rest_error Rest Par).
call{2} (MakeRFComp_after_par_or_rest_error Rest CompEnvStubPar).
auto; smt(pari_cond_after_par_or_rest_error_equiv).
rcondf{1} 1; first auto.
seq 1 0 :
  (r{1} = None /\ r{2} = None /\ !not_done{1} /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{1} (MakeInt.MI_after_func_error (MakeRFComp(Rest, Par)) Adv).
auto.
rcondf{1} 1; first auto.
rcondf{2} 1; first auto.
seq 0 1 :
  (r{1} = None /\ r{2} = None /\ !not_done{1} /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{2}
  (CompEnvMakeInt.MI_after_func_error
   (MakeRFComp(Rest, CompEnvStubPar)) CompEnvStubAdv).
auto.
rcondf{2} 1; first auto.
auto.
exlim m{1}.`2.`1 => oda.
seq 1 1 :
  (={r, m} /\ r{1} = Some m{1} /\ not_done{1} /\ not_done{2} /\
   CompGlobs.mrfc_self{1} ++ [change_pari] <= oda /\
   after_par_or_rest_continue MI.func{1} r{1} oda /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
exlim r{1} => r'.
call{1} (MakeRFComp_after_par_or_rest_continue Rest Par r').
call{2} (MakeRFComp_after_par_or_rest_continue Rest CompEnvStubPar r').
auto; 
  smt(after_func_to_env_ch_pari_implies_after_par_or_rest_cont_or_error
      pari_cond_after_par_or_rest_error_equiv).
conseq
  (_ :
   ={r, m} /\ r{1} = Some m{1} /\ not_done{1} /\ not_done{2} /\
   m{1}.`2.`1 = MI.func{1} /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   _).
progress [-delta].
have :=
  after_par_or_rest_continue_from_change_pari MI.func{1}
  (Some m{2}) oda _ _ => //.
(* beginning of reduction to first conjunct of IH *)
transitivity{1}
  {r <@ LeftMFRC.f(m);}
  (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={m} /\ not_done{1} ==>
   ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={r})
  (={m} /\ not_done{2} /\ m{1}.`2.`1 = MI.func{1} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={glob Adv, glob Rest, glob Par} /\ ={r} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None) => //.
move => &1 &2 [#] -> -> H1 -> -> H2 -> -> ->; progress.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       CompGlobs.ce_func{1} CompGlobs.ce_stub_st{1}
       MakeInt.MI.func{1} CompEnvMakeInt.MI.func{1}
       CompEnvMakeInt.MI.in_guard{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} m{2}; smt().
inline{2} 1; sp 0 3.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
transitivity{2}
  {r <@ RightMFRC.f(m);}
  (={m} /\ not_done{2} /\ m{1}.`2.`1 = MI.func{1} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={r} /\ ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None)
  (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   not_done{2} /\ ={m} ==>
   ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={r}) => //.
move =>
  &1 &2 [#] -> H0 H1 -> -> -> H2 H3 H4 H5 H6 H7 H8 H9 H10
  H11 H12 H13 H14.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       MakeInt.MI.func{1} None MakeInt.MI.func{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} (MakeInt.MI.func{1} ++ [change_pari])
       (MakeInt.MI.in_guard{1} `|` rest_adv_pis) m{2} not_done{2}; smt().
exlim (term_rest (glob Rest){1} + term_par (glob Par){1}) => tm.
case @[ambient] (0 <= tm < n) => [tm_ok | tm_not_ok].
have [#] first _ _ := IH tm _ => //.
call first; first auto; smt().
exfalso; smt(ge0_term_rest ge0_term_par).
inline{1} 1; sp 3 0.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
(* end of reduction to first conjunct of IH *)
seq 1 1 :
  (={r, m} /\ ={glob Adv, glob Rest, glob Par} /\
   ! MI.func{1} ++ [change_pari] <= m{1}.`2.`1 /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   (r{1} = None \/
    (term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
     ((oget r{1}).`1 = Adv =>
      (oget r{1}).`2.`2 \in rest_adv_pis))) /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
exlim (term_rest (glob Rest){1}) => tp.
call (Rest_invoke tp); first auto; smt().
case (r{1} = None).
seq 1 1 :
  (r{1} = None /\ r{2} = None /\ !not_done{1} /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{1} (MakeRFComp_after_par_or_rest_error Rest Par).
call{2} (MakeRFComp_after_par_or_rest_error Rest CompEnvStubPar).
auto.
rcondf{1} 1; first auto. rcondf{2} 1; first auto. 
seq 1 1 :
  (r{1} = None /\ r{2} = None /\ !not_done{1} /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{1}
  (MakeInt.MI_after_func_error (MakeRFComp(Rest, Par)) Adv).
call{2}
  (CompEnvMakeInt.MI_after_func_error
   (MakeRFComp(Rest, CompEnvStubPar)) CompEnvStubAdv).
auto.
rcondf{1} 1; first auto. rcondf{2} 1; first auto. 
auto.
conseq
  (_ :
   ={r, m} /\ r{1} <> None /\ ={glob Adv, glob Rest, glob Par} /\
   ! MI.func{1} ++ [change_pari] <= m{1}.`2.`1 /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   ((oget r{1}).`1 = Adv =>
    (oget r{1}).`2.`2 \in rest_adv_pis) /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   _); first smt().
exlim m{1}.`2.`1 => oda.
case (after_par_or_rest_error MI.func{1} r{1} oda).
seq 1 1 :
  (r{1} = None /\ r{2} = None /\ !not_done{1} /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{1} (MakeRFComp_after_par_or_rest_error Rest Par).
call{2} (MakeRFComp_after_par_or_rest_error Rest CompEnvStubPar).
auto; smt().
rcondf{1} 1; first auto. rcondf{2} 1; first auto. 
seq 1 1 :
  (r{1} = None /\ r{2} = None /\ !not_done{1} /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{1}
  (MakeInt.MI_after_func_error (MakeRFComp(Rest, Par)) Adv).
call{2}
  (CompEnvMakeInt.MI_after_func_error
   (MakeRFComp(Rest, CompEnvStubPar)) CompEnvStubAdv).
auto.
rcondf{1} 1; first auto. rcondf{2} 1; first auto. 
auto.
case (after_par_or_rest_continue MI.func{1} r{1} oda).
seq 1 1 :
  (={r, m} /\ r{1} = Some m{1} /\ not_done{1} /\ not_done{2} /\
   after_par_or_rest_continue MI.func{1} r{1} oda /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
exlim r{1} => r'.
call{1} (MakeRFComp_after_par_or_rest_continue Rest Par r').
call{2} (MakeRFComp_after_par_or_rest_continue Rest CompEnvStubPar r').
auto; smt().
conseq
  (_ :
   ={r, m} /\ r{1} = Some m{1} /\ not_done{1} /\ not_done{2} /\
   (m{1}.`2.`1 = CompGlobs.mrfc_self{1} \/
    addr_eq_subfun rf_info CompGlobs.mrfc_self{1} m{1}.`2.`1 \/
    (m{1}.`1 = Dir /\
     addr_eq_param_rest rf_info CompGlobs.mrfc_self{1} m{1}.`2.`1) \/
    (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{2} /\ envport MI.func{2} m{1}.`3)) /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   _); first smt(after_par_or_rest_continue_implies_pre_cond_equiv1).
(* beginning of reduction to first conjunct of IH *)
transitivity{1}
  {r <@ LeftMFRC.f(m);}
  (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={m} /\ not_done{1} ==>
   ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={r})
  (={m} /\ not_done{2} /\
   (m{1}.`2.`1 = CompGlobs.mrfc_self{1} \/
    addr_eq_subfun rf_info CompGlobs.mrfc_self{1} m{1}.`2.`1 \/
    (m{1}.`1 = Dir /\
     addr_eq_param_rest rf_info CompGlobs.mrfc_self{1} m{1}.`2.`1) \/
    (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{2} /\ envport MI.func{2} m{1}.`3)) /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={glob Adv, glob Rest, glob Par} /\ ={r} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None) => //.
progress.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       CompGlobs.ce_func{1} CompGlobs.ce_stub_st{1}
       MakeInt.MI.func{1} CompEnvMakeInt.MI.func{1}
       CompEnvMakeInt.MI.in_guard{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} m{2} => //.
inline{2} 1; sp 0 3.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
transitivity{2}
  {r <@ RightMFRC.f(m);}
  (={m} /\ not_done{2} /\
   (m{1}.`2.`1 = CompGlobs.mrfc_self{1} \/
    addr_eq_subfun rf_info CompGlobs.mrfc_self{1} m{1}.`2.`1 \/
    (m{1}.`1 = Dir /\
     addr_eq_param_rest rf_info CompGlobs.mrfc_self{1} m{1}.`2.`1) \/
    (m{1}.`1 = Dir /\ m{1}.`2.`1 = MI.func{2} /\ envport MI.func{2} m{1}.`3)) /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={r} /\ ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None)
  (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   not_done{2} /\ ={m} ==>
   ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={r}) => //.
progress.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       MakeInt.MI.func{1} None MakeInt.MI.func{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} (MakeInt.MI.func{1} ++ [change_pari])
       (MakeInt.MI.in_guard{1} `|` rest_adv_pis) m{2} not_done{2} => //.
exlim (term_rest (glob Rest){1} + term_par (glob Par){1}) => tm.
case @[ambient] (0 <= tm < n) => [tm_ok | tm_not_ok].
have [#] first _ _ := IH tm _ => //.
call first; first auto; smt().
exfalso; smt(ge0_term_rest ge0_term_par).
inline{1} 1; sp 3 0.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
(* end of reduction to first conjunct of IH *)
seq 1 1 :
  (={r, m} /\ r{1} = Some m{1} /\ !not_done{1} /\ !not_done{2} /\
   ! MI.func{1} ++ [change_pari] <= oda /\
   after_par_or_rest_return MI.func{1} r{1} oda /\
   ((oget r{1}).`1 = Adv => (oget r{1}).`2.`2 \in rest_adv_pis) /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
exlim r{1} => r'.
call{1} (MakeRFComp_after_par_or_rest_return Rest Par r').
call{2} (MakeRFComp_after_par_or_rest_return Rest CompEnvStubPar r').
auto; smt().
rcondf{1} 1; first auto. rcondf{2} 1; first auto.
case (MakeInt.after_func_to_env MI.func{1} r{1}).
seq 1 1 :
  (={r, m} /\ r{1} = Some m{1} /\ !not_done{1} /\ !not_done{2} /\
   ! MI.func{1} ++ [change_pari] <= oda /\
   after_par_or_rest_return MI.func{1} r{1} oda /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
exlim r{1} => r'.
call{1} (MakeInt.MI_after_func_to_env (MakeRFComp(Rest, Par)) Adv r').
call{2}
  (CompEnvMakeInt.MI_after_func_to_env
   (MakeRFComp(Rest, CompEnvStubPar)) CompEnvStubAdv r').
auto; smt().
rcondf{1} 1; first auto. rcondf{2} 1; first auto.
auto.
exlim r{1} => r'.
seq 1 1 :
  (={r, m} /\ r{1} = Some m{1} /\ not_done{1} /\ not_done{2} /\
    m{1}.`1 = Adv /\ m{1}.`2.`1 = adv /\ 0 < m{1}.`2.`2 /\
    m{1}.`2.`2 \in rest_adv_pis /\ MI.func{1} <= m{1}.`3.`1 /\
    ! MI.func{1} ++ [change_pari] <= m{1}.`3.`1 /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{1} (MakeInt.MI_after_func_to_adv (MakeRFComp(Rest, Par)) Adv r').
call{2}
  (CompEnvMakeInt.MI_after_func_to_adv
   (MakeRFComp(Rest, CompEnvStubPar)) CompEnvStubAdv r').
auto;
  smt(inc_extl after_par_or_rest_return_implies_to_env_or_adv
      after_par_or_rest_return_from_rest).
rcondt{2} 1; first auto.
rcondf{2} 1; first auto; smt(inc_nle_l).
inline{2} 1. rcondf{2} 2; first auto. inline{2} 2.
rcondt{2} 3; first auto; smt(main_guard_ext_adv_advpi_in_new).
inline{2} 3; sp 0 5.
conseq
  (_ :
   m{1} = m2{2} /\ m{1}.`1 = Adv /\ m{1}.`2.`1 = adv /\
   not_done{1} /\ not_done0{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   _) => //.
(* start of reduction to LeftMI_RightMIFromAdv *)
transitivity{1}
  {r <@ LeftMI.f(m);}
  (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={m} /\ not_done{1} ==>
   ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={r})
  (m{1} = m2{2} /\ not_done0{2} /\
   m{1}.`1 = Adv /\ m{1}.`2.`1 = adv /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={glob Adv, glob Rest, glob Par} /\ ={r} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None) => //.
progress.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       CompGlobs.ce_func{1} CompGlobs.ce_stub_st{1}
       MakeInt.MI.func{1} CompEnvMakeInt.MI.func{1}
       CompEnvMakeInt.MI.in_guard{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} m2{2} => //.
inline{2} 1; sp 0 3.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
transitivity{2}
  {r <@ RightMIFromAdv.f(m2);}
  (m{1} = m2{2} /\ m{1}.`1 = Adv /\ m{1}.`2.`1 = adv /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={r} /\ ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None)
  (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   not_done0{2} /\ ={m2} ==>
   ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={r}) => //.
progress.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       MakeInt.MI.func{1} None MakeInt.MI.func{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} (MakeInt.MI.func{1} ++ [change_pari])
       (MakeInt.MI.in_guard{1} `|` rest_adv_pis) m2{2} => //.
exlim (term_rest (glob Rest){1} + term_par (glob Par){1}) => tm.
case @[ambient] (0 <= tm < n) => [tm_ok | tm_not_ok].
call (LeftMI_RightMIFromAdv tm func' in_guard_low').
have [#] first _ _ := IH tm _ => //.
have [#] _ second _ := IH tm _ => //.
auto.
exfalso; smt(ge0_term_rest ge0_term_par).
inline{1} 1; sp 3 0.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
(* end of reduction to LeftMI_RightMIFromAdv *)
(* end of LeftMFRC.f ~ RightMFRC.f *)
split.
(* start of second equiv: LeftMFRC.f ~ RightMIFromAdv *)
proc => /=.
sp 2 2.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
seq 1 1 :
  (={r} /\ ={glob Adv, glob Rest, glob Par} /\
   MI.func{2} <= m{1}.`2.`1 /\
   (r{1} = None \/
    term_rest (glob Rest){1} + term_par (glob Par){1} < n) /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
exlim (term_par (glob Par){1}) => tp.
call (Par_invoke tp).
auto; smt().
case (r{1} = None).
seq 1 1 :
  (={r} /\ r{1} = None /\ !not_done{1} /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{1} (MakeRFComp_after_par_or_rest_error Rest Par).
call{2} (MakeInt.MI_after_func_error Par Adv).
auto; smt(inc_extl).
rcondf{1} 1; first auto. rcondf{2} 1; first auto.
rcondf{2} 1; first auto; smt().
seq 1 1 :
  (={r} /\ r{1} = None /\ !not_done{1} /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{1}
  (MakeInt.MI_after_func_error (MakeRFComp(Rest, Par)) Adv).
call{2}
  (CompEnvMakeInt.MI_after_adv_error
   (MakeRFComp(Rest, CompEnvStubPar)) CompEnvStubAdv).
auto; smt().
rcondf{1} 1; first auto. rcondf{2} 1; first auto.
auto.
conseq
  (_ :
   ={r} /\
   CompGlobs.mrfc_self{1} ++ [change_pari] <= m{1}.`2.`1 /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   _); first smt().
case (MakeInt.after_func_error MI.func{2} r{2}).
seq 1 1 :
  (r{1} = None /\ r{2} = None /\ !not_done{1} /\ !not_done{2} /\
  ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{1} (MakeRFComp_after_par_or_rest_error Rest Par).
call{2} (MakeInt.MI_after_func_error Par Adv).
auto;
  smt(inc_extl
      after_func_error_ch_pari_implies_after_par_or_rest_error).
rcondf{1} 1; first auto. rcondf{2} 1; first auto.
rcondf{2} 1; first auto.
seq 1 1 :
  (r{1} = None /\ r{2} = None /\ !not_done{1} /\ !not_done{2} /\
  ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{1} (MakeInt.MI_after_func_error (MakeRFComp(Rest, Par)) Adv).
call{2}
  (CompEnvMakeInt.MI_after_adv_error
   (MakeRFComp(Rest, CompEnvStubPar)) CompEnvStubAdv).
auto.
rcondf{1} 1; first auto. rcondf{2} 1; first auto.
auto.
case (MakeInt.after_func_to_adv MI.func{2} r{2}).
seq 1 1 :
  (={r, m} /\ r{1} = Some m{1} /\
   !not_done{1} /\ not_done{2} /\
   MakeInt.after_func_to_adv MI.func{2} r{2} /\
   ! (MakeInt.after_func_error MI.func{2} r{2}) /\
   m{1}.`1 = Adv /\ m{1}.`2.`1 = adv /\ 0 < m{1}.`2.`2 /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
exlim r{1} => r1.
call{1} (MakeRFComp_after_par_or_rest_return Rest Par r1).
call{2} (MakeInt.MI_after_func_to_adv Par Adv r1).
auto; progress [-delta];
  smt(inc_extl oget_some
      after_func_to_adv_ch_pari_implies_after_par_or_rest_return_and_adv).
rcondf{1} 1; first auto.
seq 1 0 :
  (={r, m} /\ r{1} = Some m{1} /\ not_done{1} /\ not_done{2} /\
   MakeInt.after_func_to_adv MI.func{2} r{2} /\
   ! MakeInt.after_func_error MI.func{2} r{2} /\
   m{1}.`1 = Adv /\ m{1}.`2.`1 = adv /\
   0 < m{1}.`2.`2 /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
exlim r{1} => r1.
call{1}
  (MakeInt.MI_after_func_to_adv (MakeRFComp(Rest, Par)) Adv r1).
auto; smt(inc_extl le_trans le_ext_r).
conseq
  (_ :
   ={m} /\ not_done{1} /\ not_done{2} /\
   m{1}.`1 = Adv /\ m{1}.`2.`1 = adv /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   _) => //.
(* start of reduction to LeftMI_RightMIFromAdv *)
transitivity{1}
  {r <@ LeftMI.f(m);}
  (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={m} /\ not_done{1} ==>
   ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={r})
  (={m} /\ not_done{2} /\
   m{1}.`1 = Adv /\ m{1}.`2.`1 = adv /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={glob Adv, glob Rest, glob Par} /\ ={r} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None) => //.
progress.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       CompGlobs.ce_func{1} CompGlobs.ce_stub_st{1}
       MakeInt.MI.func{1} CompEnvMakeInt.MI.func{1}
       CompEnvMakeInt.MI.in_guard{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} m{2} => //.
inline{2} 1; sp 0 3.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
transitivity{2}
  {r <@ RightMIFromAdv.f(m);}
  (={m} /\
   m{1}.`1 = Adv /\ m{1}.`2.`1 = adv /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={r} /\ ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None)
   (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
    not_done{2} /\ ={m} ==>
    ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
    ={r}) => //.
progress.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       MakeInt.MI.func{1} None MakeInt.MI.func{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} (MakeInt.MI.func{1} ++ [change_pari])
       (MakeInt.MI.in_guard{1} `|` rest_adv_pis) m{2} => //.
exlim (term_rest (glob Rest){1} + term_par (glob Par){1}) => tm.
case @[ambient] (0 <= tm < n) => [tm_ok | tm_not_ok].
call (LeftMI_RightMIFromAdv tm func' in_guard_low').
have [#] first _ _ := IH tm _ => //.
have [#] _ second _ := IH tm _ => //.
auto.
exfalso; smt(ge0_term_rest ge0_term_par).
inline{1} 1; sp 3 0.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
(* end of reduction to LeftMI_RightMIFromPar *)
exlim r{2} => r2'.
seq 0 1 :
  (={r} /\ r{2} = Some m{2} /\
   !not_done{2} /\
   CompGlobs.mrfc_self{1} ++ [change_pari] <= m{1}.`2.`1 /\
   MakeInt.after_func_to_env MI.func{2} r{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{2} (MakeInt.MI_after_func_to_env Par Adv r2').
auto; smt(inc_extl MakeInt.after_func_disj).
rcondf{2} 1; first auto. rcondt{2} 1; first auto.
rcondt{2} 2; first auto; smt().
sp 0 3; elim* => r_R ce_stub_st_R m_R.
seq 0 1 :
  (r{1} = r_R /\ MakeInt.after_func_to_env MI.func{2} r_R /\
   not_done{2} /\ CompGlobs.ce_stub_st{2} = r_R /\ r{2} = Some m{2} /\
   m{2} = dummy_msg_to_stub_par CompGlobs.ce_func{2} /\
   CompGlobs.mrfc_self{1} ++ [change_pari] <= m{1}.`2.`1 /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis).
exlim r{2} => r2''.
call{2}
  (CompEnvMakeInt.MI_after_adv_to_func
   (MakeRFComp(Rest, CompEnvStubPar)) CompEnvStubAdv r2'').
auto; progress; smt(inc_extl).
rcondt{2} 1; first auto.
rcondt{2} 1; first auto.
inline{2} 1; first auto.
sp 0 2.
rcondt{2} 1; first auto; progress [-delta].
rewrite /dummy_msg_to_stub_par /=.
left; smt(rf_info_valid change_pari_valid le_refl).
inline{2} 1; sp 0 3.
rcondt{2} 1; first auto.
rcondt{2} 1; first auto.
inline{2} 1.
rcondt{2} 2; first auto; smt().
sp 0 4; elim* => r1_R.
conseq
  (_ :
   r{1} = r1{2} /\ r1{2} = r_R /\
   MakeInt.after_func_to_env MakeInt.MI.func{2} r_R /\
   CompGlobs.mrfc_self{1} ++ [change_pari] <= m{1}.`2.`1 /\
   CompGlobs.mrfc_self{1} ++ [change_pari] <= m1{2}.`2.`1 /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MakeInt.MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MakeInt.MI.in_guard{1} = in_guard_low' /\
    CompEnvMakeInt.MI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MakeInt.MI.func{2} = func' ++ [change_pari] /\
   CompEnvMakeInt.MI.in_guard{2} = in_guard_low' /\
   MakeInt.MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   _) => //.
case (after_par_or_rest_error MI.func{1} r{1} m{1}.`2.`1).
seq 1 1 :
  (r{1} = None /\ r1{2} = None /\ !not_done{1} /\ !not_done0{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{1} (MakeRFComp_after_par_or_rest_error Rest Par).
call{2} (MakeRFComp_after_par_or_rest_error Rest CompEnvStubPar).
auto; progress [-delta];
  smt(pari_cond_after_par_or_rest_error_equiv).
rcondf{1} 1; first auto. rcondf{2} 1; first auto.
sp 0 2.
seq 1 1 :
  (r{1} = None /\ r{2} = None /\ !not_done{1} /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{1}
  (MakeInt.MI_after_func_error (MakeRFComp(Rest, Par)) Adv).
call{2}
  (CompEnvMakeInt.MI_after_func_error
   (MakeRFComp(Rest, CompEnvStubPar)) CompEnvStubAdv).
auto.
rcondf{1} 1; first auto. rcondf{2} 1; first auto.
auto.
seq 1 1 :
  (r{1} = r1{2} /\ r{1} = Some m{1} /\ r1{2} = Some m1{2} /\
   not_done{1} /\ not_done0{2} /\ m{1}.`2.`1 = MI.func{1} /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MakeInt.MI.func{1} = func' /\  CompGlobs.mrfc_self{1} = func' /\
   MakeInt.MI.in_guard{1} = in_guard_low' /\
   CompEnvMakeInt.MI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\
   MakeInt.MI.func{2} = func' ++ [change_pari] /\
   CompEnvMakeInt.MI.in_guard{2} = in_guard_low' /\
   MakeInt.MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
exlim r{1} => r1'.
call{1} (MakeRFComp_after_par_or_rest_continue Rest Par r1').
call{2} (MakeRFComp_after_par_or_rest_continue Rest CompEnvStubPar r1').
auto; progress [-delta].
smt(after_func_to_env_ch_pari_implies_after_par_or_rest_cont_or_error
    pari_cond_after_par_or_rest_error_equiv).
smt(). smt(after_par_or_rest_continue_from_change_pari).
(* beginning of reduction to first conjunct of IH *)
transitivity{1}
  {r <@ LeftMFRC.f(m);}
  (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={m} /\ not_done{1} ==>
   ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={r})
  (m{1} = m1{2} /\ not_done0{2} /\ m{1}.`2.`1 = MI.func{1} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={glob Adv, glob Rest, glob Par} /\ ={r} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None) => //.
move => &1 &2 [#] *.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       CompGlobs.ce_func{1} CompGlobs.ce_stub_st{1}
       MakeInt.MI.func{1} CompEnvMakeInt.MI.func{1}
       CompEnvMakeInt.MI.in_guard{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} m1{2}; smt().
inline{2} 1; sp 0 3.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
transitivity{2}
  {r <@ RightMFRC.f(m1);}
  (m{1} = m1{2} /\ not_done{2} /\ m{1}.`2.`1 = MI.func{1} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={r} /\ ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None)
  (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   not_done0{2} /\ ={m1} ==>
   ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={r}) => //.
move => &1 &2 [#] *.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       MakeInt.MI.func{1} None MakeInt.MI.func{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} (MakeInt.MI.func{1} ++ [change_pari])
       (MakeInt.MI.in_guard{1} `|` rest_adv_pis) m1{2} not_done0{2}; smt().
exlim (term_rest (glob Rest){1} + term_par (glob Par){1}) => tm.
case @[ambient] (0 <= tm < n) => [tm_ok | tm_not_ok].
have [#] first _ _ := IH tm _ => //.
call first; first auto; smt().
exfalso; smt(ge0_term_rest ge0_term_par).
inline{1} 1; sp 3 0.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
(* end of LeftMFRC.f ~ RightMIFromAdv *)
(* start of third equiv: LeftMFRC.f ~ RightMIFromPar *)
proc => /=.
sp 2 2.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
seq 1 1 :
  (={r} /\ ={glob Adv, glob Rest, glob Par} /\
   MI.func{2} <= m{1}.`2.`1 /\  MI.func{2} <= m_orig{2}.`2.`1 /\
   (r{1} = None \/
    term_rest (glob Rest){1} + term_par (glob Par){1} < n) /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
exlim (term_par (glob Par){1}) => tp.
call (Par_invoke tp).
auto; smt().
case (r{1} = None).
seq 1 1 :
  (={r} /\ r{1} = None /\ !not_done{1} /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{1} (MakeRFComp_after_par_or_rest_error Rest Par).
call{2} (MakeInt.MI_after_func_error Par Adv).
auto; smt(inc_extl).
rcondf{1} 1; first auto. rcondf{2} 1; first auto.
rcondf{2} 1; first auto; smt().
seq 1 1 :
  (={r} /\ r{1} = None /\ !not_done{1} /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{1}
  (MakeInt.MI_after_func_error (MakeRFComp(Rest, Par)) Adv).
call{2} (MakeRFComp_after_par_or_rest_error Rest CompEnvStubPar).
auto; smt().
rcondf{1} 1; first auto. rcondf{2} 1; first auto.
seq 1 1 :
  (={r} /\ !not_done{1} /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{2}
  (CompEnvMakeInt.MI_after_func_error (MakeRFComp(Rest, CompEnvStubPar))
   CompEnvStubAdv).
auto; smt(inc_extl).
rcondf{2} 1; first auto.
auto.
conseq
  (_ :
   ={r} /\
   CompGlobs.mrfc_self{1} ++ [change_pari] <= m{1}.`2.`1 /\
   CompGlobs.mrfc_self{1} ++ [change_pari] <= m_orig{2}.`2.`1 /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   _); first smt().
case (MakeInt.after_func_error MI.func{2} r{2}).
seq 1 1 :
  (r{1} = None /\ r{2} = None /\ !not_done{1} /\ !not_done{2} /\
  ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{1} (MakeRFComp_after_par_or_rest_error Rest Par).
call{2} (MakeInt.MI_after_func_error Par Adv).
auto;
  smt(inc_extl
      after_func_error_ch_pari_implies_after_par_or_rest_error).
rcondf{1} 1; first auto. rcondf{2} 1; first auto.
rcondf{2} 1; first auto.
seq 1 1 :
  (r{1} = None /\ r{2} = None /\ !not_done{1} /\ !not_done{2} /\
  ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{1} (MakeInt.MI_after_func_error (MakeRFComp(Rest, Par)) Adv).
call{2} (MakeRFComp_after_par_or_rest_error Rest CompEnvStubPar).
auto.
rcondf{1} 1; first auto. rcondf{2} 1; first auto.
seq 0 1 :
  (r{1} = None /\ r{2} = None /\ !not_done{1} /\ !not_done{2} /\
  ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{2}
  (CompEnvMakeInt.MI_after_func_error
   (MakeRFComp(Rest, CompEnvStubPar)) CompEnvStubAdv); first auto.
rcondf{2} 1; first auto.
auto.
case (MakeInt.after_func_to_adv MI.func{2} r{2}).
seq 1 1 :
  (={r, m} /\ r{1} = Some m{1} /\
   ! not_done{1} /\ not_done{2} /\
   CompGlobs.mrfc_self{1} ++ [change_pari] <= m_orig{2}.`2.`1 /\
   MakeInt.after_func_to_adv MI.func{2} r{2} /\
   ! (MakeInt.after_func_error MI.func{2} r{2}) /\
   m{1}.`1 = Adv /\ m{1}.`2.`1 = adv /\ 0 < m{1}.`2.`2 /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
exlim r{1} => r1.
call{1} (MakeRFComp_after_par_or_rest_return Rest Par r1).
call{2} (MakeInt.MI_after_func_to_adv Par Adv r1).
auto; progress [-delta];
  smt(inc_extl oget_some
      after_func_to_adv_ch_pari_implies_after_par_or_rest_return_and_adv).
rcondf{1} 1; first auto.
seq 1 0 :
  (={r, m} /\ r{1} = Some m{1} /\ not_done{1} /\ not_done{2} /\
   MakeInt.after_func_to_adv MI.func{2} r{2} /\
   ! MakeInt.after_func_error MI.func{2} r{2} /\
   m{1}.`1 = Adv /\ m{1}.`2.`1 = adv /\
   0 < m{1}.`2.`2 /\
   MI.func{1} ++ [change_pari] <= m_orig{2}.`2.`1 /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
exlim r{1} => r1.
call{1}
  (MakeInt.MI_after_func_to_adv (MakeRFComp(Rest, Par)) Adv r1).
auto; smt(inc_extl le_trans le_ext_r).
conseq
  (_ :
   ={m} /\ not_done{1} /\ not_done{2} /\
   m{1}.`1 = Adv /\ m{1}.`2.`1 = adv /\
   MI.func{1} ++ [change_pari] <= m_orig{2}.`2.`1 /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   _) => //.
(* start of reduction to LeftMI_RightMIFromPar *)
transitivity{1}
  {r <@ LeftMI.f(m);}
  (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={m} /\ not_done{1} ==>
   ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={r})
  (={m} /\ not_done{2} /\
   m{1}.`1 = Adv /\ m{1}.`2.`1 = adv /\
   MI.func{1} ++ [change_pari] <= m_orig{2}.`2.`1 /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={glob Adv, glob Rest, glob Par} /\ ={r} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None) => //.
progress.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       CompGlobs.ce_func{1} CompGlobs.ce_stub_st{1}
       MakeInt.MI.func{1} CompEnvMakeInt.MI.func{1}
       CompEnvMakeInt.MI.in_guard{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} m{2} => //.
inline{2} 1; sp 0 3.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
transitivity{2}
  {r <@ RightMIFromPar.f(m, m_orig);}
  (={m} /\ MI.func{1} ++ [change_pari] <= m_orig{2}.`2.`1 /\
   m{1}.`1 = Adv /\ m{1}.`2.`1 = adv /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={r} /\ ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None)
   (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
    not_done{2} /\ ={m, m_orig} ==>
    ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
    ={r}) => //.
progress.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       MakeInt.MI.func{1} None MakeInt.MI.func{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} (MakeInt.MI.func{1} ++ [change_pari])
       (MakeInt.MI.in_guard{1} `|` rest_adv_pis) m{2} m_orig{2} => //.
exlim (term_rest (glob Rest){1} + term_par (glob Par){1}) => tm.
case @[ambient] (0 <= tm < n) => [tm_ok | tm_not_ok].
call (LeftMI_RightMIFromPar tm func' in_guard_low').
have [#] first _ _ := IH tm _ => //.
have [#] _ _ third := IH tm _ => //.
auto.
exfalso; smt(ge0_term_rest ge0_term_par).
inline{1} 1; sp 4 0.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
(* end of reduction to LeftMI_RightMIFromPar *)
exlim r{2} => r2'.
seq 0 1 :
  (={r} /\ r{2} = Some m{2} /\
   !not_done{2} /\
   CompGlobs.mrfc_self{1} ++ [change_pari] <= m{1}.`2.`1 /\
   CompGlobs.mrfc_self{1} ++ [change_pari] <= m_orig{2}.`2.`1 /\
   MakeInt.after_func_to_env MI.func{2} r{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{2} (MakeInt.MI_after_func_to_env Par Adv r2').
auto; smt(inc_extl MakeInt.after_func_disj).
rcondf{2} 1; first auto. rcondt{2} 1; first auto.
rcondf{2} 2; first auto; smt().
sp 0 1.
case (after_par_or_rest_error MI.func{1} r{1} m{1}.`2.`1).
seq 1 1 :
  (r{1} = None /\ r{2} = None /\ !not_done{1} /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{1} (MakeRFComp_after_par_or_rest_error Rest Par).
call{2} (MakeRFComp_after_par_or_rest_error Rest CompEnvStubPar).
auto; smt(pari_cond_after_par_or_rest_error_equiv).
rcondf{1} 1; first auto.
seq 1 0 :
  (r{1} = None /\ r{2} = None /\ !not_done{1} /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{1} (MakeInt.MI_after_func_error (MakeRFComp(Rest, Par)) Adv).
auto.
rcondf{1} 1; first auto.
rcondf{2} 1; first auto.
seq 0 1 :
  (r{1} = None /\ r{2} = None /\ !not_done{1} /\ !not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call{2}
  (CompEnvMakeInt.MI_after_func_error
   (MakeRFComp(Rest, CompEnvStubPar)) CompEnvStubAdv).
auto.
rcondf{2} 1; first auto.
auto.
exlim m{1}.`2.`1 => oda.
seq 1 1 :
  (={r, m} /\ r{1} = Some m{1} /\ not_done{1} /\ not_done{2} /\
   CompGlobs.mrfc_self{1} ++ [change_pari] <= oda /\
   after_par_or_rest_continue MI.func{1} r{1} oda /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
exlim r{1} => r'.
call{1} (MakeRFComp_after_par_or_rest_continue Rest Par r').
call{2} (MakeRFComp_after_par_or_rest_continue Rest CompEnvStubPar r').
auto; 
  smt(after_func_to_env_ch_pari_implies_after_par_or_rest_cont_or_error
      pari_cond_after_par_or_rest_error_equiv).
conseq
  (_ :
   ={r, m} /\ r{1} = Some m{1} /\ not_done{1} /\ not_done{2} /\
   m{1}.`2.`1 = MI.func{1} /\
   ={glob Adv, glob Rest, glob Par} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   _).
progress [-delta].
have :=
  after_par_or_rest_continue_from_change_pari MI.func{1}
  (Some m{2}) oda _ _ => //.
(* beginning of reduction to first conjunct of IH *)
transitivity{1}
  {r <@ LeftMFRC.f(m);}
  (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={m} /\ not_done{1} ==>
   ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={r})
  (={m} /\ not_done{2} /\ m{1}.`2.`1 = MI.func{1} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={glob Adv, glob Rest, glob Par} /\ ={r} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None) => //.
move => &1 &2 [#] -> -> H1 -> -> H2 -> -> ->.
progress.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       CompGlobs.ce_func{1} CompGlobs.ce_stub_st{1}
       MakeInt.MI.func{1} CompEnvMakeInt.MI.func{1}
       CompEnvMakeInt.MI.in_guard{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} m{2}; smt().
inline{2} 1; sp 0 3.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
transitivity{2}
  {r <@ RightMFRC.f(m);}
  (={m} /\ not_done{2} /\ m{1}.`2.`1 = MI.func{1} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   term_rest (glob Rest){1} + term_par (glob Par){1} < n /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={r} /\ ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None)
  (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   not_done{2} /\ ={m, m_orig} ==>
   ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={r}) => //.
move =>
  &1 &2 [#] -> H0 H1 -> -> -> H2 H3 H4 H5 H6 H7 H8 H9 H10
  H11 H12 H13 H14.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       MakeInt.MI.func{1} None MakeInt.MI.func{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} (MakeInt.MI.func{1} ++ [change_pari])
       (MakeInt.MI.in_guard{1} `|` rest_adv_pis) m{2}
       m_orig{2} not_done{2}; smt().
exlim (term_rest (glob Rest){1} + term_par (glob Par){1}) => tm.
case @[ambient] (0 <= tm < n) => [tm_ok | tm_not_ok].
have [#] first _ _ := IH tm _ => //.
call first; first auto; smt().
exfalso; smt(ge0_term_rest ge0_term_par).
inline{1} 1; sp 3 0.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
(* end of reduction to first conjunct of IH *)
qed.

lemma comp_bridge (func' : addr, in_guard_low' : int fset) &m :
  exper_pre func' => disjoint in_guard_low' rest_adv_pis =>
  Pr[Exper(MI(MakeRFComp(Rest, Par), Adv), Env)
       .main(func', in_guard_low') @ &m : res] =
  Pr[Exper(MI(Par, Adv), CompEnv(Rest, Env))
       .main(func' ++ [change_pari], in_guard_low' `|` rest_adv_pis)
         @ &m : res].
proof.
move => ep_func' disj_igl'_rest_adv_pis.
byequiv => //.
proc; inline *; wp.
swap{2} 6 14; swap{2} 5 14; swap{2} 17 1; sp.
seq 3 3 :
  (={glob Env, glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   _self{1} = func' /\ _self{1} = func{1} /\
   _self{1} = MI.func{1} /\ _self{1} = CompGlobs.mrfc_self{1} /\
   in_guard{1} = in_guard_low' /\ in_guard{1} = MI.in_guard{1} /\
   _self{2} = func' /\ _self{2} = func0{2} /\
   _self{2} = CompEnvMI.func{2} /\
   _self{2} = CompGlobs.mrfc_self{2} /\ _self{2} = CompGlobs.ce_func{2} /\
   MI.func{2} = func' ++ [change_pari] /\
   in_guard1{2} = CompEnvMI.in_guard{2} /\
   in_guard1{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
call (_ : true).
call Par_init.
call Rest_init.
auto; progress.
rewrite size_cat /= take_size_cat //.
rewrite size_cat /= take_size_cat //.
by rewrite disjoint_add_remove.
call
  (_ :
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None).
proc.
if => //.
inline loop.
sp 3 3.
case (MI.func{1} <= m0{1}.`2.`1).
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
inline{1} 1; inline{2} 1.
sp 2 2.
if => //.
inline{1} 1; inline{2} 1.
sp 3 3; wp.
(* start of reduction to LeftMFRC ~ RightMFRC *)
conseq
  (_ :
   ={m2} /\ not_done0{1} /\ not_done0{2} /\
   (m2{1}.`2.`1 = CompGlobs.mrfc_self{1} \/
    addr_eq_subfun rf_info CompGlobs.mrfc_self{1} m2{1}.`2.`1 \/
    (m2{1}.`1 = Dir /\
     addr_eq_param_rest rf_info CompGlobs.mrfc_self{1} m2{1}.`2.`1) \/
    (m2{1}.`1 = Adv /\
     addr_ge_param_rest rf_info CompGlobs.mrfc_self{1} m2{1}.`2.`1) \/
    (m2{1}.`1 = Dir /\ m2{1}.`2.`1 = MI.func{2} /\
     envport MI.func{2} m2{1}.`3)) /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   _).
auto; smt(inc_nle_l).
transitivity{1}
  {r0 <@ LeftMFRC.f(m2);}
  (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={m2} /\ not_done0{1} ==>
   ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={r0})
  (={m2} /\ not_done0{1} /\ not_done0{2} /\
   (m2{1}.`2.`1 = CompGlobs.mrfc_self{1} \/
    addr_eq_subfun rf_info CompGlobs.mrfc_self{1} m2{1}.`2.`1 \/
    (m2{1}.`1 = Dir /\
     addr_eq_param_rest rf_info CompGlobs.mrfc_self{1} m2{1}.`2.`1) \/
    (m2{1}.`1 = Adv /\
     addr_ge_param_rest rf_info CompGlobs.mrfc_self{1} m2{1}.`2.`1) \/
    (m2{1}.`1 = Dir /\ m2{1}.`2.`1 = MI.func{2} /\
     envport MI.func{2} m2{1}.`3)) /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
  ={glob Adv, glob Rest, glob Par} /\ ={r0} /\
  invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
  MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
  MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
  CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
  MI.func{2} = func' ++ [change_pari] /\
  CompEnvMI.in_guard{2} = in_guard_low' /\
  MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
  CompGlobs.ce_stub_st{2} = None) => //.
progress.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       CompGlobs.ce_func{1} CompGlobs.ce_stub_st{1}
       MakeInt.MI.func{1} CompEnvMakeInt.MI.func{1}
       CompEnvMakeInt.MI.in_guard{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} m2{2} true => //.
inline{2} 1; sp 0 3.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
transitivity{2}
  {r0 <@ RightMFRC.f(m2);}
  (={m2} /\
   (m2{1}.`2.`1 = CompGlobs.mrfc_self{1} \/
    addr_eq_subfun rf_info CompGlobs.mrfc_self{1} m2{1}.`2.`1 \/
    (m2{1}.`1 = Dir /\
     addr_eq_param_rest rf_info CompGlobs.mrfc_self{1} m2{1}.`2.`1) \/
    (m2{1}.`1 = Adv /\
     addr_ge_param_rest rf_info CompGlobs.mrfc_self{1} m2{1}.`2.`1) \/
    (m2{1}.`1 = Dir /\ m2{1}.`2.`1 = MI.func{2} /\
     envport MI.func{2} m2{1}.`3)) /\
    ={glob Adv, glob Rest, glob Par} /\
    invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
    MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
    MI.in_guard{1} = in_guard_low' /\
    CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
    CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
    CompEnvMI.in_guard{2} = in_guard_low' /\
    MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
    CompGlobs.ce_stub_st{2} = None ==>
   ={r0} /\ ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None)
  (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   not_done0{2} /\ ={m2} ==>
   ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={r0}) => //.
progress.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       MakeInt.MI.func{1} None MakeInt.MI.func{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} (MakeInt.MI.func{1} ++ [change_pari])
       (MakeInt.MI.in_guard{1} `|` rest_adv_pis) m2{2} => //.
exlim (glob Rest){1}, (glob Par){2} => gr gp.
have [#] first _ _ :=
  comp_bridge_induct func' in_guard_low'
  ep_func' disj_igl'_rest_adv_pis (term_rest gr + term_par gp).
call first; first auto.
inline{1} 1; sp 3 0.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
(* end of LeftMFRC ~ RightMFRC reduction *)
sp 1 1; elim* => r0_r r0_L.
seq 1 1 :
  (={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None /\
   ={r0, not_done} /\ r0{1} = None /\ !not_done{1}).
call{1} (MakeInt.MI_after_func_error (MakeRFComp(Rest, Par)) Adv).
call{2}
  (CompEnvMakeInt.MI_after_func_error (MakeRFComp(Rest, CompEnvStubPar))
   CompEnvStubAdv).
auto; smt().
rcondf{1} 1; first auto. rcondf{2} 1; first auto.
auto; smt().
conseq
  (_ :
   ={m0} /\ m0{1}.`1 = Adv /\ m0{1}.`2.`1 = adv /\
   MakeInt.main_guard MakeInt.MI.func{1} MakeInt.MI.in_guard{1} m0{1} /\
   not_done{1} /\ not_done{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   _); first smt(le_refl).
rcondt{2} 1; first auto.
rcondf{2} 1; first auto; smt(inc_nle_l).
inline{2} 1; sp 0 1.
rcondf{2} 1; first auto.
inline{2} 1; sp 0 1.
rcondt{2} 1; first auto; smt(main_guard_ext inc_nle_l).
inline{2} 1; sp 0 3.
conseq
  (_ :
   m0{1} = m3{2} /\ m0{1}.`1 = Adv /\ m0{1}.`2.`1 = adv /\
   not_done{1} /\ not_done0{2} /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   _) => //.
(* start of reduction to LeftMI ~ RightMIFromAdv *)
transitivity{1}
  {r <@ LeftMI.f(m0);}
  (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={m0} /\ not_done{1} ==>
   ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={r})
  (m0{1} = m3{2} /\ not_done{1} /\ not_done0{2} /\
   m0{1}.`1 = Adv /\ m0{1}.`2.`1 = adv /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
  ={glob Adv, glob Rest, glob Par} /\ ={r} /\
  invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
  MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
  MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
  CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
  MI.func{2} = func' ++ [change_pari] /\
  CompEnvMI.in_guard{2} = in_guard_low' /\
  MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
  CompGlobs.ce_stub_st{2} = None) => //.
progress.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       CompGlobs.ce_func{1} CompGlobs.ce_stub_st{1}
       MakeInt.MI.func{1} CompEnvMakeInt.MI.func{1}
       CompEnvMakeInt.MI.in_guard{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} m3{2} true => //.
inline{2} 1; sp 0 3.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
transitivity{2}
  {r <@ RightMIFromAdv.f(m3);}
  (m0{1} = m3{2} /\ m0{1}.`1 = Adv /\ m0{1}.`2.`1 = adv /\
   ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\
   CompEnvMI.func{2} = func' /\ CompGlobs.mrfc_self{2} = func' /\
   CompGlobs.ce_func{2} = func' /\ MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None ==>
   ={r} /\ ={glob Adv, glob Rest, glob Par} /\
   invar_rest (glob Rest){1} /\ invar_par (glob Par){1} /\
   MI.func{1} = func' /\ CompGlobs.mrfc_self{1} = func' /\
   MI.in_guard{1} = in_guard_low' /\ CompEnvMI.func{2} = func' /\
   CompGlobs.mrfc_self{2} = func' /\ CompGlobs.ce_func{2} = func' /\
   MI.func{2} = func' ++ [change_pari] /\
   CompEnvMI.in_guard{2} = in_guard_low' /\
   MI.in_guard{2} = in_guard_low' `|` rest_adv_pis /\
   CompGlobs.ce_stub_st{2} = None)
  (={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   not_done0{2} /\ ={m3} ==>
   ={glob Adv, glob Rest, glob Par, glob CompGlobs, glob MI} /\
   ={r}) => //.
progress.
exists (glob Adv){2} (glob Par){2} (glob Rest){2}
       MakeInt.MI.func{1} None MakeInt.MI.func{1} MakeInt.MI.func{1}
       MakeInt.MI.in_guard{1} (MakeInt.MI.func{1} ++ [change_pari])
       (MakeInt.MI.in_guard{1} `|` rest_adv_pis) m3{2} => //.
exlim (glob Rest){1}, (glob Par){2} => gr gp.
call
  (LeftMI_RightMIFromAdv (term_rest gr + term_par gp)
   func' in_guard_low').
have [#] first _ _  // :=
  comp_bridge_induct func' in_guard_low'
  ep_func' disj_igl'_rest_adv_pis (term_rest gr + term_par gp).
have [#] _ second _  // :=
  comp_bridge_induct func' in_guard_low'
  ep_func' disj_igl'_rest_adv_pis (term_rest gr + term_par gp).
auto.
inline{1} 1; sp 3 0.
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
sim.
(* end of reduction to LeftMI ~ RightMIFromAdv *)
auto.
auto.
qed.

end section.

lemma compos_bridge
      (Env <: ENV{-MI, -CompGlobs}) (Adv <: ADV{-MI, -CompGlobs, -Env})
      (Rest <: FUNC{-MI, -CompGlobs, -Env, -Adv})
      (Par <: FUNC{-MI, -CompGlobs, -Env, -Adv, -Rest})
      (invar_rest : glob Rest -> bool, term_rest : glob Rest -> int,
       invar_par : glob Par -> bool, term_par : glob Par -> int)
      (func' : addr, in_guard_low' : int fset) &m :
  (forall (gl : glob Rest), invar_rest gl => 0 <= term_rest gl) =>
  hoare [Rest.init : true ==> invar_rest (glob Rest)] =>
  (forall (n : int),
   hoare
   [Rest.invoke :
    invar_rest (glob Rest) /\ term_rest (glob Rest) = n ==>
    invar_rest (glob Rest) /\
    (res <> None =>
     term_rest (glob Rest) < n /\
     ((oget res).`1 = Adv => (oget res).`2.`2 \in rest_adv_pis))]) =>
  (forall (gl : glob Par), invar_par gl => 0 <= term_par gl) =>
  hoare [Par.init : true ==> invar_par (glob Par)] =>
  (forall (n : int),
   hoare
   [Par.invoke :
    invar_par (glob Par) /\ term_par (glob Par) = n ==>
    invar_par (glob Par) /\
    (res <> None =>
     term_par (glob Par) < n /\
     ((oget res).`1 = Adv => (oget res).`2.`2 \in change_par_adv_pis))]) =>
  exper_pre func' => disjoint in_guard_low' rest_adv_pis =>
  Pr[Exper(MI(MakeRFComp(Rest, Par), Adv), Env)
       .main(func', in_guard_low') @ &m : res] =
  Pr[Exper(MI(Par, Adv), CompEnv(Rest, Env))
       .main
        (func' ++ [change_pari],
         in_guard_low' `|` rest_adv_pis)
       @ &m : res].
proof.
move =>
  ge0_term_rest rest_init rest_invoke
  ge0_term_par  par_init  par_invoke
  ep_func' disj_igl'_rest_adv_pis.
have rest_init_equiv :=
  init_invar_hoare_implies_equiv Rest invar_rest rest_init.
have rest_invoke_equiv :
  forall (n : int),
  equiv
  [Rest.invoke ~ Rest.invoke :
   ={arg, glob Rest} /\ invar_rest (glob Rest){1} /\
   term_rest (glob Rest){1} = n ==>
   ={res, glob Rest} /\ invar_rest (glob Rest){1} /\
   (res{1} <> None =>
    term_rest (glob Rest){1} < n /\
    ((oget res{1}).`1 = Adv => (oget res{1}).`2.`2 \in rest_adv_pis))].
  move => n.
  rewrite
  (invoke_term_metric_hoare_implies_equiv Rest
   invar_rest term_rest)
  rest_invoke.
have par_init_equiv :=
  init_invar_hoare_implies_equiv Par invar_par par_init.
have par_invoke_equiv :
  forall (n : int),
  equiv
  [Par.invoke ~ Par.invoke :
   ={arg, glob Par} /\ invar_par (glob Par){1} /\
   term_par (glob Par){1} = n ==>
   ={res, glob Par} /\ invar_par (glob Par){1} /\
   (res{1} <> None =>
    term_par (glob Par){1} < n /\
    ((oget res{1}).`1 = Adv => (oget res{1}).`2.`2 \in change_par_adv_pis))].
  move => n.
  rewrite
  (invoke_term_metric_hoare_implies_equiv Par
   invar_par term_par)
  par_invoke.
apply
  (comp_bridge Env Adv Rest Par
   invar_rest term_rest invar_par term_par
   ge0_term_rest rest_init_equiv rest_invoke_equiv
   ge0_term_par par_init_equiv par_invoke_equiv
   _ _ &m) => //.
qed.

(* the composition theorem

   when used:

     Adv1 wil be Adv
     Par1 will be the fully real functionality
     Adv2 will be the application of the corresponding
       simulator to Adv
     Par2 will be the corresponding ideal functionality

   note that the assumption about the bound relating to these modules
   will be an application of the security of the parameter as long as

     disjoint (change_par_adv_pis `|` rest_adv_pis) in_guard' *)

lemma composition
      (Env <: ENV{-MI, -CompGlobs}) (Rest <: FUNC{-MI, -CompGlobs, -Env})
      (Adv1 <: ADV{-MI, -CompGlobs, -Env, -Rest})
      (Par1 <: FUNC{-MI, -CompGlobs, -Env, -Rest, -Adv1})
      (Adv2 <: ADV{-MI, -CompGlobs, -Env, -Rest})
      (Par2 <: FUNC{-MI, -CompGlobs, -Env, -Rest, -Adv2})
      (invar_rest : glob Rest -> bool, term_rest : glob Rest -> int,
       invar_par1 : glob Par1 -> bool, term_par1 : glob Par1 -> int,
       invar_par2 : glob Par2 -> bool, term_par2 : glob Par2 -> int)
      (func' : addr, in_guard' : int fset, b : real) &m :
  (forall (gl : glob Rest), invar_rest gl => 0 <= term_rest gl) =>
  hoare [Rest.init : true ==> invar_rest (glob Rest)] =>
  (forall (n : int),
   hoare
   [Rest.invoke :
    invar_rest (glob Rest) /\ term_rest (glob Rest) = n ==>
    invar_rest (glob Rest) /\
    (res <> None =>
       term_rest (glob Rest) < n /\
       ((oget res).`1 = Adv => (oget res).`2.`2 \in rest_adv_pis))]) =>
  (forall (gl : glob Par1), invar_par1 gl => 0 <= term_par1 gl) =>
  hoare [Par1.init : true ==> invar_par1 (glob Par1)] =>
  (forall (n : int),
   hoare
   [Par1.invoke :
    invar_par1 (glob Par1) /\ term_par1 (glob Par1) = n ==>
    invar_par1 (glob Par1) /\
    (res <> None =>
       term_par1 (glob Par1) < n /\
       ((oget res).`1 = Adv => (oget res).`2.`2 \in change_par_adv_pis))]) =>
  (forall (gl : glob Par2), invar_par2 gl => 0 <= term_par2 gl) =>
  hoare [Par2.init : true ==> invar_par2 (glob Par2)] =>
  (forall (n : int),
   hoare
   [Par2.invoke :
    invar_par2 (glob Par2) /\ term_par2 (glob Par2) = n ==>
    invar_par2 (glob Par2) /\
    (res <> None =>
       term_par2 (glob Par2) < n /\
       ((oget res).`1 = Adv => (oget res).`2.`2 \in change_par_adv_pis))]) =>
  exper_pre func' => disjoint in_guard' rest_adv_pis =>
  `|Pr[Exper(MI(Par1, Adv1), CompEnv(Rest, Env))
         .main(func' ++ [change_pari], in_guard' `|` rest_adv_pis)
           @ &m : res] -
    Pr[Exper(MI(Par2, Adv2), CompEnv(Rest, Env))
         .main(func' ++ [change_pari], in_guard' `|` rest_adv_pis)
           @ &m : res]| <= b =>
  `|Pr[Exper(MI(MakeRFComp(Rest, Par1), Adv1), Env)
         .main(func', in_guard') @ &m : res] -
    Pr[Exper(MI(MakeRFComp(Rest, Par2), Adv2), Env)
         .main(func', in_guard') @ &m : res]| <= b.
proof.
move =>
  ge0_term_rest rest_init rest_invoke
  ge0_term_par1 par1_init par1_invoke
  ge0_term_par2 par2_init par2_invoke
  ep_func' disj_igl'_rest_adv_pis bound_Pars.
rewrite
  (compos_bridge
   Env Adv1 Rest Par1
   invar_rest term_rest
   invar_par1 term_par1
   func' in_guard' &m) //.
by rewrite
  (compos_bridge
   Env Adv2 Rest Par2
   invar_rest term_rest
   invar_par2 term_par2
   func' in_guard' &m).
qed.

end Composition.
