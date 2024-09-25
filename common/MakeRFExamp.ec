(* MakeRFExamp.ec *)

(* example showing workflow of using RealFunctionality.MakeRF and
   associated lemmas about invariants and termination metrics *)

require import UCCore.

op rf_info : rf_info.
axiom rf_info_valid : rf_info_valid rf_info.

clone import RealFunctionality with
  op rf_info <- rf_info
proof*.
realize rf_info_valid. apply rf_info_valid. qed.

type state = [
  | Init
  | Main of int
].

(* a silly core functionality, that doesn't actually do anything
   with messages *)

module MyCore = {
  var st : state

  proc init(self : addr) : unit = {
    st <- Init;
  }

  proc invoke(m : msg) : msg option = {
    var r : msg option;
    match st with
    | Init => {
        st <- Main 2;
        r <- Some m;
      }
    | Main n => {
        if (n = 0) {
          r <- None;
        }
        else {
          st <- Main (n - 1);
          r <- Some m;
        }
      }
    end;
    return r;
  }
}.

op mycore_invar : glob MyCore -> bool =
  fun (g : glob MyCore) =>
    match g with
    | Init   => true
    | Main n => 0 <= n <= 2
    end.

op mycore_metric : glob MyCore -> int =
  fun (g : glob MyCore) =>
    match g with
    | Init   => 3
    | Main n => n
    end.

lemma mycore_metric_good (g : glob MyCore) :
  mycore_invar g => 0 <= mycore_metric g.
proof. smt(). qed.

lemma mycore_init :
  hoare [MyCore.init : true ==> mycore_invar (glob MyCore)].
proof. proc. auto. qed.

lemma mycore_invoke (n : int) :
  hoare
  [MyCore.invoke :
   mycore_invar (glob MyCore) /\ mycore_metric (glob MyCore) = n ==>
   mycore_invar (glob MyCore) /\
   (res <> None => mycore_metric (glob MyCore) < n)].
proof.
proc; match; auto; smt().
qed.

(* now we lift to MakeRF(MyCore) *)

lemma MakeRF_MyCore_init_invar_hoare :
  hoare [MakeRF(MyCore).init : true ==> mycore_invar (glob MyCore)].
proof.
apply (MakeRF_init_invar_hoare MyCore mycore_invar).
apply mycore_init.
qed.

lemma MakeRF_MyCore_invoke_term_metric_hoare (n : int) :
  hoare
  [MakeRF(MyCore).invoke :
   mycore_invar (glob MyCore) /\ mycore_metric (glob MyCore) = n ==>
   mycore_invar (glob MyCore) /\
   (res <> None => mycore_metric (glob MyCore) < n)].
proof.
apply (MakeRF_invoke_term_metric_hoare MyCore mycore_invar mycore_metric).
apply mycore_invoke.
qed.

(* an abbreviation *)

module MyFun = MakeRF(MyCore).

(* now we lift our invariant, termination metric and lemmas to
   MyFun *)

(*
print glob MyFun.

Globals [# = 0]:

Prog. variables [# = 2]:
  MyCore.st : state
  MakeRF.self : addr
*)

op myfun_invar : glob MyFun -> bool =
  fun (g : glob MyFun) => mycore_invar g.`1.

op myfun_metric : glob MyFun -> int =
  fun (g : glob MyFun) => mycore_metric g.`1.

lemma myfun_metric_good (g : glob MyFun) :
  myfun_invar g => 0 <= myfun_metric g.
proof. smt(). qed.

lemma MyFun_init_invar_hoare :
  hoare [MyFun.init : true ==> myfun_invar (glob MyFun)].
proof.
rewrite /myfun_invar /=.
apply MakeRF_MyCore_init_invar_hoare.
qed.

lemma MyFun_invoke_term_metric_hoare (n : int) :
  hoare
  [MyFun.invoke :
   myfun_invar (glob MyFun) /\ myfun_metric (glob MyFun) = n ==>
   myfun_invar (glob MyFun) /\
   (res <> None => myfun_metric (glob MyFun) < n)].
proof.
rewrite /myfun_invar /myfun_metric /=.
apply MakeRF_MyCore_invoke_term_metric_hoare.
qed.
