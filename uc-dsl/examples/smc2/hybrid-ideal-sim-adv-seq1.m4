define(__HybridIdealSimAdvSeq1__,<<<dnl
(* start of m4 generated code from call at line __line__ of
   file __file__ *)
inline{1} 1; inline{2} 1; sp 2 2.
rcondf{2} 1; first auto; smt(@UCListPO).
inline{2} 1; sp 0 3.
rcondt{2} 1; first auto.
rcondt{2} 1; first auto; progress; smt(@UCListPO).
inline{2} 1; sp 0 2.
match => //.
if => //.
sp 2 2.
seq 1 1 :
  (r0{1} = r2{2} /\ ! not_done{1} /\ ! not_done0{2} /\
   ={MI.func, MI.in_guard} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MakeInt.after_adv_to_env func' r0{1} /\
   $1).
exlim r0{1} => r0'.
call{1} (MakeInt.MI_after_adv_to_env Hybrid DummyAdv r0').
call{2} (MSCore.MS_after_adv_return SimCore DummyAdv r0').
auto => />; smt(@UCListPO).
rcondf{1} 1; first auto. rcondf{2} 1; first auto. sp 0 2.
seq 0 1 :
  (={r0} /\ ! not_done{2} /\ ={MI.func, MI.in_guard} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   $1).
exlim r0{2} => r0'.
call{2} (MakeInt.MI_after_adv_to_env IF SimDA r0').
auto.
rcondf{2} 1; first auto.
auto; smt($2).
seq 2 2 :
  (r0{1} = None /\ r2{2} = None /\
   ! not_done{1} /\ ! not_done0{2} /\
   ={MI.func, MI.in_guard} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MakeInt.after_adv_error func' r0{1} /\
   $1).
call{1} (MakeInt.MI_after_adv_error Hybrid DummyAdv).
call{2} (MSCore.MS_after_adv_error SimCore DummyAdv).
auto => />; smt(@UCListPO).
rcondf{1} 1; first auto. rcondf{2} 1; first auto. sp 0 2.
seq 0 1 :
  (={r0} /\ ! not_done{2} /\ ={MI.func, MI.in_guard} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   $1).
call{2} (MakeInt.MI_after_adv_error IF SimDA).
auto; smt().
rcondf{2} 1; first auto.
auto; smt($2).
move => x1 x2.
seq 0 0 :
  (#pre /\ x1 = x2 /\
   m1{1} = 
   (Adv, adv_root_port, env_root_port, TagNoInter,
    (epdp_tuple4_univ epdp_port_univ epdp_int_univ epdp_tag_univ
     epdp_id).`enc (x1.`dfe_pt, x1.`dfe_n, x1.`dfe_tag, x1.`dfe_u))).
auto => />; smt(eq_of_valid_da_from_env).
if => //.
seq 2 2 :
  (r0{1} = r2{2} /\
   r0{1} =
   Some
   (UCBasicTypes.Adv, x1.`dfe_pt, (adv, x1.`dfe_n), x1.`dfe_tag,
    x1.`dfe_u) /\
   ={MI.func, MI.in_guard} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   (MakeInt.after_adv_to_env func' r0{1} \/
    MakeInt.after_adv_to_func func' r0{1}) /\
   $1).
auto; smt().
case (MakeInt.after_adv_to_env func' r0{1}).
seq 1 1 :
  (r0{1} = r2{2} /\ ! not_done{1} /\ ! not_done0{2} /\
   ={MI.func, MI.in_guard} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MakeInt.after_adv_to_env func' r0{1} /\
   $1).
exlim r0{1} => r0'.
call{1} (MakeInt.MI_after_adv_to_env Hybrid DummyAdv r0').
call{2} (MSCore.MS_after_adv_return SimCore DummyAdv r0').
auto; smt().
rcondf{1} 1; first auto. rcondf{2} 1; first auto. sp 0 2.
seq 0 1 :
  (={r0} /\ ! not_done{2} /\  ={MI.func, MI.in_guard} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   $1).
exlim r0{2} => r0'.
call{2} (MakeInt.MI_after_adv_to_env IF SimDA r0').
auto.
rcondf{2} 1; first auto.
auto; smt($2).
seq 0 0 : (#pre /\ MakeInt.after_adv_to_func func' r0{1});
  first auto; smt().
seq 1 1 :
  (m0{1} = m2{2} /\ not_done{1} /\ not_done0{2} /\
   ={MI.func, MI.in_guard} /\
   MI.func{1} = func' /\ MI.in_guard{1} = in_guard' /\
   MakeInt.after_adv_to_func func' (Some m0{1}) /\
   $1).
exlim r0{1} => r0'.
call{1} (MakeInt.MI_after_adv_to_func Hybrid DummyAdv r0').
call{2} (MSCore.MS_after_adv_continue SimCore DummyAdv r0').
auto; progress [-delta];
  smt(MSCore.MI_after_adv_to_func_implies_after_adv_return_if_addr_opt_unset).
rcondt{1} 1; first auto. rcondt{2} 1; first auto.
rcondt{1} 1; first auto; smt().
rcondf{2} 1; first auto; progress; smt(@UCListPO).
inline{1} 1; inline{2} 1; sp 2 2.
rcondf{2} 1; first auto; smt().
(* end of m4 generated code *)
>>>)dnl
