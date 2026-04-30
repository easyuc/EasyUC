(* DDHExamp.ec *)

(* an example of how the reduction in DDH.ec from lazy to
   eager (ordinary) DDH can be used in a security proof *)

require import AllCore.

(* Diffie-Hellman exponents and keys, including generator
   and exponentiation *)
require import KeyExp.

(* module type of protocols *)

module type PROTOCOL = {
  (* initialization - the integer n is the number of steps
     the protocol should carry out before taking no more
     action *)

  proc init(n : int) : unit

  (* steps return keys until they have exceeded the allotted
     number of steps *)

  proc step() : key option
}.

(* an adversary can call the step procedure of a protocol *)

module type ADV (Proto : PROTOCOL) = {
  proc main(n : int) : bool {Proto.step}
}.

(* experiments *)

module Exper(Proto : PROTOCOL, Adv : ADV) = {
  proc main(n : int) : bool = {
    var b : bool;
    Proto.init(n);
    b <@ Adv(Proto).main(n);
    return b;
  }
}.

(* the real protocol *)

type real_state = [
  | RS0 of int
  | RS1 of int & exp
  | RS2 of int & exp & exp
  | RS3 of int & exp & exp
  | RS4
].

module ProtoReal : PROTOCOL = {
  var st : real_state

  proc init(n : int) : unit = {
    st <- RS0 n;
  }

  proc step() : key option = {
    var q : exp;
    var r : key option <- None;
    match st with
    | RS0 n     => {
        if (0 < n) {
          (* Party 1 generates and returns first key,
             we can imagine it's also passed to Party 2;
             we return it to the adversary, because we
             assume the adversary can see network traffic *)
          q <$ dexp;
          st <- RS1 (n - 1) q;
          r <- Some (g ^ q);
        }
        else { st <- RS4; }
      }
    | RS1 n x   => {
        if (0 < n) {
          (* Party 2 generates and returns second key,
             we can imagine it's also passed to Party 1;
             we return it to the adversary, because we
             assume the adversary can see network traffic *)
          q <$ dexp;
          st <- RS2 (n - 1) x q;
          r <- Some (g ^ q);
        }
        else { st <- RS4; }
      }
    | RS2 n x y => {
        if (0 < n) {
          (* Party 2 computes and returns the shared key,
             taking the one given it by Party 1 (g ^ x), and
             raising this to the power y; we return it, as
             if returning it to the UC environment *)
          st <- RS3 (n - 1) x y;
          r <- Some ((g ^ x) ^ y);
        }
        else { st <- RS4; }
      }
    | RS3 n x y => {
        if (0 < n) {
          (* Party 1 computes and returns the shared key,
             taking the one given it by Party 2 (g ^ y), and
             raising this to the power x; wee return it, as
             if returning it to the UC environment *)
          st <- RS4;
          r <- Some ((g ^ y) ^ x);
        }
        else { st <- RS4; }
      }
    | RS4       => { }
    end;
    return r;
  }
}.

(* the ideal protocol *)

type ideal_state = [
  | IS0 of int
  | IS1 of int & exp
  | IS2 of int & exp & exp
  | IS3 of int & exp & exp & exp
  | IS4
].

module ProtoIdeal : PROTOCOL = {
  var st : ideal_state

  proc init(n : int) : unit = {
    st <- IS0 n;
  }

  proc step() : key option = {
    var q : exp;
    var r : key option <- None;
    match st with
    | IS0 n       => {
        if (0 < n) {
          (* Party 1 *)
          q <$ dexp;
          st <- IS1 (n - 1) q;
          r <- Some (g ^ q);
        }
        else { st <- IS4; }
      }
    | IS1 n x     => {
        if (0 < n) {
          (* Party 2 *)
          q <$ dexp;
          st <- IS2 (n - 1) x q;
          r <- Some (g ^ q);
        }
        else { st <- IS4; }
      }
    | IS2 n x y   => {
        if (0 < n) {
          (* Party 2 generates the shared key freshly *)
          q <$ dexp;
          st <- IS3 (n - 1) x y q;
          r <- Some (g ^ q);
        }
        else { st <- IS4; }
      }
    | IS3 n x y z => {
        if (0 < n) {
          (* Party 1 returns the same shared key, which it
             obtained by "magic" *)
          st <- IS4;
          r <- Some (g ^ z);
        }
        else { st <- IS4; }
      }
    | IS4         => { }
    end;
    return r;
  }
}.

(* eager (ordinary) and lazy Decisional Diffie-Hellman assumptions *)

require DDH.

clone include DDH with
  type input <- int,
  type key   <- key,
  type exp   <- exp,
  op ( * )   <- KeyExp.( * ),
  op dexp    <- dexp,
  op g       <- g,
  op (^)     <- KeyExp.(^)
proof *.
realize dexp_ll. apply dexp_ll. qed.
realize dexp_uni. apply dexp_uni. qed.
realize dexp_fu. apply dexp_fu. qed.

(* the constructed DDH oracle adversary used by our reduction

   you can only understand its structure by studying the proof *)

type abs_state = [
  | AS0 of int
  | AS1 of int & key
  | AS2 of int & key & key
  | AS3 of int & key & key & key
  | AS4
].

(* we make a DDH oracle adversary out of an adversary *)

module (DDHOrAdv (Adv : ADV) : DDH_OR_ADV) (Or : DDH_OR) = {
  module Proto : PROTOCOL = {
    var st : abs_state

    proc init(n : int) : unit = {
      st <- AS0 n;
    }

    proc step() : key option = {
      var k : key;
      var r : key option <- None;
      match st with
      | AS0 n       => {
          if (0 < n) {
            k <@ Or.get(One);
            st <- AS1 (n - 1) k;
            r <- Some k;
          }
          else { st <- AS4; }
        }
      | AS1 n x     => {
          if (0 < n) {
            k <@ Or.get(Two);
            st <- AS2 (n - 1) x k;
            r <- Some k;
          }
          else { st <- AS4; }
        }
      | AS2 n x y   => {
          if (0 < n) {
            k <@ Or.get(Three);
            st <- AS3 (n - 1) x y k;
            r <- Some k;
          }
          else { st <- AS4; }
        }
      | AS3 n x y z => {
          if (0 < n) {
            st <- AS4;
            r <- Some z;
          }
          else { st <- AS4; }
        }
      | AS4         => { }
      end;
      return r;
    }
  }

  proc main(n : int) : bool = {
    var b : bool;
    Proto.init(n);
    b <@ Adv(Proto).main(n);
    return b;
  }
}.

(* see the main lemma after the section *)

section.

declare module
  Adv <:
  ADV{-ProtoReal, -ProtoIdeal, -DDHOrAdv, -DDH1_Or, -DDH2_Or, -DDH_Adv_Conv}.

local op x_opt_of_glob_DDH1_Or (g : glob DDH1_Or) : exp option = g.`1.
local op y_opt_of_glob_DDH1_Or (g : glob DDH1_Or) : exp option = g.`2.

local inductive real_invar
      (r_st : real_state, a_st : abs_state, or_st : glob DDH1_Or) =
  | RI0(n : int) of
      (r_st = RS0 n /\ a_st = AS0 n /\
       x_opt_of_glob_DDH1_Or or_st = None /\
       y_opt_of_glob_DDH1_Or or_st = None)
  | RI1(n : int, x1 : exp) of
      (r_st = RS1 n x1 /\ a_st = AS1 n (g ^ x1) /\
       x_opt_of_glob_DDH1_Or or_st = Some x1 /\
       y_opt_of_glob_DDH1_Or or_st = None)
  | RI2(n : int, x1 : exp, x2 : exp) of
      (r_st = RS2 n x1 x2 /\ a_st = AS2 n (g ^ x1) (g ^ x2) /\
       x_opt_of_glob_DDH1_Or or_st = Some x1 /\
       y_opt_of_glob_DDH1_Or or_st = Some x2)
  | RI3(n : int, x1 : exp, x2 : exp) of
      (r_st = RS3 n x1 x2 /\
       a_st = AS3 n (g ^ x1) (g ^ x2) (g ^ (x1 * x2))/\
       x_opt_of_glob_DDH1_Or or_st = Some x1 /\
       y_opt_of_glob_DDH1_Or or_st = Some x2)
  | RI4 of (r_st = RS4 /\ a_st = AS4).

local lemma real_equiv (n' : int) &m :
  Pr[Exper(ProtoReal, Adv).main(n') @ &m : res] =
  Pr[DDH_Or_Game(DDH1_Or, DDHOrAdv(Adv)).main(n') @ &m : res].
proof.
byequiv => //; proc; inline*; wp.
seq 2 5 :
  (={n, glob Adv} /\ ProtoReal.st{1} = RS0 n{1} /\
   DDHOrAdv.Proto.st{2} = AS0 n{2} /\
   DDH1_Or.x_opt{2} = None /\ DDH1_Or.y_opt{2} = None).
auto.
call
  (_ :
   real_invar (glob ProtoReal){1} (glob DDHOrAdv){2} (glob DDH1_Or){2}).
proc.
exlim ProtoReal.st{1}, DDHOrAdv.Proto.st{2}, (glob DDH1_Or){2} =>
  r_st a_st or_st.
(* the "!!" is a hack to make the ambient case be a boolean one *)
case @[ambient] (!! real_invar r_st a_st or_st) =>
  [/= [] | ?]; last exfalso; smt().
(* RI0 *)
move => n'' [#] r_st_eq a_st_eq x_opt_eq y_opt_eq.
sp 1 1.
match RS0 {1} 1; first auto; smt().
match AS0 {2} 1; first auto; smt().
if; first smt().
inline{2} 1.
match One {2} 2; first auto.
rcondt{2} 2; first auto.
swap{2} -1.
auto; smt(RI1).
auto; smt(RI4).
(* RI1 *)
move => n'' x1 [#] r_st_eq a_st_eq x_opt_eq y_opt_eq.
sp 1 1.
match RS1 {1} 1; first auto; smt().
match AS1 {2} 1; first auto; smt().
if; first smt().
inline{2} 1.
match Two {2} 2; first auto.
rcondt{2} 2; first auto.
swap{2} -1.
auto; smt(RI2).
auto; smt(RI4).
(* RI2 *)
move => n'' x1 x2 [#] r_st_eq a_st_eq x_opt_eq y_opt_eq.
sp 1 1.
match RS2 {1} 1; first auto; smt().
match AS2 {2} 1; first auto; smt().
if; first smt().
inline{2} 1.
match Three {2} 2; first auto.
rcondt{2} 2; first auto; smt().
auto; smt(double_exp_gen RI3).
auto; smt(RI4).
(* RI3 *)
move => n'' x1 x2 [#] r_st_eq a_st_eq x_opt_eq y_opt_eq.
sp 1 1.
match RS3 {1} 1; first auto; smt().
match AS3 {2} 1; first auto; smt().
if; first smt().
auto; smt(double_exp_gen mulC RI4).
auto; smt(RI4).
(* RI4 *)
move => [] r_st_eq a_st_eq.
sp 1 1.
match RS4 {1} 1; first auto.
match AS4 {2} 1; first auto.
auto.
auto; smt(RI0).
qed.

local op x_opt_of_glob_DDH2_Or (g : glob DDH2_Or) : exp option = g.`1.
local op y_opt_of_glob_DDH2_Or (g : glob DDH2_Or) : exp option = g.`2.
local op z_opt_of_glob_DDH2_Or (g : glob DDH2_Or) : exp option = g.`3.

local inductive ideal_invar
      (i_st : ideal_state, a_st : abs_state, or_st : glob DDH2_Or) =
  | II0(n : int) of
      (i_st = IS0 n /\ a_st = AS0 n /\
       x_opt_of_glob_DDH2_Or or_st = None /\
       y_opt_of_glob_DDH2_Or or_st = None /\
       z_opt_of_glob_DDH2_Or or_st = None)
  | II1(n : int, x1 : exp) of
      (i_st = IS1 n x1 /\ a_st = AS1 n (g ^ x1) /\
       x_opt_of_glob_DDH2_Or or_st = Some x1 /\
       y_opt_of_glob_DDH2_Or or_st = None /\
       z_opt_of_glob_DDH2_Or or_st = None)
  | II2(n : int, x1 : exp, x2 : exp) of
      (i_st = IS2 n x1 x2 /\ a_st = AS2 n (g ^ x1) (g ^ x2) /\
       x_opt_of_glob_DDH2_Or or_st = Some x1 /\
       y_opt_of_glob_DDH2_Or or_st = Some x2 /\
       z_opt_of_glob_DDH2_Or or_st = None)
  | II3(n : int, x1 : exp, x2 : exp, x3 : exp) of
      (i_st = IS3 n x1 x2 x3 /\
       a_st = AS3 n (g ^ x1) (g ^ x2) (g ^ x3)/\
       x_opt_of_glob_DDH2_Or or_st = Some x1 /\
       y_opt_of_glob_DDH2_Or or_st = Some x2 /\
       z_opt_of_glob_DDH2_Or or_st = Some x3)
  | II4 of (i_st = IS4 /\ a_st = AS4).

local lemma ideal_equiv (n' : int) &m :
  Pr[Exper(ProtoIdeal, Adv).main(n') @ &m : res] =
  Pr[DDH_Or_Game(DDH2_Or, DDHOrAdv(Adv)).main(n') @ &m : res].
proof.
byequiv => //; proc; inline*; wp.
seq 2 6 :
  (={n, glob Adv} /\ ProtoIdeal.st{1} = IS0 n{1} /\
   DDHOrAdv.Proto.st{2} = AS0 n{2} /\
   DDH2_Or.x_opt{2} = None /\ DDH2_Or.y_opt{2} = None /\
   DDH2_Or.z_opt{2} = None).
auto.
call
  (_ :
   ideal_invar (glob ProtoIdeal){1} (glob DDHOrAdv){2} (glob DDH2_Or){2}).
proc.
exlim ProtoIdeal.st{1}, DDHOrAdv.Proto.st{2}, (glob DDH2_Or){2} =>
  i_st a_st or_st.
(* the "!!" is a hack to make the ambient case be a boolean one *)
case @[ambient] (!! ideal_invar i_st a_st or_st) =>
  [/= [] | ?]; last exfalso; smt().
(* II0 *)
move => n'' [#] i_st_eq a_st_eq x_opt_eq y_opt_eq z_opt_eq.
sp 1 1.
match IS0 {1} 1; first auto; smt().
match AS0 {2} 1; first auto; smt().
if; first smt().
inline{2} 1.
match One {2} 2; first auto.
rcondt{2} 2; first auto.
swap{2} -1.
auto; smt(II1).
auto; smt(II4).
(* II1 *)
move => n'' x1 [#] i_st_eq a_st_eq x_opt_eq y_opt_eq z_opt_eq.
sp 1 1.
match IS1 {1} 1; first auto; smt().
match AS1 {2} 1; first auto; smt().
if; first smt().
inline{2} 1.
match Two {2} 2; first auto.
rcondt{2} 2; first auto.
swap{2} -1.
auto; smt(II2).
auto; smt(II4).
(* II2 *)
move => n'' x1 x2 [#] i_st_eq a_st_eq x_opt_eq y_opt_eq z_opt_eq.
sp 1 1.
match IS2 {1} 1; first auto; smt().
match AS2 {2} 1; first auto; smt().
if; first smt().
inline{2} 1.
match Three {2} 2; first auto.
rcondt{2} 2; first auto; smt().
rcondt{2} 2; first auto; smt().
swap{2} 2 -1.
auto; smt(II3).
auto; smt(II4).
(* II3 *)
move => n'' x1 x2 x3 [#] i_st_eq a_st_eq x_opt_eq y_opt_eq z_opt_eq.
sp 1 1.
match IS3 {1} 1; first auto; smt().
match AS3 {2} 1; first auto; smt().
if; first smt().
auto; smt(II4).
auto; smt(II4).
(* II4 *)
move => [] i_st_eq a_st_eq.
sp 1 1.
match IS4 {1} 1; first auto.
match AS4 {2} 1; first auto.
auto.
auto; smt(II0).
qed.

lemma security' (n' : int) &m :
  `|Pr[Exper(ProtoReal, Adv).main(n') @ &m : res] -
    Pr[Exper(ProtoIdeal, Adv).main(n') @ &m : res]| =
  `|Pr[DDH1(DDH_Adv_Conv(DDHOrAdv(Adv))).main(n') @ &m : res] -
    Pr[DDH2(DDH_Adv_Conv(DDHOrAdv(Adv))).main(n') @ &m : res]|.
proof.
by rewrite real_equiv ideal_equiv (Reduction (DDHOrAdv(Adv))).
qed.

end section.

lemma security
      (Adv <:
       ADV{-ProtoReal, -ProtoIdeal, -DDHOrAdv,
           -DDH1_Or, -DDH2_Or, -DDH_Adv_Conv})
      (n : int) &m :
  `|Pr[Exper(ProtoReal, Adv).main(n) @ &m : res] -
    Pr[Exper(ProtoIdeal, Adv).main(n) @ &m : res]| =
  `|Pr[DDH1(DDH_Adv_Conv(DDHOrAdv(Adv))).main(n) @ &m : res] -
    Pr[DDH2(DDH_Adv_Conv(DDHOrAdv(Adv))).main(n) @ &m : res]|.
proof. apply (security' Adv). qed.
