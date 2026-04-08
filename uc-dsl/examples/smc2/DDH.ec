(* DDH.h *)

(* Decisional Diffie-Hellman Assumptions, Eager and Lazy *)

prover quorum=2 ["Z3" "Alt-Ergo"].

require import AllCore Distr FMap PROM.

(*************************** Begin Theory Parameters **************************)

type input.  (* additional input to adversary *)

type key.  (* keys *)

type exp.  (* exponents *)

op ( * ) : exp -> exp -> exp.  (* multiplication *)

op [full uniform lossless] dexp : exp distr.

op g : key.  (* generator *)

op (^) : key -> exp -> key.  (* exponentiation *)

(* more axioms will hold, but this is all we need in this theory *)

(**************************** End Theory Parameters ***************************)

(******************** Decisional Diffie-Hellman Assumption ********************)

(* this is the normal, "eager", DDH assumption, in which the
   exponents are chosen at the beginning of the games

   the two games take in a value of type input, which is passed
   to the adversary *)

(* DDH Adversary *)

module type DDH_ADV = {
  proc main(x : input, k1 k2 k3 : key) : bool
}.

module DDH1 (Adv : DDH_ADV) = {
  proc main(x : input) : bool = {
    var b : bool; var q1, q2 : exp;
    q1 <$ dexp; q2 <$ dexp;
    b <@ Adv.main(x, g ^ q1, g ^ q2, g ^ (q1 * q2));
    return b;
  }
}.
  
module DDH2 (Adv : DDH_ADV) = {
  proc main(x : input) : bool = {
    var b : bool; var q1, q2, q3 : exp;
    q1 <$ dexp; q2 <$ dexp; q3 <$ dexp;
    b <@ Adv.main(x, g ^ q1, g ^ q2 , g ^ q3);
    return b;
  }
}.

(* for all x : input, the *advantage* of a DDH adversary Adv is

   `|Pr[DDH1(Adv).main(x) @ &m : res] - Pr[DDH2(Adv).main(x) @ &m : res]|

   this will be negligible under certain assumptions about key, exp
   and the efficiency of Adv (including that Adv doesn't compute the
   inverse of fun q => g ^ q) *)

(***************** Lazy Decisional Diffie-Hellman Assumption ****************)

(* a "lazy", oracle-based version of the Decisional Diffie-Hellman
   assumption, with two oracles (DDH_Or1 and DDH_Or2) and a single
   game using them

   the exponents are only generated (and cached) by the oracles when
   keys are requested by the adversary

   the third key may only be requested (otherwise witness is returned)
   after the first two have been (in either order) *)

type three = [One | Two | Three].

module type DDH_OR = {
  proc init() : unit         (* initialization *)
  proc get(i : three) : key  (* get on of the three keys *)
}.

module DDH1_Or : DDH_OR = {
  var x_opt : exp option
  var y_opt : exp option

  proc init() : unit = {
    x_opt <- None; y_opt <- None;
  }

  proc get(i : three) : key = {
    var r : key; var x, y : exp;
    match i with
    | One   => {
        if (x_opt = None) {
          x <$ dexp; x_opt <- Some x;
        }
        r <- g ^ oget x_opt;
      }
    | Two   => {
        if (y_opt = None) {
          y <$ dexp; y_opt <- Some y;
        }
        r <- g ^ oget y_opt;
      }
    | Three => {
        (* witness is returned unless both of x and y have
           already been generated *)
        if (x_opt <> None /\ y_opt <> None) {
          r <- g ^ (oget x_opt * oget y_opt);
        }
        else { r <- witness; }
      }
    end;
    return r;
  }
}.

module DDH2_Or : DDH_OR = {
  var x_opt : exp option
  var y_opt : exp option
  var z_opt : exp option

  proc init() : unit = {
    x_opt <- None; y_opt <- None; z_opt <- None;
  }

  proc get(i : three) : key = {
    var r : key; var x, y, z : exp;
    match i with
    | One   => {
        if (x_opt = None) {
          x <$ dexp; x_opt <- Some x;
        }
        r <- g ^ oget x_opt;
      }
    | Two   => {
        if (y_opt = None) {
          y <$ dexp; y_opt <- Some y;
        }
        r <- g ^ oget y_opt;
      }
    | Three => {
        (* witness is returned unless both x and y have
           already been generated *)
        if (x_opt <> None /\ y_opt <> None) {
          if (z_opt = None) {
            z <$ dexp; z_opt <- Some z;
          }
          r <- g ^ oget z_opt;
        }
        else { r <- witness; }
      }
    end;
    return r;
  }
}.

(* module type of DDH oracle adversaries

   the adversary cannot reinitialize the oracle *)

module type DDH_OR_ADV (Or : DDH_OR) = {
  proc main(x : input) : bool {Or.get}
}.

module DDH_Or_Game (Or : DDH_OR, Adv : DDH_OR_ADV) = {
  proc main(x : input) : bool = {
    var b : bool;
    Or.init();
    b <@ Adv(Or).main(x);
    return b;
  }
}.

(* convert a DDH oracle adversary to an ordinary DDH
   adversary *)

module Conv (Adv : DDH_OR_ADV) : DDH_ADV = {
  module Or : DDH_OR = {
    var k1, k2, k3 : key
    var one, two : bool  (* have the first two keys been requested? *)

    proc init() : unit = { }

    proc get(i : three) : key = {
      var r : key;
      match i with
      | One   => { r <- k1; one <- true; }
      | Two   => { r <- k2; two <- true; }
      | Three => {
          (* witness is returned if the first two keys have
             not already been requested *)
          if (one /\ two) { r <- k3; }
          else { r <- witness; }
        }
      end;
      return r;
    }
  }

  proc main(x : input, k1 : key, k2 : key, k3 : key) : bool = {
    var b : bool;
    Or.k1 <- k1; Or.k2 <- k2; Or.k3 <- k3;
    Or.one <- false; Or.two <- false;
    b <@ Adv(Or).main(x);
    return b;
  }
}.

(* skip to the end of the section to see the first main lemma *)
        
section.

declare module Adv <: DDH_OR_ADV{-Conv, -DDH1_Or}.

(* we use eager/lazy sampling - see PROM *)

local clone FullRO with
  type in_t    <- three,
  type out_t   <- exp,
  op dout      <- fun _ => dexp,
  type d_in_t  <- input,
  type d_out_t <- bool
proof *.

local module (RO_Disting1 : FullRO.RO_Distinguisher) (RO : FullRO.RO) = {
  module Or : DDH_OR = {
    var one, two : bool

    proc init() : unit = { }

    proc get(i : three) : key = {
      var r : key; var x, y : exp;
      match i with
      | One   => {
          x <@ RO.get(One); one <- true;
          r <- g ^ x;
        }
      | Two   => {
          y <@ RO.get(Two); two <- true;
          r <- g ^ y;
        }
      | Three => {
          if (one /\ two) {
            x <@ RO.get(One);
            y <@ RO.get(Two);
            r <- g ^ (x * y);
          }
          else { r <- witness; }
        }
      end;
      return r;
    }
  }

  proc distinguish(x : input) : bool = {
    var b : bool;
    Or.one <- false; Or.two <- false;
    (* sample either eagerly or lazily *)
    RO.sample(One); RO.sample(Two);
    b <@ Adv(Or).main(x);
    return b;
  }
}.

local lemma first (x' : input) &m :
  Pr[DDH_Or_Game(DDH1_Or, Adv).main(x') @ &m : res] =
  Pr[FullRO.MainD(RO_Disting1, FullRO.LRO).distinguish(x') @ &m : res].
proof.
byequiv (_ : ={x, glob Adv} ==> _) => //; proc; inline*; wp.
seq 2 6 :
  (={glob Adv} /\ x{1} = x0{2} /\
   DDH1_Or.x_opt{1} = FullRO.RO.m{2}.[One] /\
   DDH1_Or.y_opt{1} = FullRO.RO.m{2}.[Two] /\
   (DDH1_Or.x_opt{1} = None <=> ! RO_Disting1.Or.one{2}) /\
   (DDH1_Or.y_opt{1} = None <=> ! RO_Disting1.Or.two{2})).
auto; smt(emptyE).
call
  (_ : 
   DDH1_Or.x_opt{1} = FullRO.RO.m{2}.[One] /\
   DDH1_Or.y_opt{1} = FullRO.RO.m{2}.[Two] /\
   (DDH1_Or.x_opt{1} = None <=> ! RO_Disting1.Or.one{2}) /\
   (DDH1_Or.y_opt{1} = None <=> ! RO_Disting1.Or.two{2})).
proc; match => //.
inline{2} 1.
case (DDH1_Or.x_opt{1} = None).
rcondt{1} 1; first auto.
rcondt{2} 3; first auto.
swap{2} 2 -1; wp; rnd; auto; smt(get_setE).
rcondf{1} 1; first auto.
rcondf{2} 3; first auto.
swap{2} 2 -1; wp; rnd{2}; auto.
inline{2} 1.
case (DDH1_Or.y_opt{1} = None).
rcondt{1} 1; first auto.
rcondt{2} 3; first auto.
swap{2} 2 -1; wp; rnd; auto; smt(get_setE).
rcondf{1} 1; first auto.
rcondf{2} 3; first auto.
swap{2} 2 -1; wp; rnd{2}; auto.
inline*.
if; first smt().
rcondf{2} 3; first auto.
rcondf{2} 6; first auto.
auto.
auto.
auto.
qed.

local lemma second (x : input) &m :
  Pr[FullRO.MainD(RO_Disting1, FullRO.LRO).distinguish(x) @ &m : res] =
  Pr[FullRO.MainD(RO_Disting1, FullRO.RO).distinguish(x) @ &m : res].
proof.
byequiv
  (_ :
   ={x, glob Adv, RO_Disting1.Or.one, RO_Disting1.Or.two} ==> _) => //.
symmetry.
conseq (FullRO.FullEager.RO_LRO RO_Disting1 _) => //.
smt(dexp_ll).
qed.

local lemma third (x : input) &m :
  Pr[FullRO.MainD(RO_Disting1, FullRO.RO).distinguish(x) @ &m : res] =
  Pr[DDH1(Conv(Adv)).main(x) @ &m : res].
proof.
byequiv (_ : ={x, glob Adv} ==> _) => //; proc; inline*; wp.
rcondt{1} 8; first auto; smt(emptyE).
rcondt{1} 12; first auto; smt(mem_set mem_empty).
swap{1} 7 -6; swap{1} 11 -9.
seq 12 11 :
  (={x0, glob Adv} /\ ={one, two}(RO_Disting1.Or, Conv.Or) /\
   FullRO.RO.m{1} = (empty.[One <- r0{1}]).[Two <- r1{1}] /\
   Conv.Or.k1{2} = g ^ r0{1} /\ Conv.Or.k2{2} = g ^ r1{1} /\
   Conv.Or.k3{2} = g ^ (r0{1} * r1{1})).
wp; rnd; rnd; auto.
exlim r0{1}, r1{1} => r0_L r1_L.
call
  (_ :
   ={one, two}(RO_Disting1.Or, Conv.Or) /\
   FullRO.RO.m{1} = (empty.[One <- r0_L]).[Two <- r1_L] /\
   Conv.Or.k1{2} = g ^ r0_L /\ Conv.Or.k2{2} = g ^ r1_L /\
   Conv.Or.k3{2} = g ^ (r0_L * r1_L)).
proc.
match => //.
inline*.
rcondf{1} 3; first auto; smt(mem_set).
auto; smt(get_setE).
inline*.
rcondf{1} 3; first auto; smt(mem_set).
auto; smt(get_setE).
if => //.
inline*.
rcondf{1} 3; first auto; smt(mem_set).
rcondf{1} 6; first auto; smt(mem_set).
auto; smt(get_setE).
auto.
auto.
qed.

lemma Reduction1' (x : input) &m :
  Pr[DDH_Or_Game(DDH1_Or, Adv).main(x) @ &m : res] =
  Pr[DDH1(Conv(Adv)).main(x) @ &m : res].
proof. by rewrite first second third. qed.

end section.

lemma Reduction1 (Adv <: DDH_OR_ADV{-Conv, -DDH1_Or}) (x : input) &m :
  Pr[DDH_Or_Game(DDH1_Or, Adv).main(x) @ &m : res] =
  Pr[DDH1(Conv(Adv)).main(x) @ &m : res].
proof. by rewrite (Reduction1' Adv). qed.

(* skip to the end of the section to see the second main lemma *)

section.

declare module Adv <: DDH_OR_ADV{-Conv, -DDH2_Or}.

local clone FullRO with
  type in_t    <- three,
  type out_t   <- exp,
  op dout      <- fun _ => dexp,
  type d_in_t  <- input,
  type d_out_t <- bool
proof *.

local module (RO_Disting2 : FullRO.RO_Distinguisher) (RO : FullRO.RO) = {
  module Or : DDH_OR = {
    var one, two : bool

    proc init() : unit = { }

    proc get(i : three) : key = {
      var r : key; var x, y, z : exp;
      match i with
      | One   => {
          x <@ RO.get(One); one <- true;
          r <- g ^ x;
        }
      | Two   => {
          y <@ RO.get(Two); two <- true;
          r <- g ^ y;
        }
      | Three => {
          if (one /\ two) {
            z <@ RO.get(Three);
            r <- g ^ z;
          }
          else { r <- witness; }
        }
      end;
      return r;
    }
  }

  proc distinguish(x : input) : bool = {
    var b : bool;
    Or.one <- false; Or.two <- false;
    (* sample either eagerly or lazily *)
    RO.sample(One); RO.sample(Two); RO.sample(Three);
    b <@ Adv(Or).main(x);
    return b;
  }
}.

local lemma first (x' : input) &m :
  Pr[DDH_Or_Game(DDH2_Or, Adv).main(x') @ &m : res] =
  Pr[FullRO.MainD(RO_Disting2, FullRO.LRO).distinguish(x') @ &m : res].
proof.
byequiv (_ : ={x, glob Adv} ==> _) => //; proc; inline*; wp.
seq 3 7 :
  (={glob Adv} /\ x{1} = x0{2} /\
   DDH2_Or.x_opt{1} = FullRO.RO.m{2}.[One] /\
   DDH2_Or.y_opt{1} = FullRO.RO.m{2}.[Two] /\
   DDH2_Or.z_opt{1} = FullRO.RO.m{2}.[Three] /\
   (DDH2_Or.x_opt{1} = None <=> ! RO_Disting2.Or.one{2}) /\
   (DDH2_Or.y_opt{1} = None <=> ! RO_Disting2.Or.two{2})).
auto; smt(emptyE).
call
  (_ : 
   DDH2_Or.x_opt{1} = FullRO.RO.m{2}.[One] /\
   DDH2_Or.y_opt{1} = FullRO.RO.m{2}.[Two] /\
   DDH2_Or.z_opt{1} = FullRO.RO.m{2}.[Three] /\
   (DDH2_Or.x_opt{1} = None <=> ! RO_Disting2.Or.one{2}) /\
   (DDH2_Or.y_opt{1} = None <=> ! RO_Disting2.Or.two{2})).
proc; match => //.
inline{2} 1.
case (DDH2_Or.x_opt{1} = None).
rcondt{1} 1; first auto.
rcondt{2} 3; first auto.
swap{2} 2 -1; wp; rnd; auto; smt(get_setE).
rcondf{1} 1; first auto.
rcondf{2} 3; first auto.
swap{2} 2 -1; wp; rnd{2}; auto.
inline{2} 1.
case (DDH2_Or.y_opt{1} = None).
rcondt{1} 1; first auto.
rcondt{2} 3; first auto.
swap{2} 2 -1; wp; rnd; auto; smt(get_setE).
rcondf{1} 1; first auto.
rcondf{2} 3; first auto.
swap{2} 2 -1; wp; rnd{2}; auto.
inline*.
if; first smt().
case (DDH2_Or.z_opt{1} = None).
rcondt{1} 1; first auto.
rcondt{2} 3; first auto.
swap{2} 2 -1; wp; rnd.
auto; progress; by rewrite get_setE.
rcondf{1} 1; first auto.
rcondf{2} 3; first auto.
auto.
auto.
auto.
qed.

local lemma second (x : input) &m :
  Pr[FullRO.MainD(RO_Disting2, FullRO.LRO).distinguish(x) @ &m : res] =
  Pr[FullRO.MainD(RO_Disting2, FullRO.RO).distinguish(x) @ &m : res].
proof.
byequiv
  (_ :
   ={x, glob Adv, RO_Disting2.Or.one, RO_Disting2.Or.two} ==> _) => //.
symmetry.
conseq (FullRO.FullEager.RO_LRO RO_Disting2 _) => //.
smt(dexp_ll).
qed.

local lemma third (x : input) &m :
  Pr[FullRO.MainD(RO_Disting2, FullRO.RO).distinguish(x) @ &m : res] =
  Pr[DDH2(Conv(Adv)).main(x) @ &m : res].
proof.
byequiv (_ : ={x, glob Adv} ==> _) => //; proc; inline*; wp.
rcondt{1} 8; first auto; smt(emptyE).
rcondt{1} 12; first auto; smt(mem_set mem_empty).
rcondt{1} 16; first auto; smt(mem_set mem_empty).
swap{1} 7 -6; swap{1} 11 -9; swap{1} 15 -12.
seq 16 12 :
  (={x0, glob Adv} /\ ={one, two}(RO_Disting2.Or, Conv.Or) /\
   FullRO.RO.m{1} =
   ((empty.[One <- r0{1}]).[Two <- r1{1}]).[Three <- r2{1}] /\
   Conv.Or.k1{2} = g ^ r0{1} /\ Conv.Or.k2{2} = g ^ r1{1} /\
   Conv.Or.k3{2} = g ^ r2{1}).
wp; rnd; rnd; rnd; auto.
exlim r0{1}, r1{1}, r2{1} => r0_L r1_L r2_L.
call
  (_ :
   ={one, two}(RO_Disting2.Or, Conv.Or) /\
   FullRO.RO.m{1} =
   ((empty.[One <- r0_L]).[Two <- r1_L]).[Three <- r2_L] /\
   Conv.Or.k1{2} = g ^ r0_L /\ Conv.Or.k2{2} = g ^ r1_L /\
   Conv.Or.k3{2} = g ^ r2_L).
proc; match => //.
inline*.
rcondf{1} 3; first auto; smt(mem_set).
auto; smt(get_setE).
inline*.
rcondf{1} 3; first auto; smt(mem_set).
auto; smt(get_setE).
if => //.
inline*.
rcondf{1} 3; first auto; smt(mem_set).
auto; smt(get_setE).
auto.
auto.
qed.

lemma Reduction2' (x : input) &m :
  Pr[DDH_Or_Game(DDH2_Or, Adv).main(x) @ &m : res] =
  Pr[DDH2(Conv(Adv)).main(x) @ &m : res].
proof. by rewrite first second third. qed.

end section.

lemma Reduction2 (Adv <: DDH_OR_ADV{-Conv, -DDH2_Or})
                 (x : input) &m :
  Pr[DDH_Or_Game(DDH2_Or, Adv).main(x) @ &m : res] =
  Pr[DDH2(Conv(Adv)).main(x) @ &m : res].
proof. by rewrite (Reduction2' Adv). qed.

(* our main result, reducing lazy decisional Diffie-Hellman
   to ordinary (eager) decisional Diffie-Hellman *)

lemma Reduction (Adv <: DDH_OR_ADV{-Conv, -DDH1_Or, -DDH2_Or})
                (x : input) &m :
  `|Pr[DDH_Or_Game(DDH1_Or, Adv).main(x) @ &m : res] -
    Pr[DDH_Or_Game(DDH2_Or, Adv).main(x) @ &m : res]| =
  `|Pr[DDH1(Conv(Adv)).main(x) @ &m : res] -
    Pr[DDH2(Conv(Adv)).main(x) @ &m : res]|.
proof. by rewrite (Reduction1 Adv) (Reduction2 Adv). qed.
