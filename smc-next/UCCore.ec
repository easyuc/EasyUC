(* UCCore.eca *)

prover quorum=2 ["Alt-Ergo" "Z3"].

(* Core UC Definitions and Lemmas *)

require import AllCore List FSet ListPO Encoding.

(* real protocols and ideal functionalities (collectively,
   "functionalities") have hierarchical addresses

   if a functionality has address alpha, it is also responsible for all
   sub-functionalities with addresses beta >= alpha (in the prefix
   partial ordering of ListPO)

   adversaries are also modeled as functionalities - but with no
   subaddresses/sub-functionalties; simulators are functionalities
   parameterized by adversaries *)

type addr = int list.

(* ports - pairs of functionality addresses and port indices

   a functionality's ports are used/interpreted however the
   functionality chooses, but typically they are divided into
   different parties

   adversaries can handle multiple port indices, and each simulator
   has a single port index *)

type port = addr * int.

(* messages have modes:

     * direct - supplying functionality inputs, consuming their
         outputs

     * adversarial - communication between functionalties and
         adversaries/simulators, communication between different
         adversaries/simulators, and communication between
         environments and adversaries/simulators *)

type mode = [
    Dir  (* direct *)
  | Adv  (* adversarial *)
].

lemma not_dir (mod : mode) :
  mod <> Dir <=> mod = Adv.
proof. by case mod. qed.

lemma not_adv (mod : mode) :
  mod <> Adv <=> mod = Dir.
proof. by case mod. qed.

(* begin theory parameters *)

type univ.  (* universe of values *)

(* universe encoding/decoding operators - more can be added by
   other theories *)

(* univ encoding: port * int * univ *)

clone EPDP as EPDP_Univ_PortIntUniv with
  type orig <- port * int * univ,
  type enc  <- univ.

(* end theory parameters *)

(* a message has the form (mod, pt1, pt2, u), for a mode mod, a
   destination port pt1, a source port pt2, and a universe
   value u *)

type msg = mode * port * port * univ.

(* guard an optional message using predicate *)

op opt_msg_guard :
     (mode -> addr -> int -> addr -> int -> univ -> bool) ->
     msg option -> msg option =
     fun f : mode -> addr -> int -> addr -> int -> univ -> bool =>
     fun m_opt : msg option =>
       match m_opt with
         None   => None
       | Some m =>
           if f m.`1 m.`2.`1 m.`2.`2 m.`3.`1 m.`3.`2 m.`4
           then m_opt
           else None
       end.

(* module type used for real protocols and ideal functionalities
   (collectively, "functionalities"), as well as adversaries and
   simulators *)

pred func_init_pre (self adv : addr) = inc self adv.

module type FUNC = {
  (* initialize functionality (or adversary), telling it its address
     (self) and the address of its adversary (adv)

     in the case of the adversary, the second argument will be [], the
     root address of the environment (so the adversary's "adversary" is
     the environment)

     precondition for ordinary (non-adversary) functionalties:
     func_init_pre self adv *)

  proc init(self adv : addr) : unit

  (* respond to an incoming message, producing an optional
     outgoing message (None means error)

     messages to a functionality should have addresses that are >=
     self (in the case of an adversary, = self)

     if Some m' is returned, then the destination address of m' should
     not be >= self, and the source address of m' should be >= self
     (in the case of an adversary, the source address should be =
     self) *)

  proc invoke(m : msg) : msg option
}.

(* module type of interfaces (to environment): consists of
   a functionality part and an adversary part *)

pred inter_init_pre (func adv : addr) = inc func adv.

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

  (* respond to an incoming message, producing an optional
     outgoing message (None means error)

     messages whose destination addresses aren't either >= the
     interface's functionality part's address, func, or *equal* to the
     interface's adversary part's addresss, adv, should result in None
     being returned

     all incoming messages with mode Dir must be addressed to the
     interface's functionality part (else None is returned); all
     incoming messages with mode Adv must be addressed to the
     interface's adversary part (else None is returned)

     if the interface's functionality part returns a message with
     destination address >= func, or if the interface's adversary part
     returns a message with destination address >= adv, then
     None should be returned

     if the interface's functionality part returns a message with
     source address not >= func, or if the interface's adversary part
     returns a message with source address <> adv, then None should be
     returned

     all outgoing messages with mode Dir come from the interface's
     functionality part; all outgoing messages with mode Adv come from
     the interface's adversary part

     the standard (Adv mode) channel between the environment and the
     interface's adversary part consists of messages between port
     ([], 0) (in the environment) and port (adv, 0) (in the
     interface's adversary part)

     the environment may communicate with other port indices of the
     interface's adversary part, except that such a communication will
     result in an error if its destination port isn't of the form
     (adv, n) for some n in in_guard

     if the interface's functionality part sends a message to the
     interface's adversary port (destination address must be = adv),
     this message must have mode Adv, and it may not have destination
     port (adv, 0)

     if the interface's adversary port sends a message to the
     interface's functionality part, this message must have mode
     Adv *)

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

     the standard (Adv mode) channel between the environment and the
     interface's adversary part consists of messages between port
     ([], 0) (in the environment) and port (adv, 0) (in the
     interface's adversary part)

     the environment may communicate with other ports of the
     interface's adversary part, except that such a communication will
     result in an error if its destination port isn't of the form
     (adv, n) for some n in in_guard

     precondition : env_pre func adv *)

  proc main(func adv : addr, in_guard : int fset) : bool {Inter.invoke}
}.

(* carry out experiment in which the environment is allowed to
   interact with, and issue a final boolean judgment about, an
   interface, which is first initialized *)

pred exper_pre (func adv : addr) = inter_init_pre func adv.

lemma exper_pre_ext1 (func adv ext : addr) :
  exper_pre func adv => exper_pre (func ++ ext) adv.
proof.
rewrite /exper_pre /inter_init_pre.
move => |> inc_fun_adv.
by apply inc_ext1.
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

(* make interface out of functionality and adversary parts *)

abstract theory MakeInterface.

module MI (Func : FUNC, Adv : FUNC) : INTER = {
  var func, adv : addr
  var in_guard : int fset

  proc init(func_ adv_ : addr, in_guard_ : int fset) : unit = {
    func <- func_; adv <- adv_; in_guard <- in_guard_;
    Func.init(func, adv);
    Adv.init(adv, []);
  }

  proc loop(m : msg) : msg option = {
    var r : msg option <- None;
    var not_done : bool <- true;

    (* loop invariant in terms of m:

         not_done =>
         func <= m.`2.`1 \/
         m.`1 = Adv /\ m.`2.`1 = adv *)

    while (not_done) {
      if (func <= m.`2.`1) {
        r <@ Func.invoke(m);
        if (r = None) {
          not_done <- false;
        }
        else {
          m <- oget r;  (* next iteration, if any, will use m *)
          if (func <= m.`2.`1 \/ ! func <= m.`3.`1) {
            r <- None; not_done <- false;
          }
          elif (m.`1 = Dir) {
            not_done <- false;
            if (adv <= m.`2.`1) {
              r <- None;
            }
          }
          elif (m.`2.`1 <> adv \/ m.`2.`2 = 0) {
            r <- None; not_done <- false;
          }
        }          
      }
      else {  (* m.`1 = Adv /\ m.`2.`1 = adv *)
        r <@ Adv.invoke(m);
        if (r = None) {
          not_done <- false;
        }
        else {
          m <- oget r;  (* next iteration, if any, will use m *)
          if (m.`1 = Dir \/ adv <= m.`2.`1 \/ ! adv <> m.`3.`1) {
            r <- None; not_done <- false;
          }
          elif (! func <= m.`2.`1) {
            not_done <- false;
          }
        }
      }      
    }
    return r;
  }

  proc invoke(m : msg) : msg option = {
    var r : msg option;
    if ((m.`1 = Dir /\ func <= m.`2.`1 \/
         m.`1 = Adv /\ m.`2.`1 = adv /\
         (m.`2.`2 = 0 \/ m.`2.`2 \in in_guard)) /\
        ! func <= m.`3.`1 /\ ! adv <= m.`3.`1) {
      r <@ loop(m);
    }
    else {
      r <- None;
    }
    return r;
  }
}.

end MakeInterface.

(* dummy adversary (DA) - completely controlled by environment *)

abstract theory DummyAdversary.

(* message from port ([], 0) of environment to port (dfe_da, 0) of
   dummy adversary, instructing dummy adversary to send message (Adv,
   dfe_pt, (dfe_da, dfe_n), dfe_u); dfa_n should not be 0, and
   dfe_pt should not be [] or be >= address of DA *)

type da_from_env =
  {dfe_da : addr;   (* address of dummy adversary *)
   (* data: *)
   dfe_pt : port;   (* destination port of message to be sent by DA *)
   dfe_n  : int;    (* source port index of message to be sent by DA *)
   dfe_u  : univ}.  (* value of message to be sent by DA *)

op da_from_env (x : da_from_env) : msg =
     (Adv, (x.`dfe_da, 0), ([], 0),
      EPDP_Univ_PortIntUniv.enc (x.`dfe_pt, x.`dfe_n, x.`dfe_u)).

op dec_da_from_env (m : msg) : da_from_env option =
     let (mod, pt1, pt2, v) = m
     in (mod = Dir \/ pt1.`2 <> 0 \/ pt2 <> ([], 0) \/
         ! EPDP_Univ_PortIntUniv.valid v) ?
        None :
        let (pt, n, u) = oget (EPDP_Univ_PortIntUniv.dec v)
        in Some {|dfe_da = pt1.`1; dfe_pt = pt; dfe_n = n; dfe_u = u|}.

lemma epdp_da_from_env : epdp da_from_env dec_da_from_env.
proof.
apply epdp_intro.
move => x.
rewrite /da_from_env /dec_da_from_env /= EPDP_Univ_PortIntUniv.valid_enc
        /= EPDP_Univ_PortIntUniv.enc_dec oget_some /#.
move => [mod pt1 pt2 u] v.
rewrite /da_from_env /dec_da_from_env /=.
case (mod = Dir \/ pt1.`2 <> 0 \/ pt2 <> ([], 0) \/
      ! (EPDP_Univ_PortIntUniv.valid u)) => //.
rewrite !negb_or /= not_dir => [#] -> pt1_2 -> val_u.
have [] t : exists (t : port * int * univ), EPDP_Univ_PortIntUniv.dec u = Some t.
  exists (oget (EPDP_Univ_PortIntUniv.dec u)); by rewrite -some_oget.
move => /EPDP_Univ_PortIntUniv.dec_enc <-.
rewrite EPDP_Univ_PortIntUniv.enc_dec oget_some /#.
qed.

lemma dest_valid_da_from_env (m : msg) :
  dec2valid dec_da_from_env m =>
  m.`2.`1 = (oget (dec_da_from_env m)).`dfe_da /\ m.`2.`2 = 0.
proof.
move => val_m.
have [] x : exists (x : da_from_env), dec_da_from_env m = Some x.
  exists (oget (dec_da_from_env m)); by rewrite -some_oget.
case x => x1 x2 x3 x4.
move => /(epdp_dec_enc _ _ _ _ epdp_da_from_env) <-.
by rewrite (epdp_enc_dec _ _ _ epdp_da_from_env).
qed.

lemma source_valid_da_from_env (m : msg) :
  dec2valid dec_da_from_env m => m.`3 = ([], 0).
proof.
move => val_m.
have [] x : exists (x : da_from_env), dec_da_from_env m = Some x.
  exists (oget (dec_da_from_env m)); by rewrite -some_oget.
case x => x1 x2 x3 x4.
move => /(epdp_dec_enc _ _ _ _ epdp_da_from_env) => <- //.
qed.

(* message from port (da, 0) of dummy adversary to port ([], 0) of
   environment, telling environment that dummy adversary received
   message (Adv, (da, n), pt, u) *)

type da_to_env =
  {dte_da : addr;   (* address of dummy adversary *)
   (* data: *)
   dte_pt : port;   (* source port of message sent to DA *)
   dte_n  : int;    (* destination port index of message sent to DA *)
   dte_u  : univ}.  (* value of message sent to DA *)

op da_to_env (x : da_to_env) : msg =
     (Adv, ([], 0), (x.`dte_da, 0), 
      EPDP_Univ_PortIntUniv.enc(x.`dte_pt, x.`dte_n, x.`dte_u)).

op dec_da_to_env (m : msg) : da_to_env option =
     let (mod, pt1, pt2, v) = m
     in (mod = Dir \/ pt1 <> ([], 0) \/ pt2.`2 <> 0 \/
         ! EPDP_Univ_PortIntUniv.valid v) ?
        None :
        let (pt, n, u) = oget (EPDP_Univ_PortIntUniv.dec v)
        in Some {|dte_da = pt2.`1; dte_pt = pt; dte_n = n; dte_u = u|}.

lemma epdp_da_to_env : epdp da_to_env dec_da_to_env.
proof.
apply epdp_intro.
move => x.
rewrite /da_to_env /dec_da_to_env /= EPDP_Univ_PortIntUniv.valid_enc
        /= EPDP_Univ_PortIntUniv.enc_dec oget_some /#.
move => [mod pt1 pt2 u] v.
rewrite /da_to_env /dec_da_to_env /=.
case (mod = Dir \/ pt1 <> ([], 0) \/ pt2.`2 <> 0 \/
      ! (EPDP_Univ_PortIntUniv.valid u)) => //.
rewrite !negb_or /= not_dir => [#] -> -> pt2_2 val_u.
have [] t : exists (t : port * int * univ), EPDP_Univ_PortIntUniv.dec u = Some t.
  exists (oget (EPDP_Univ_PortIntUniv.dec u)); by rewrite -some_oget.
move => /EPDP_Univ_PortIntUniv.dec_enc <-.
rewrite EPDP_Univ_PortIntUniv.enc_dec oget_some /#.
qed.

lemma dest_valid_da_to_env (m : msg) :
  dec2valid dec_da_to_env m =>
  m.`3.`1 = (oget (dec_da_to_env m)).`dte_da /\ m.`3.`2 = 0.
proof.
move => val_m.
have [] x : exists (x : da_to_env), dec_da_to_env m = Some x.
  exists (oget (dec_da_to_env m)); by rewrite -some_oget.
case x => x1 x2 x3 x4.
move => /(epdp_dec_enc _ _ _ _ epdp_da_to_env) <-.
by rewrite (epdp_enc_dec _ _ _ epdp_da_to_env).
qed.

lemma source_valid_da_to_env (m : msg) :
  dec2valid dec_da_to_env m => m.`2 = ([], 0).
proof.
move => val_m.
have [] x : exists (x : da_to_env), dec_da_to_env m = Some x.
  exists (oget (dec_da_to_env m)); by rewrite -some_oget.
case x => x1 x2 x3 x4.
move => /(epdp_dec_enc _ _ _ _ epdp_da_to_env) => <- //.
qed.

module DummyAdv : FUNC = {
  var self, env : addr

  proc init(self_ env_ : addr) = {
    self <- self_; env <- env_;
  }

  proc invoke(m : msg) : msg option = {
    var r : msg option <- None;

    match (dec_da_from_env m) with
      Some x => {  (* message from ([], 0); m.`2.`2 = 0 *)
        if (x.`dfe_da = self /\ x.`dfe_n <> 0 /\
            x.`dfe_pt.`1 <> [] /\ !self <= x.`dfe_pt.`1 ) {
          r <- Some (Adv, x.`dfe_pt, (self, x.`dfe_n), x.`dfe_u);
        }
      }
    | None   => {
        (* message from functionality; we should have
           m.`1 = Adv /\ m.`2.`1 = self /\ m.`2.`2 <> 0 /\
           ! self <= m.`3.`1 *)
        r <-
          Some
          (da_to_env
           {|dte_da = self; dte_pt = m.`3; dte_n = m.`2.`2;
             dte_u = m.`4|});
      }
    end;
    return r;
  }
}.

end DummyAdversary.
