(* Diffie Hellman Key Exchange in a Universal Composability (UC)
   Style *)

(************************** Import Standard Theories **************************)

require import AllCore List FSet NewFMap Distr DBool.

(*********** Maps Whose Domains Have Exactly Two Distinct elements ************)

pred two_fmap (mp : ('a, 'b)fmap, x y : 'a) =
  x <> y /\
  dom mp = fset0 `|` fset1 x `|` fset1 y.

op two_fmap_init (x y : 'a, u v : 'b) = map0.[x <- u].[y <- v].

lemma two_fmap_init (x y : 'a, u v : 'b) :
  x <> y => two_fmap (two_fmap_init x y u v) x y.
proof.
move => ne_xy.
by rewrite /two_fmap /two_fmap_init 2!dom_set dom0.
qed.

lemma two_fmap_update (mp : ('a, 'b)fmap, x y z : 'a, u : 'b) :
  two_fmap mp x y => (z = x \/ z = y) =>
  two_fmap (mp.[z <- u]) x y.
proof.
move => two_mp_xy z_eq_x_or_y; rewrite /two.
split; first smt().
rewrite dom_set fsetP => w; smt(in_fsetU in_fset1).
qed.

lemma two_fmap_get1 (mp : ('a, 'b)fmap, x y : 'a) :
  two_fmap mp x y => mp.[x] = Some(oget mp.[x]).
proof.
move => [ne_xy dom_mp_xy].
rewrite get_oget.
rewrite dom_mp_xy; smt(in_fsetU in_fset1).
by rewrite oget_some.
qed.

lemma two_fmap_get2 (mp : ('a, 'b)fmap, x y : 'a) :
  two_fmap mp x y => mp.[y] = Some(oget mp.[y]).
proof.
move => [ne_xy dom_mp_xy].
rewrite get_oget.
rewrite dom_mp_xy; smt(in_fsetU in_fset1).
by rewrite oget_some.
qed.

lemma two_fmap_init_get1 (x y : 'a, u v : 'b) :
  x <> y => oget(two_fmap_init x y u v).[x] = u.
proof.
move => ne_xy.
by rewrite /two_fmap_init set_set ne_xy /= getP_eq oget_some.
qed.

lemma two_fmap_init_get2 (x y : 'a, u v : 'b) :
  x <> y => oget(two_fmap_init x y u v).[y] = v.
proof.
move => ne_xy.
by rewrite /two_fmap_init getP_eq oget_some.
qed.

(******** Finite Type Exp (Exponent) Plus Uniform/Lossless Distribution *******)

type exp.

op exp_distr : exp distr.

axiom exp_distr_uni : is_uniform exp_distr.

axiom exp_distr_ll : is_lossless exp_distr.

(********** Keys Uniquely Formed From Generator Using Exponentiation **********)

type key.

op g : key.

op (^) : key -> exp -> key.

axiom gen_surj (k : key) : exists (x : exp), g ^ x = k.

axiom gen_inj (x y : exp) : g ^ x = g ^ y => x = y.

axiom pow_pow_comm (k : key) (x y : exp) :
  k ^ x ^ y = k ^ y ^ x.

(******************** Decisional Diffie-Hellman Assumption ********************)

(* DDH Adversary *)

module type DDH_ADV = {
  proc * main(k1 k2 k3 : key) : bool
}.

module DDH1(Adv : DDH_ADV) = {
  proc main() : bool = {
    var b : bool; var x, y : exp;
    x <$ exp_distr; y <$ exp_distr;
    b <@ Adv.main(g ^ x, g ^ y , g ^ x ^ y);
    return b;
  }
}.
  
module DDH2(Adv : DDH_ADV) = {
  proc main() : bool = {
    var b : bool; var x, y, z : exp;
    x <$ exp_distr; y <$ exp_distr; z <$ exp_distr;
    b <@ Adv.main(g ^ x, g ^ y , g ^ z);
    return b;
  }
}.

(* informally, we assume that exp/key and associated operations are
   such that, assuming Adv : DDH_ADV is probabilistic polynomial time,

   `|Pr[DDH1(Adv).main() @ &m : res] - Pr[DDH2(Adv).main() @ &m : res]|

   is negligible *)

(************************** Machine Identities (IDs) **************************)

(* by convention, 0 is the ID of the Environment *)

type id = int.

(****************** Universe Of Values Exchanged By Machines ******************)

type univ = [
    UnivUnit
  | UnivID   of id
  | UnivKey  of key
  | UnivPair of (univ * univ)
].

(* universe decoding functions *)

op dec_univ_id (v : univ) : id option =
  with v = UnivUnit   => None
  with v = UnivID id  => Some id
  with v = UnivKey _  => None
  with v = UnivPair _ => None.

op is_univ_id (v : univ) : bool = dec_univ_id v <> None.

op dec_univ_key (v : univ) : key option =
  with v = UnivUnit   => None
  with v = UnivID _   => None
  with v = UnivKey k  => Some k
  with v = UnivPair _ => None.

op is_univ_key (v : univ) : bool = dec_univ_key v <> None.

op dec_univ_pair (v : univ) : (univ * univ)option =
  with v = UnivUnit   => None
  with v = UnivID _   => None
  with v = UnivKey _  => None
  with v = UnivPair p => Some p.

op is_univ_pair (v : univ) : bool = dec_univ_pair v <> None.

(****************** Higher-level Universe Encoding/decoding *******************)

op enc_univ_pair_id (id : id, u : univ) : univ = UnivPair(UnivID id, u).

op dec_univ_pair_id (v : univ) : (id * univ)option =
  (dec_univ_pair v = None) ?
  None :
  let (w, u) = oget(dec_univ_pair v)
  in (dec_univ_id w = None) ?
     None : Some(oget(dec_univ_id w), u).

op is_univ_pair_id (v : univ) : bool = dec_univ_pair_id v <> None.

lemma univ_pair_id_enc_dec id u :
  dec_univ_pair_id(enc_univ_pair_id id u) =
  Some(id, u).
proof. trivial. qed.

lemma is_univ_pair_id (id : id, u : univ) :
  is_univ_pair_id(enc_univ_pair_id id u).
proof. trivial. qed.

op enc_univ_pair_id_key (id : id, k : key) : univ =
  enc_univ_pair_id id (UnivKey k).

op dec_univ_pair_id_key (v : univ) : (id * key)option =
  (dec_univ_pair_id v = None) ?
  None :
  let (id, u) = oget(dec_univ_pair_id v)
  in (dec_univ_key u = None) ?
     None :
     Some(id, oget(dec_univ_key u)).

op is_univ_pair_id_key (v : univ) : bool = dec_univ_pair_id_key v <> None.

lemma univ_pair_id_key_enc_dec (id : id, k : key) :
  dec_univ_pair_id_key(enc_univ_pair_id_key id k) =
  Some(id, k).
proof.
by rewrite /enc_univ_pair_id_key /dec_univ_pair_id_key
           univ_pair_id_enc_dec.
qed.

lemma is_univ_pair_id_key (id : id, k : key) :
  is_univ_pair_id_key(enc_univ_pair_id_key id k).
proof.
by rewrite /is_univ_pair_id_key univ_pair_id_key_enc_dec.
qed.

(****************************** Machine Actions *******************************)

(* ActSend(id, v) means to send v to machine id

   ActCall(id1, id2, v) means to call machine id1 with
   v, saying that id2 is the ID of the calling machine

   ActReturn(id, v) means to return v to machine id *)

type act = [
    ActSend   of (id * univ)
  | ActCall   of (id * id * univ)
  | ActReturn of (id * univ)
].
  
(* default action: send nothing to Environment *)

op act_def : act = ActSend(0, UnivUnit).

(* action decoding functions *)

op dec_act_send (a : act) : (id * univ)option =
  with a = ActSend x   => Some x
  with a = ActCall _   => None
  with a = ActReturn _ => None.  

op is_act_send (a : act) : bool = dec_act_send a <> None.

lemma is_act_send_elim (a : act) :
  is_act_send a =>
  exists (id : id, v : univ), a = ActSend(id, v).
proof.
case a => //; move => [id v]; by exists id v.
qed.

op dec_act_call (a : act) : (id * id * univ)option =
  with a = ActSend _   => None
  with a = ActCall x   => Some x
  with a = ActReturn _ => None.

op is_act_call (a : act) : bool = dec_act_call a <> None.

lemma is_act_call_elim (a : act) :
  is_act_call a =>
  exists (id id' : id, v : univ), a = ActCall(id, id', v).
proof.
case a => //; move => [id id' v] _; by exists id id' v.
qed.

op dec_act_return (a : act) : (id * univ)option =
  with a = ActSend _   => None
  with a = ActCall _   => None
  with a = ActReturn x => Some x.

op is_act_return (a : act) : bool = dec_act_return a <> None.

lemma is_act_return_elim (a : act) :
  is_act_return a =>
  exists (id : id, v : univ), a = ActReturn(id, v).
proof.
case a => //; move => [id v] _; by exists id v.
qed.

(* test if action's target is id *)

op act_for_id (id : id, a : act) : bool =
  with a = ActSend x   => x.`1 = id
  with a = ActCall x   => x.`1 = id
  with a = ActReturn x => x.`1 = id.

lemma act_for_id_send (id : id, a : act) :
  act_for_id id a => is_act_send a =>
  (oget(dec_act_send a)).`1 = id.
proof.
case a => //; smt().
qed.

lemma act_for_id_call (id : id, a : act) :
  act_for_id id a => is_act_call a =>
  (oget(dec_act_call a)).`1 = id.
proof.
case a => //; smt().
qed.

lemma act_for_id_return (id : id, a : act) :
  act_for_id id a => is_act_return a =>
  (oget(dec_act_return a)).`1 = id.
proof.
case a => //; smt().
qed.

lemma act_for_id_exclusive (id id' : id, a : act) :
  id <> id' => act_for_id id a => ! act_for_id id' a.
proof.
move => ne_id_id'; by case a.
qed.

(* test if action's target is in range *)

op act_for_id_range (id1 id2 : id, a : act) : bool =
  with a = ActSend x   => id1 <= x.`1 <= id2
  with a = ActCall x   => id1 <= x.`1 <= id2
  with a = ActReturn x => id1 <= x.`1 <= id2.

lemma act_for_id_range_send (id1 id2 : id, a : act) :
  act_for_id_range id1 id2 a => is_act_send a =>
  id1 <= (oget(dec_act_send a)).`1 <= id2.
proof.
case a.
move => [id v]; by rewrite /= oget_some.
smt().
smt().
qed.

lemma act_for_id_range_call (id1 id2 : id, a : act) :
  act_for_id_range id1 id2 a => is_act_call a =>
  id1 <= (oget(dec_act_call a)).`1 <= id2.
proof.
case a.
smt().
move => [id id' v]; by rewrite /= oget_some.
smt().
qed.

lemma act_for_id_range_return (id1 id2 : id, a : act) :
  act_for_id_range id1 id2 a => is_act_return a =>
  id1 <= (oget(dec_act_return a)).`1 <= id2.
proof.
case a.
smt().
smt().
move => [id' v]; by rewrite /= oget_some.
qed.

(******************* Higher Level Action Encoding/Decoding ********************)

op enc_act_call_unit (id id' : id) : act = ActCall(id, id', UnivUnit).

op dec_act_call_unit (a : act) : (id * id)option =
  (dec_act_call a = None) ?
  None :
  let (id, id', u) = oget(dec_act_call a)
  in (u <> UnivUnit) ? None : Some(id, id').

op is_act_call_unit (a : act) : bool = dec_act_call_unit a <> None.

lemma act_call_unit_enc_dec (id id' : id) :
  dec_act_call_unit(enc_act_call_unit id id') = Some(id, id').
proof. trivial. qed.

lemma is_act_call_unit (id id' : id) :
  is_act_call_unit(enc_act_call_unit id id').
proof. trivial. qed.

lemma is_act_call_unit_up (a : act) :
  is_act_call_unit a => is_act_call a.
proof. smt(). qed.

lemma is_act_call_unit_elim (a : act) :
  is_act_call_unit a =>
  exists (id id' : id), a = ActCall(id, id', UnivUnit).
proof.
move => call_unit.
have [id id' v] ->> := is_act_call_elim a _.
  by apply is_act_call_unit_up.
exists id id'; move : call_unit.
case (v = UnivUnit) => // ne_v_unit.
by rewrite /is_act_call_unit /dec_act_call_unit /= oget_some /= ne_v_unit.
qed.

lemma dec_act_call_unit_up1 (a : act) :
  is_act_call_unit a =>
  (oget(dec_act_call_unit a)).`1 = (oget(dec_act_call a)).`1.
proof.
case a.
move => [id v]; smt().
move => [id id' v].
rewrite /= oget_some /= /is_act_call_unit /dec_act_call_unit
        /= oget_some /=.
by case (v <> UnivUnit).
move => [id v]; smt().
qed.

lemma dec_act_call_unit_up2 (a : act) :
  is_act_call_unit a =>
  (oget(dec_act_call_unit a)).`2 = (oget(dec_act_call a)).`2.
proof.
elim a.
move => [id v]; smt().
move => [id id' v].
rewrite /= oget_some /= /is_act_call_unit /dec_act_call_unit
        /= oget_some /=.
by case (v <> UnivUnit).
move => [id v]; smt().
qed.

op enc_act_call_pair_id (id id' id'' : id, u : univ) : act =
  ActCall(id, id', enc_univ_pair_id id'' u).

op dec_act_call_pair_id (a : act) : (id * id * id * univ)option =
  (dec_act_call a = None) ?
  None :
  let (id, id', u) = oget(dec_act_call a)
  in (dec_univ_pair_id u = None) ?
     None :
     let (id'', v) = oget(dec_univ_pair_id u)
     in Some(id, id', id'', v).

op is_act_call_pair_id (a : act) : bool = dec_act_call_pair_id a <> None.

lemma act_call_pair_id_enc_dec (id id' id'' : id, u : univ) :
  dec_act_call_pair_id(enc_act_call_pair_id id id' id'' u) =
  Some(id, id', id'', u).
proof.
by rewrite /enc_act_call_pair_id /dec_act_call_pair_id /= oget_some /=
           univ_pair_id_enc_dec.
qed.

lemma is_act_call_pair_id (id id' id'' : id, u : univ) :
  is_act_call_pair_id(enc_act_call_pair_id id id' id'' u).
proof.
by rewrite /is_act_call_pair_id act_call_pair_id_enc_dec.
qed.

lemma is_act_call_pair_id_up (a : act) :
  is_act_call_pair_id a => is_act_call a.
proof. smt(). qed.

lemma dec_act_call_pair_id_up1 (a : act) :
  is_act_call_pair_id a =>
  (oget(dec_act_call_pair_id a)).`1 = (oget(dec_act_call a)).`1.
proof.
case a.
move => [id v]; by delta.
move => [id id' v].
case v.
by delta.
move => id''; by delta.
move => k; by delta.
move => [u v].
case u.
by delta.
move => id''.
case v.
by delta.
move => id'''; by delta.
move => k; by delta.
move => [u v]; by delta.
move => k; by delta.
move => [t u]; by delta.
move => [id u]; by delta.
qed.

lemma dec_act_call_pair_id_up2 (a : act) :
  is_act_call_pair_id a =>
  (oget(dec_act_call_pair_id a)).`2 = (oget(dec_act_call a)).`2.
proof.
case a.
move => [id v]; by delta.
move => [id id' v].
case v.
by delta.
move => id''; by delta.
move => k; by delta.
move => [u v].
case u.
by delta.
move => id''.
case v.
by delta.
move => id'''; by delta.
move => k; by delta.
move => [u v]; by delta.
move => k; by delta.
move => [t u]; by delta.
move => [id u]; by delta.
qed.

lemma act_for_id_call_pair_id (id : id, a : act) :
  act_for_id id a => is_act_call_pair_id a =>
  (oget(dec_act_call_pair_id a)).`1 = id.
proof.
move => act_for call_pair_id.
by rewrite (dec_act_call_pair_id_up1 a) //
           (act_for_id_call id a) //
           is_act_call_pair_id_up.
qed.

op enc_act_call_pair_id_key (id id' id'' : id, k : key) : act =
  enc_act_call_pair_id id id' id'' (UnivKey k).

op dec_act_call_pair_id_key (a : act) : (id * id * id * key)option =
  (dec_act_call_pair_id a = None) ?
  None :
  let (id, id', id'', u) = oget(dec_act_call_pair_id a)
  in (dec_univ_key u = None) ?
     None :
     Some(id, id', id'', oget(dec_univ_key u)).

op is_act_call_pair_id_key (a : act) : bool =
  dec_act_call_pair_id_key a <> None.

lemma act_call_pair_id_key_enc_dec (id id' id'' : id, k : key) :
  dec_act_call_pair_id_key(enc_act_call_pair_id_key id id' id'' k) =
  Some(id, id', id'', k).
proof.
by rewrite /enc_act_call_pair_id_key /dec_act_call_pair_id_key
           act_call_pair_id_enc_dec.
qed.

lemma is_act_call_pair_id_key (id id' id'' : id, k : key) :
  is_act_call_pair_id_key(enc_act_call_pair_id_key id id' id'' k).
proof.
by rewrite /is_act_call_pair_id_key act_call_pair_id_key_enc_dec.
qed.

lemma is_act_call_pair_id_key_up (a : act) :
  is_act_call_pair_id_key a => is_act_call_pair_id a.
proof. smt(). qed.

op enc_act_send_unit (id : id) : act =
  ActSend(id, UnivUnit).

op dec_act_send_unit (a : act) : id option =
  (dec_act_send a = None) ?
  None :
  let (id, u) = oget(dec_act_send a)
  in (u <> UnivUnit) ? None : Some id.

op is_act_send_unit (a : act) : bool = dec_act_send_unit a <> None.

lemma act_send_unit_enc_dec (id : id) :
  dec_act_send_unit(enc_act_send_unit id) = Some id.
proof. trivial. qed.

lemma is_act_send_unit (id : id) :
  is_act_send_unit(enc_act_send_unit id).
proof. trivial. qed.

lemma is_act_send_unit_up (a : act) :
  is_act_send_unit a => is_act_send a.
proof. smt(). qed.

lemma dec_act_send_unit_up (a : act) :
  is_act_send_unit a =>
  (oget(dec_act_send_unit a)) = (oget(dec_act_send a)).`1.
proof.
case a.
move => [id u].
case u.
by delta.
move => id'; by delta.
move => k; by delta.
move => [u v]; by delta.
move => [id id' u]; by delta.
move => [id u]; by delta.
qed.

lemma is_act_send_unit_elim (a : act) :
  is_act_send_unit a =>
  exists (id : id), a = ActSend(id, UnivUnit).
proof.
move => send_unit.
have [id v] ->> := is_act_send_elim a _.
  by apply is_act_send_unit_up.
exists id; move : send_unit.
case (v = UnivUnit) => // ne_v_unit.
by rewrite /is_act_send_unit /dec_act_send_unit /= oget_some /= ne_v_unit.
qed.

op enc_act_send_pair_id (id id' : id, u : univ) : act =
  ActSend(id, enc_univ_pair_id id' u).

op dec_act_send_pair_id (a : act) : (id * id * univ)option =
  (dec_act_send a = None) ?
  None :
  let (id, u) = oget(dec_act_send a)
  in (dec_univ_pair_id u = None) ?
     None :
     let (id', v) = oget(dec_univ_pair_id u)
     in Some(id, id', v).

op is_act_send_pair_id (a : act) : bool = dec_act_send_pair_id a <> None.

lemma act_send_pair_id_enc_dec (id id': id, u : univ) :
  dec_act_send_pair_id(enc_act_send_pair_id id id' u) =
  Some(id, id', u).
proof.
by rewrite /enc_act_send_pair_id /dec_act_send_pair_id
           /= oget_some /= univ_pair_id_enc_dec.
qed.

lemma is_act_send_pair_id (id id' : id, u : univ) :
  is_act_send_pair_id(enc_act_send_pair_id id id' u).
proof.
by rewrite /is_act_send_pair_id act_send_pair_id_enc_dec.
qed.

lemma is_act_send_pair_id_up (a : act) :
  is_act_send_pair_id a => is_act_send a.
proof. smt(). qed.

op enc_act_return_unit (id : id) : act = ActReturn(id, UnivUnit).

op dec_act_return_unit (a : act) : id option =
  (dec_act_return a = None) ?
  None :
  let (id, u) = oget(dec_act_return a)
  in (u <> UnivUnit) ? None : Some id.

op is_act_return_unit (a : act) : bool = dec_act_return_unit a <> None.

lemma act_return_unit_enc_dec (id : id) :
  dec_act_return_unit(enc_act_return_unit id) =
  Some id.
proof. trivial. qed.

lemma is_act_return_unit (id : id) :
  is_act_return_unit(enc_act_return_unit id).
proof. trivial. qed.

lemma is_act_return_unit_up (a : act) :
  is_act_return_unit a => is_act_return a.
proof. smt(). qed.

op enc_act_return_key (id : id, k : key) : act =
  ActReturn(id, UnivKey k).

op dec_act_return_key (a : act) : (id * key)option =
  (dec_act_return a = None) ?
  None :
  let (id, u) = oget(dec_act_return a)
  in (dec_univ_key u = None) ?
     None :
     Some(id, oget(dec_univ_key u)).

op is_act_return_key (a : act) : bool = dec_act_return_key a <> None.

lemma act_return_key_enc_dec (id : id, k : key) :
  dec_act_return_key(enc_act_return_key id k) =
  Some(id, k).
proof. trivial. qed.

lemma is_act_return_key (id : id, k : key) :
  is_act_return_key(enc_act_return_key id k).
proof. trivial. qed.

lemma is_act_return_key_up (a : act) :
  is_act_return_key a => is_act_return a.
proof. smt(). qed.

(****************************** Functionalities *******************************)

(* a functionality is a module providing the following
   procedures

   init initializes the functionality, and is passed the ID of the
   functionality's first machine, id; the rest of the functionality's
   machines are assigned a fixed and advertised number of successive
   IDs

   invoke responds to an incoming action, generating an outgoing
   action

   if the target of an incoming action (first ID of a call, send or
   return) isn't one of the functionality's machines, then act_def
   should be returned; similarly, if the return ID of an incoming call
   is one of the functionality's machines, act_def should be
   returned

   the target of an outgoing action shouldn't be one of the
   functionality's machines *)

module type FUN = {
  proc * init(id : id) : unit

  proc invoke(a : act) : act
}.

(******************************** Environment *********************************)

(* Environment may only invoke the functionality (it may not
   initialize it) *)

module type ENV(Fun : FUN) = {
  proc * main() : bool {Fun.invoke}
}.

(********************************* Experiment *********************************)

(* the Experiment is parameterized by a Functionality and the
   Environment *)

module Exper(Fun : FUN, Env : ENV) = {
  module E = Env(Fun)

  proc main() : bool = {
    var b : bool;
    Fun.init(1);  (* as 0 is the Environment's ID *)
    b <@ E.main();
    return b;
  }
}.

(*********************** Forwarding Ideal Functionality ***********************)

abstract theory Forward.

(* state of ideal functionality

   ForwStateInit is the initial state

   ForwStateWait(ret_id, v) is the state in which ideal functionality
   is waiting for Environment to tell it to return v to ret_id - after
   which it transitions to final state *)

type forw_state = [
    ForwStateInit
  | ForwStateWait of (id * univ)
  | ForwStateDone
].

op dec_fs_wait (st : forw_state) : (id * univ)option =
  with st = ForwStateInit    => None
  with st = ForwStateWait x  => Some x
  with st = ForwStateDone    => None.

op is_fs_wait (st : forw_state) = dec_fs_wait st <> None.

(* functionality uses a single ID *)

module Forw : FUN = {
  var self_id : id  (* our ID *)
  var st : forw_state  (* current state *)

  proc init(id : id) : unit = {
    self_id <- id; st <- ForwStateInit;
  }

  proc invoke(a : act) : act = {
    var id, ret_id, dest_id : id; var u : univ;
    var a' : act <- act_def;  (* default result *)

    if (st = ForwStateInit) {  (* init state *)
      if (is_act_call_pair_id a) {
        (id, ret_id, dest_id, u) <- oget(dec_act_call_pair_id a);
        if (id = self_id /\ ret_id <> self_id) {
          a' <- enc_act_send_pair_id 0 self_id (enc_univ_pair_id dest_id u);
          st <- ForwStateWait(dest_id, u);
        }
      }
    }
    elif (is_fs_wait st) {  (* wait state *)
      (dest_id, u) <- oget(dec_fs_wait st);
      if (is_act_send_unit a) {
        id <- oget(dec_act_send_unit a);
        if (id = self_id) {
          a' <- ActReturn(dest_id, u); st <- ForwStateDone;
        }
      }
    }
    return a';
  }
}.

end Forward.

(*************************** Diffie-Hellman Protocol **************************)

(* state of Diffie-Hellman protocol party

   DHStateInit is the initial state

   DHStateSent ret_id is the state after the forwarding functionality
   has been called:

     ret_id is the ID of machine to which the agreed upon key will be
     returned

   DHStateDone is the final state *)

type dh_state = [
    DHStateInit
  | DHStateSent of id
  | DHStateDone
].

op dec_dhs_sent (st : dh_state) : id option =
  with st = DHStateInit    => None
  with st = DHStateSent id => Some id
  with st = DHStateDone    => None.

op is_dhs_sent (st : dh_state) : bool = dec_dhs_sent st <> None.

lemma is_dhs_sent_elim (st : dh_state) :
  is_dhs_sent st => exists (id : id), st = DHStateSent id.
proof.
case st => // id sent; by exists id.
qed.

(* test whether ID of dh_state (if any) is outside of a range *)

op dhs_outside_range (id1 id2 : id, st : dh_state) : bool =
  st = DHStateInit \/
  (exists (id : id), st = DHStateSent id /\ (id < id1 \/ id2 < id)) \/
  st = DHStateDone.

(* guard a id1:

   return a, if a has the form ActSend(0, v) or
   ActReturn(id, v) where id1 <= id <= id1 + 1

   returns act_def, otherwise *)

op guard (a : act, id1 : id) : act =
  ((is_act_send a ?
    (let (id, v) = oget(dec_act_send a)
     in id = 0) :
    false) \/
   (is_act_return a ?
    (let (id, v) = oget(dec_act_return a)
     in id1 <= id <= id1 + 1) :
    false)) ?
  a : act_def.

lemma guard_send0 (a : act, id1 : id, v : univ) :
  guard (ActSend(0, v)) id1 = (ActSend(0, v)).
proof. trivial. qed.

lemma guard_return_in_range (a : act, id1, id : id, v : univ) :
  id1 <= id <= id1 + 1 =>
  guard (ActReturn(id, v)) id1 = (ActReturn(id, v)).
proof.
move => id_rng; rewrite /guard /#.
qed.

lemma guard_call (a : act, id1, id, id' : id, v : univ) :
  guard (ActCall(id, id', v)) id1 = act_def.
proof. trivial. qed.

lemma guard_send_non0 (a : act, id1, id : id, v : univ) :
  id <> 0 => guard (ActSend(id, v)) id1 = act_def.
proof.
move => ne0_id; rewrite /guard /#.
qed.

lemma guard_return_not_in_range (a : act, id1, id : id, v : univ) :
  !(id1 <= id <= id1 + 1) =>
  guard (ActReturn(id, v)) id1 = act_def.
proof.
move => id_not_in_rng; rewrite /guard /#.
qed.

(* functionality is parameterized by two instances of forwarding
   fuctionality *)

module DH(Fw1 : FUN, Fw2 : FUN) : FUN = {
  (* machine IDs

     id1 and id1 + 1 are IDs of first and second parties

     id1 + 2 and id1 + 3 are IDs of parties' forwarding
     functionalities' machines *)

  var id1 : id

  (* map sending id1 and id1 + 1 to the states for parties 1 and 2 *)

  var states : (id, dh_state)fmap

  (* map sending id1 and id1 + 1 to randomly chosen exp's for parties
     1 and 2 *)

  var exps : (id, exp)fmap

  proc init(id : id) : unit = {
    var exp1, exp2 : exp;
    id1 <- id;
    exp1 <$ exp_distr; exp2 <$ exp_distr;
    exps <- two_fmap_init id (id + 1) exp1 exp2;
    states <- two_fmap_init id (id + 1) DHStateInit DHStateInit;    
    Fw1.init(id + 2); Fw2.init(id + 3);
  }

  (* DH party

     self_id is party's ID (id1 or id1 + 1), and a acts for
     self_id *)

  proc party(self_id : id, a : act) : act = {
    var id, other_id, ret_id, fw_id : id;
    var k : key;
    var st : dh_state <- oget states.[self_id];
    var x : exp <- oget exps.[self_id];
    var a' : act <- act_def;

    (* other party *)
    other_id <- (self_id = id1) ? self_id + 1 : (self_id - 1);
    fw_id <- self_id + 2;  (* ID of our forwarding machine *)
    if (st = DHStateInit) {  (* init state *)
      if (is_act_call_unit a) {
        (id, ret_id) <- oget(dec_act_call_unit a);
        a' <- enc_act_call_pair_id_key fw_id self_id other_id (g ^ x);
        states.[self_id] <- DHStateSent ret_id;
      }
      elif (is_act_return_key a) {  (* from forwarding, but too soon *)
        states.[self_id] <- DHStateDone;
      }
    }
    elif (is_dhs_sent st) {  (* sent state *)
      ret_id <- oget(dec_dhs_sent st);
      if (is_act_return_key a) {  (* from forwarding *)
        (id, k) <- oget(dec_act_return_key a);
        a' <- enc_act_return_key ret_id (k ^ x);
        states.[self_id] <- DHStateDone;
      }
    }
    return a';
  }

  (* dispatch loop *)

  proc loop(a : act) : act = {
    var id : id; var v : univ;

    while (act_for_id_range id1 (id1 + 3) a) {
      if (act_for_id id1 a) {
        a <@ party(id1, a);
      }
      elif (act_for_id (id1 + 1) a) {
        a <@ party(id1 + 1, a);
      }
      else {
        if (act_for_id (id1 + 2) a) {
          a <@ Fw1.invoke(a);
        } 
        else  (* act_for_id (id1 + 3) a *) {
          a <@ Fw2.invoke(a);
        }
        (* restrict way Fw1/Fw2 may communicate *)
        a <- guard a id1;
      }
    }
    return a;
  }

  proc invoke(a : act) : act = {
    var id, id' : id; var a' : act;
    var ignore : bool <- false;

    (* functionality only responds to

         calls to DH party with value UnivUnit

         sends to Fw1 or Fw2 with value UnivUnit *)

    if (is_act_call_unit a) {
      (id, id') <- oget(dec_act_call_unit a);
      if (id < id1 \/ id1 + 1 < id \/ id1 <= id' <= id1 + 3) {
        ignore <- true;
      }
    }
    elif (is_act_send_unit a) {
      id <- oget(dec_act_send_unit a);
      if (id < id1 + 2 \/ id1 + 3 < id) {
        ignore <- true;
      }
    }
    else {  (* return or unwanted call/send *)
      ignore <- true;
    }

    if (ignore) {
      a' <- act_def;
    }
    else {
      a' <@ loop(a);
    }
    return a';
  }
}.

(***************************** Ideal Functionality ****************************)

(* Ideal Functionality is parameterized by Simulator *)

module IF(Sim : FUN) : FUN = {
  (* machine IDs

     id1 and id1 + 1 are IDs of first and second parties

     id1 + 2 and id1 + 3 are IDs of parties' forwarding
     functionalities' machines, run by Sim *)

  var id1 : id

  (* map sending id1 and id1 + 1 to the states for parties 1 and 2 *)

  var states : (id, dh_state)fmap

  (* generated exp *)

  var exp : exp

  proc init(id : id) : unit = {
    id1 <- id;
    exp <$ exp_distr;
    states <- two_fmap_init id (id + 1) DHStateInit DHStateInit;
    Sim.init(id + 2);
  }

  (* IF party

     self_id is party's ID (id1 or id1 + 1), and a acts for
     self_id *)

  proc party(self_id : id, a : act) : act = {
    var id, other_id, ret_id, sim_id : id;
    var k : key;
    var st : dh_state <- oget states.[self_id];
    var a' : act <- act_def;

    other_id <- (self_id = id1) ? self_id + 1 : (self_id - 1);
    sim_id <- self_id + 2;  (* ID of Sim machine acting as forwarder *)
    if (st = DHStateInit) {  (* init state *)
      if (is_act_call_unit a) {
        (id, ret_id) <- oget(dec_act_call_unit a);
        a' <- enc_act_call_unit sim_id self_id;
        states.[self_id] <- DHStateSent ret_id;
      }
      elif (is_act_return_unit a) {  (* from Sim, but too soon *)
        states.[self_id] <- DHStateDone;
      }
    }
    elif (is_dhs_sent st) {  (* sent state *)
      ret_id <- oget(dec_dhs_sent st);
      if (is_act_return_unit a) {  (* from Sim *)
        a' <- enc_act_return_key ret_id (g ^ exp);
        states.[self_id] <- DHStateDone;
      }
    }
    return a';
  }

  (* dispatch loop *)

  proc loop(a : act) : act = {
    var id : id; var v : univ;

    while (act_for_id_range id1 (id1 + 3) a) {
      if (act_for_id id1 a) {
        a <@ party(id1, a);
      }
      elif (act_for_id (id1 + 1) a) {
        a <@ party(id1 + 1, a);
      }
      else  (* act_for_id_range (id1 + 2) (id1 + 3) a *) {
        a <@ Sim.invoke(a);
        a <- guard a id1;
      } 
    }
    return a;
  }

  proc invoke(a : act) : act = {
    var id, id' : id; var a' : act;
    var ignore : bool <- false;

    if (is_act_call_unit a) {
      (id, id') <- oget(dec_act_call_unit a);
      if (id < id1 \/ id1 + 1 < id \/ id1 <= id' <= id1 + 3) {
        ignore <- true;
      }
    }
    elif (is_act_send_unit a) {
      id <- oget(dec_act_send_unit a);
      if (id < id1 + 2 \/ id1 + 3 < id) {
        ignore <- true;
      }
    }
    else {
      ignore <- true;
    }

    if (ignore) {
      a' <- act_def;
    }
    else {
      a' <@ loop(a);
    }
    return a';
  }
}.

(********************************** Simulator *********************************)

(* the Simulator simulates two forwarding functionality machines,
   each with a state *)

type sim_state = [
    SimStateInit
  | SimStateWait
  | SimStateDone
].

module Sim : FUN = {
  (* machine IDs:

       id1 and id1 + 1 simulate the two forwarding functionality
       machines *)

  var id1 : id

  (* map sending id1 and id1 + 1 to Simulator state *)

  var states : (id, sim_state)fmap

  (* map sending id1 and id1 + 1 to generated exponent *)

  var exps : (id, exp)fmap

  proc init(id : id) : unit = {
    var x1, x2 : exp;
    id1 <- id;
    states <- two_fmap_init id (id + 1) SimStateInit SimStateInit;
    x1 <$ exp_distr; x2 <$ exp_distr;
    exps <- two_fmap_init id (id + 1) x1 x2;
  }

  proc invoke(a : act) : act = {
    var st, other_st : sim_state;
    var id, self_id, ret_id, dest_id;
    var x : exp; var u : univ;
    var a' : act <- act_def;

    self_id <- (act_for_id id1 a) ? id1 : (id1 + 1);
    st <- oget states.[self_id];
    if (st = SimStateInit) {
      if (is_act_call_unit a) {
        (id, ret_id) <- oget(dec_act_call_unit a);
        x <- oget exps.[self_id];
        u <- UnivKey(g ^ x);
        dest_id <- (self_id = id1) ? id1 - 1 : (id1 - 2);
        a' <- enc_act_send_pair_id 0 self_id (enc_univ_pair_id dest_id u);
        states.[self_id] <- SimStateWait;
      }
    }
    elif (st = SimStateWait) {
      if (is_act_send_unit a) {
        ret_id <- (self_id = id1) ? id1 - 1 : (id1 - 2);
        a' <- enc_act_return_unit ret_id;
        states.[self_id] <- SimStateDone;
      }
    }
    return a';
  }
}.

(******************************** DDH Adversary *******************************)

(* our security theorem involves a DDH Adversary constructed from the
   Environment *)

module DDHAdv(Env : ENV) : DDH_ADV = {
  var key1, key2, key3 : key

  module Sim : FUN = {
    var id1 : id
    var states : (id, sim_state)fmap

    proc init(id : id) : unit = {
      id1 <- id;
      states <- two_fmap_init id (id + 1) SimStateInit SimStateInit;
    }

    proc invoke(a : act) : act = {
      var st, other_st : sim_state;
      var id, self_id, ret_id, dest_id : id;
      var k : key; var u : univ;
      var a' : act <- act_def;

      self_id <- (act_for_id id1 a) ? id1 : (id1 + 1);
      st <- oget states.[self_id];
      if (st = SimStateInit) {
        if (is_act_call_unit a) {
          (id, ret_id) <- oget(dec_act_call_unit a);
          k <- (self_id = id1) ? key1 : key2;  (* NOTE *)
          u <- UnivKey k;
          dest_id <- (self_id = id1) ? id1 - 1 : (id1 - 2);
          a' <- enc_act_send_pair_id 0 self_id (enc_univ_pair_id dest_id u);
          states.[self_id] <- SimStateWait;
        }
      }
      elif (st = SimStateWait) {
        if (is_act_send_unit a) {
          ret_id <- (self_id = id1) ? id1 - 1 : (id1 - 2);
          a' <- enc_act_return_unit ret_id;
          states.[self_id] <- SimStateDone;
        }
      }
      return a';
    }
  }

  module Fun : FUN = {
    var id1 : id

    var states : (id, dh_state)fmap

    proc init(id : id) : unit = {
      id1 <- id;
      states <- two_fmap_init id (id + 1) DHStateInit DHStateInit;
      Sim.init(id + 2);
    }

    proc party(self_id : id, a : act) : act = {
      var id, other_id, ret_id, sim_id : id;
      var k : key;
      var st : dh_state <- oget states.[self_id];
      var a' : act <- act_def;
  
      other_id <- (self_id = id1) ? self_id + 1 : (self_id - 1);
      sim_id <- self_id + 2;
      if (st = DHStateInit) {
        if (is_act_call_unit a) {
          (id, ret_id) <- oget(dec_act_call_unit a);
          a' <- enc_act_call_unit sim_id self_id;
          states.[self_id] <- DHStateSent ret_id;
        }
        elif (is_act_return_unit a) {
          states.[self_id] <- DHStateDone;
        }
      }
      elif (is_dhs_sent st) {
        ret_id <- oget(dec_dhs_sent st);
        if (is_act_return_unit a) {
          a' <- enc_act_return_key ret_id key3;  (* NOTE *)
          states.[self_id] <- DHStateDone;
        }
      }
      return a';
    }

    proc loop(a : act) : act = {
      var id : id; var v : univ;

      while (act_for_id_range id1 (id1 + 3) a) {
        if (act_for_id id1 a) {
          a <@ party(id1, a);
        }
        elif (act_for_id (id1 + 1) a) {
          a <@ party(id1 + 1, a);
        }
        else {
          a <@ Sim.invoke(a);
          a <- guard a id1;
        } 
      }
      return a;
    }

    proc invoke(a : act) : act = {
      var id, id' : id; var a' : act;
      var ignore : bool <- false;

      if (is_act_call_unit a) {
        (id, id') <- oget(dec_act_call_unit a);
        if (id < id1 \/ id1 + 1 < id \/ id1 <= id' <= id1 + 3) {
          ignore <- true;
        }
      }
      elif (is_act_send_unit a) {
        id <- oget(dec_act_send_unit a);
        if (id < id1 + 2 \/ id1 + 3 < id) {
          ignore <- true;
        }
      }
      else {
        ignore <- true;
      }

      if (ignore) {
        a' <- act_def;
      }
      else {
        a' <@ loop(a);
      }
      return a';
    }
  }

  module E = Env(Fun)

  proc main(k1 k2 k3 : key) : bool = {
    var b : bool;
    key1 <- k1; key2 <- k2; key3 <- k3; 
    Fun.init(1);
    b <@ E.main();
    return b;
  }
}.

(****************** Instances of Forwarding Functionalities *******************)

(* by cloning Forward twice, we get functionalities with disjoint
   global variables *)

clone Forward as Fw1.  (* for Party 1 *)
clone Forward as Fw2.  (* for Party 2 *)

(* our goal is to prove (see end of file):

lemma Security (Env <: ENV{DH, Fw1.Forw, Fw2.Forw, IF, Sim, DDHAdv}) &m :
    `|Pr[Exper(DH(Fw1.Forw, Fw2.Forw), Env).main() @ &m : res] -
      Pr[Exper(IF(Sim), Env).main() @ &m : res]| =
    `|Pr[DDH1(DDHAdv(Env)).main() @ &m : res] -
      Pr[DDH2(DDHAdv(Env)).main() @ &m : res]|.
*)

(******************************************************************************)
(***************************** Main Part of Proof *****************************)
(******************************************************************************)

lemma act_for_id_range_1_4_not_3 (a : act) :
  act_for_id_range 1 4 a =>
  ! act_for_id 1 a =>
  ! act_for_id 2 a =>
  ! act_for_id 3 a =>
  act_for_id 4 a.
proof.
elim a; smt().
qed.

lemma act_for_id_range_1_4_not_1_2 (a : act) :
  act_for_id_range 1 4 a =>
  ! act_for_id 1 a =>
  ! act_for_id 2 a =>
  act_for_id_range 3 4 a.
proof.
elim a; smt().
qed.

(*************************** Invariant on DH States ***************************)

pred dh_states_pred (states : (id, dh_state)fmap) =
  two_fmap states 1 2 /\
  dhs_outside_range 1 4 (oget states.[1]) /\
  dhs_outside_range 1 4 (oget states.[2]).

lemma dh_states_pred_init :
  dh_states_pred(two_fmap_init 1 2 DHStateInit DHStateInit).
proof.
split; first by rewrite two_fmap_init.
rewrite /two_fmap_init.
split; first by rewrite set_set /= getP_eq oget_some.
by rewrite getP_eq oget_some.
qed.

lemma dh_states_pred_update
      (id : id, dhs : dh_state, states : (id, dh_state)fmap) :
  dh_states_pred states =>
  (id = 1 \/ id = 2) => dhs_outside_range 1 4 dhs =>
  dh_states_pred (states.[id <- dhs]).
proof.
move => dhs_pred id_1_or_2 dhs_outside; rewrite /dh_states_pred.
elim id_1_or_2 => ->.
split; first rewrite two_fmap_update; smt().
split; first by rewrite getP /= 1:oget_some.
rewrite getP /= /#.
split; first rewrite two_fmap_update; smt().
split; first rewrite getP /= /#.
by rewrite getP_eq oget_some.
qed.

lemma dh_states_pred_sent_outside (id : id, states : (id, dh_state)fmap) :
  dh_states_pred states =>
  (id = 1 \/ id = 2) => is_dhs_sent (oget states.[id]) =>
  oget(dec_dhs_sent (oget states.[id])) < 1 \/
  4 < oget (dec_dhs_sent (oget states.[id])).
proof.
move => [two [out1 out2]] id_1_or_2.
elim id_1_or_2 => ->>.
move => /is_dhs_sent_elim [id' states_1_eq].
rewrite states_1_eq /= oget_some /#.
move => /is_dhs_sent_elim [id' states_2_eq].
rewrite states_2_eq /= oget_some /#.
qed.

(********** Relational Invariants Between Forwarding/Simulator States *********)

(* for Fw1 *)

pred forward_rel1 (fw_st : Fw1.forw_state, sim_st : sim_state, exp1 : exp) =
  fw_st = Fw1.ForwStateInit /\ sim_st = SimStateInit \/
  fw_st = Fw1.ForwStateWait(2, UnivKey(g ^ exp1)) /\ sim_st = SimStateWait \/
  fw_st = Fw1.ForwStateDone /\ sim_st = SimStateDone.

lemma forward_rel1_wait
      (fw_st : Fw1.forw_state, sim_st : sim_state, exp1 : exp) :
  forward_rel1 fw_st sim_st exp1 =>
  Fw1.is_fs_wait fw_st <=> sim_st = SimStateWait.
proof. 
elim; first smt().
elim => [[-> _] |].
by rewrite /is_fs_wait.
smt().
qed.

lemma forward_rel1_wait_dest_id
      (fw_st : Fw1.forw_state, sim_st : sim_state, exp1 : exp) :
  forward_rel1 fw_st sim_st exp1 =>
  Fw1.is_fs_wait fw_st =>
  (oget (Fw1.dec_fs_wait fw_st)).`1 = 2.
proof.
elim; first smt().
elim => [[-> _] |].
by rewrite /is_fs_wait.
smt().
qed.

lemma forward_rel1_wait_key
      (fw_st : Fw1.forw_state, sim_st : sim_state, exp1 : exp) :
  forward_rel1 fw_st sim_st exp1 =>
  Fw1.is_fs_wait fw_st =>
  (oget (Fw1.dec_fs_wait fw_st)).`2 = UnivKey(g ^ exp1).
proof.
elim; first smt().
elim => [[-> _] |].
by rewrite /is_fs_wait.
smt().
qed.

(* for Fw2 *)

pred forward_rel2 (fw_st : Fw2.forw_state, sim_st : sim_state, exp2 : exp) =
  fw_st = Fw2.ForwStateInit /\ sim_st = SimStateInit \/
  fw_st = Fw2.ForwStateWait(1, UnivKey(g ^ exp2)) /\ sim_st = SimStateWait \/
  fw_st = Fw2.ForwStateDone /\ sim_st = SimStateDone.

lemma forward_rel2_wait
      (fw_st : Fw2.forw_state, sim_st : sim_state, exp1 : exp) :
  forward_rel2 fw_st sim_st exp1 =>
  Fw2.is_fs_wait fw_st <=> sim_st = SimStateWait.
proof. 
elim; first smt().
elim => [[-> _] |].
by rewrite /is_fs_wait.
smt().
qed.

lemma forward_rel2_wait_dest_id
      (fw_st : Fw2.forw_state, sim_st : sim_state, exp1 : exp) :
  forward_rel2 fw_st sim_st exp1 =>
  Fw2.is_fs_wait fw_st =>
  (oget (Fw2.dec_fs_wait fw_st)).`1 = 1.
proof.
elim; first smt().
elim => [[-> _] |].
by rewrite /is_fs_wait.
smt().
qed.

lemma forward_rel2_wait_key
      (fw_st : Fw2.forw_state, sim_st : sim_state, exp2 : exp) :
  forward_rel2 fw_st sim_st exp2 =>
  Fw2.is_fs_wait fw_st =>
  (oget (Fw2.dec_fs_wait fw_st)).`2 = UnivKey(g ^ exp2).
proof.
elim; first smt().
elim => [[-> _] |].
by rewrite /is_fs_wait.
smt().
qed.

(*************** Relational Invariant Between Actions for DH/IF ***************)

inductive act_rel (a1 a2 : act, exp1 exp2 : exp) =
    (* the default *)

    ActRelDefault of
        (a1 = act_def)
      & (a2 = act_def)

    (* Environment's calls to the DH Parties *)

  | ActRelEnvCallToDHParty1 (id : id) of
        (id < 1 \/ 4 < id)
      & (a1 = ActCall(1, id, UnivUnit))
      & (a2 = ActCall(1, id, UnivUnit))

  | ActRelEnvCallToDHParty2 (id : id) of
        (id < 1 \/ 4 < id)
      & (a1 = ActCall(2, id, UnivUnit))
      & (a2 = ActCall(2, id, UnivUnit))

    (* DH Parties' calls to Forwarding Functionalities *)

  | ActRelDHParty1CallToFwd1 of
        (a1 = ActCall(3, 1, enc_univ_pair_id_key 2 (g ^ exp1)))
      & (a2 = ActCall(3, 1, UnivUnit))

  | ActRelDHParty2CallToFwd2 of
        (a1 = ActCall(4, 2, enc_univ_pair_id_key 1 (g ^ exp2)))
      & (a2 = ActCall(4, 2, UnivUnit))

    (* Forwarding Functionalities' sends to Environment *)

  | ActRelFw1SendToEnv of
        (a1 =
         ActSend
         (0, enc_univ_pair_id 3 (enc_univ_pair_id_key 2 (g ^ exp1))))
      & (a2 =
         ActSend
         (0, enc_univ_pair_id 3 (enc_univ_pair_id_key 2 (g ^ exp1))))

  | ActRelFw2SendToEnv of
        (a1 =
         ActSend
         (0, enc_univ_pair_id 4 (enc_univ_pair_id_key 1 (g ^ exp2))))
      & (a2 =
         ActSend
         (0, enc_univ_pair_id 4 (enc_univ_pair_id_key 1 (g ^ exp2))))

    (* Environment's sends to Forwarding Functionalities *)

  | ActRelEnvSendToFw1 of
        (a1 = ActSend(3, UnivUnit))
      & (a2 = ActSend(3, UnivUnit))

  | ActRelEnvSendToFw2 of
        (a1 = ActSend(4, UnivUnit))
      & (a2 = ActSend(4, UnivUnit))

    (* Forwarding Functionalities's returns to DH Parties *)

  | ActRelFw1ReturnToDHParty2 of
        (a1 = ActReturn(2, UnivKey(g ^ exp1)))
      & (a2 = ActReturn(2, UnivUnit))

  | ActRelFw2ReturnToDHParty1 of
        (a1 = ActReturn(1, UnivKey(g ^ exp2)))
      & (a2 = ActReturn(1, UnivUnit))

    (* DH Parties's returns to Environment *)

  | ActRelDHPartiesReturnToEnv (id : id) of
        (id < 1 \/ 4 < id)
      & (a1 = ActReturn(id, UnivKey(g ^ exp2 ^ exp1)))
      & (a2 = ActReturn(id, UnivKey(g ^ exp1 ^ exp2))).

lemma act_rel_act_for_id (a1 a2 : act, exp1 exp2 : exp, id : id) :
  act_rel a1 a2 exp1 exp2 =>
  act_for_id id a1 <=> act_for_id id a2.
proof.  
by move => [].
qed.

lemma act_rel_act_for_id_range (a1 a2 : act, exp1 exp2 : exp, id1 id2 : id) :
  act_rel a1 a2 exp1 exp2 =>
  act_for_id_range id1 id2 a1 <=> act_for_id_range id1 id2 a2.
proof.  
by move => [].
qed.

lemma act_rel_not_act_for_range_eq (a1 a2 : act, exp1 exp2 : exp) :
  act_rel a1 a2 exp1 exp2 => ! act_for_id_range 1 4 a1 =>
  a1 = a2.
proof.
move => act_rel not_act_for_id_range_1_4.
case act_rel; smt(act_rel_act_for_id pow_pow_comm).
qed.

lemma act_rel_act_for_1_or_2_call_unit_eq
      (a1 a2 : act, exp1 exp2 : exp, id : id) :
  act_rel a1 a2 exp1 exp2 =>
  1 <= id <= 2 => act_for_id id a1 =>
  is_act_call_unit a1 => is_act_call_unit a2 =>
  a1 = a2.
proof.
move => act_rel id_range act_for call_unit1 call_unit2.
case act_rel => //; smt().
qed.

lemma act_rel_send_unit_iff (a1 a2 : act, exp1 exp2 : exp) :
  act_rel a1 a2 exp1 exp2 =>
  (is_act_send_unit a1 <=> is_act_send_unit a2).
proof.
by move => [].
qed.

lemma act_rel_act_for_1_or_2_call_unit
      (a1 a2 : act, exp1 exp2 : exp, id : id) :
  act_rel a1 a2 exp1 exp2 =>
  1 <= id <= 2 => act_for_id id a1 =>
  is_act_call_unit a1 <=> is_act_call_unit a2.
proof.
move => act_rel id_range act_for.
case act_rel => //.
move => ->> _; rewrite /= /# in act_for.
move => ->> _; rewrite /= /# in act_for.
qed.

lemma act_rel_call_pair_id_imp_call_unit (a1 a2 : act, exp1 exp2 : exp) :
  act_rel a1 a2 exp1 exp2 => is_act_call_pair_id a1 =>
  is_act_call_unit a2.
proof.
move => act_rel call_pair_id.
case act_rel => //.
qed.

lemma act_rel_act_for3_call_unit_imp_call_pair_id
      (a1 a2 : act, exp1 exp2 : exp) :
  act_rel a1 a2 exp1 exp2 =>
  act_for_id 3 a2 => is_act_call_unit a2 =>
  is_act_call_pair_id a1.
proof.
move => act_rel act_for call_unit.
case act_rel => //.
move => -> _.
rewrite /enc_univ_pair_id_key
       -/(enc_act_call_pair_id 3 1 2 (UnivKey (g ^ exp1)))
       is_act_call_pair_id.
move => _ ->>; rewrite /= in act_for; elim act_for.
qed.

lemma act_rel_act_for4_call_unit_imp_call_pair_id
      (a1 a2 : act, exp1 exp2 : exp) :
  act_rel a1 a2 exp1 exp2 =>
  act_for_id 4 a2 => is_act_call_unit a2 =>
  is_act_call_pair_id a1.
proof.
move => act_rel act_for call_unit.
case act_rel => //.
move => _ ->>; rewrite /= in act_for; elim act_for.
move => -> _.
rewrite /enc_univ_pair_id_key
       -/(enc_act_call_pair_id 4 2 1 (UnivKey (g ^ exp2)))
       is_act_call_pair_id.
qed.

lemma act_rel_return_unit2_imp_return_key1 (a1 a2 : act, exp1 exp2 : exp) :
  act_rel a1 a2 exp1 exp2 => is_act_return_unit a2 =>
  is_act_return_key a1.
proof.
move => act_rel ret_unit2.
case act_rel => //.
qed.

lemma act_rel_act_for_1_or_2_return_key1_imp_return_unit2
      (a1 a2 : act, exp1 exp2 : exp, id : int) :
  act_rel a1 a2 exp1 exp2 =>
  1 <= id <= 2 => act_for_id id a1 => 
  is_act_return_key a1 =>
  is_act_return_unit a2.
proof.
move => act_rel id_ran act_for ret_key1.
case act_rel => //.
move => id' id'_range ->> _.
rewrite /= in act_for.
have /# : 1 <= id <= 2 by smt().
qed.

lemma act_rel_act_for1_return_key_unit_act_key (a1 a2 : act, exp1 exp2 : exp) :
  act_rel a1 a2 exp1 exp2 =>
  act_for_id 1 a1 =>
  is_act_return_key a1 => is_act_return_unit a2 =>
  (oget (dec_act_return_key a1)).`2 = g ^ exp2.
proof.
move => act_rel act_for1 ret_key1 ret_unit2.
case act_rel; first 9 smt().
move => ->> _.
rewrite /= in act_for1.
elim act_for1.
move => -> _.
by rewrite -/(enc_act_return_key 1 (g ^ exp2))
           act_return_key_enc_dec oget_some.
move => id range ->> _.
rewrite /= in act_for1; smt().
qed.

lemma act_rel_act_for2_return_key_unit_act_key
      (a1 a2 : act, exp1 exp2 : exp) :
  act_rel a1 a2 exp1 exp2 =>
  act_for_id 2 a1 =>
  is_act_return_key a1 => is_act_return_unit a2 =>
  (oget (dec_act_return_key a1)).`2 = g ^ exp1.
proof.
move => act_rel act_for2 ret_key1 ret_unit2.
case act_rel; first 9 smt().
move => -> _.
by rewrite -/(enc_act_return_key 2 (g ^ exp1))
           act_return_key_enc_dec oget_some.
move => ->> _.
rewrite /= in act_for2.
elim act_for2.
move => id id_range ->> _.
rewrite /= in act_for2.
have /# : 1 <= id <= 2 by smt().
qed.

lemma act_rel_call_pair_id2 (a1 a2 : act, exp1 exp2 : exp) :
  act_rel a1 a2 exp1 exp2 =>
  is_act_call_pair_id a1 =>
  (oget (dec_act_call_pair_id a1)).`2 < 3.
proof.
move => act_rel call_pair_id.
(case act_rel; first 3 smt()); last 7 smt().
move => -> _.
by rewrite /enc_univ_pair_id_key
           -/(enc_act_call_pair_id 3 1 2 (UnivKey (g ^ exp1)))
           act_call_pair_id_enc_dec oget_some.
move => -> _.
by rewrite /enc_univ_pair_id_key
           -/(enc_act_call_pair_id 3 1 2 (UnivKey (g ^ exp1)))
           act_call_pair_id_enc_dec oget_some.
qed.

lemma act_rel_call_unit_ret_outside_range (a1 a2 : act, exp1 exp2 : exp) :
  act_rel a1 a2 exp1 exp2 => is_act_call_unit a1 =>
  let id = (oget (dec_act_call_unit a1)).`2 in
  id < 1 \/ 4 < id.
proof.
move => act_rel call_unit1.
case act_rel; last 7 smt().
smt().
move => id range -> _.
by rewrite -/(enc_act_call_unit 1 id) act_call_unit_enc_dec oget_some.
move => id range -> _.
by rewrite -/(enc_act_call_unit 1 id) act_call_unit_enc_dec oget_some.
move => ->> _.
rewrite /is_act_call_unit /dec_act_call_unit /= oget_some /= /#
  in call_unit1.
move => ->> _.
rewrite /is_act_call_unit /dec_act_call_unit /= oget_some /= /#
  in call_unit1.
qed.

lemma act_rel_init_call_unit (a1 a2 : act, exp1 exp2 : exp) :
  a1 = a2 => is_act_call_unit a1 =>
  ! ((oget(dec_act_call_unit a1)).`1 < 1 \/
     2 < (oget(dec_act_call_unit a1)).`1 \/
     1 <= (oget (dec_act_call_unit a1)).`2 <= 4) =>
  act_rel a1 a2 exp1 exp2.
proof.
move => <- /is_act_call_unit_elim [id id'] -> ranges.
rewrite
  -/(enc_act_call_unit id id') act_call_unit_enc_dec oget_some /=
  in ranges.
have range_id' : id' < 1 \/ 4 < id' by smt().
have [] : id = 1 \/ id = 2 by smt().
move => ->; by apply (ActRelEnvCallToDHParty1 _ _ _ _ id').
move => ->; by apply (ActRelEnvCallToDHParty2 _ _ _ _ id').
qed.

lemma act_rel_init_send_unit (a1 a2 : act, exp1 exp2 : exp) :
  a1 = a2 => is_act_send_unit a1 =>
  ! (oget(dec_act_send_unit a1) < 3 \/
     4 < oget(dec_act_send_unit a1)) =>
  act_rel a1 a2 exp1 exp2.
proof.
move => <- /is_act_send_unit_elim [id] -> range.
rewrite
  -/(enc_act_send_unit id) act_send_unit_enc_dec oget_some /=
  in range.
have [] : id = 3 \/ id = 4 by smt().
move => ->; by apply ActRelEnvSendToFw1.
move => ->; by apply ActRelEnvSendToFw2.
qed.

lemma act_rel_return_key_unit1
      (id : id, u : univ, exp1 exp2 : exp, fw_st : Fw1.forw_state,
       sim_st : sim_state) :
  forward_rel1 fw_st sim_st exp1 => Fw1.is_fs_wait fw_st =>
  act_rel (ActReturn(oget(Fw1.dec_fs_wait fw_st)))
          (enc_act_return_unit 2) exp1 exp2.
proof.
move => fw_rel1 wait_fw_st.
smt(forward_rel1_wait_dest_id forward_rel1_wait_key
    ActRelFw1ReturnToDHParty2).
qed.

lemma act_rel_return_key_unit2
      (id : id, u : univ, exp1 exp2 : exp, fw_st : Fw2.forw_state,
       sim_st : sim_state) :
  forward_rel2 fw_st sim_st exp2 => Fw2.is_fs_wait fw_st =>
  act_rel (ActReturn(oget(Fw2.dec_fs_wait fw_st)))
          (enc_act_return_unit 1) exp1 exp2.
proof.
move => fw_rel2 wait_fw_st.
smt(forward_rel2_wait_dest_id forward_rel2_wait_key
    ActRelFw2ReturnToDHParty1).
qed.

lemma act_rel_return_key (a1 a2 : act, exp1 exp2 : exp, id : id) :
  act_rel a1 a2 exp1 exp2 =>
  is_act_return_key a1 => is_act_return_unit a2 =>
  (id < 1 \/ 4 < id) =>
  act_rel
  (enc_act_return_key id (g ^ exp2 ^ exp1))
  (enc_act_return_key id (g ^ exp1 ^ exp2))
  exp1 exp2.
proof.
move => act_rel ret_key1 ret_unit2 out_range.
by apply (ActRelDHPartiesReturnToEnv _ _ _ _ id).
qed.

lemma act_rel_guard (a1 a2 : act, exp1 exp2 : exp) :
  act_rel a1 a2 exp1 exp2 =>
  act_rel (guard a1 1) (guard a2 1) exp1 exp2.
proof.
rewrite /guard.
case.
move => -> -> /=; by apply ActRelDefault.
move => id id_range -> ->.
rewrite /= /is_act_return /is_act_send /=; by apply ActRelDefault.
move => id id_range -> ->.
rewrite /= /is_act_return /is_act_send /=; by apply ActRelDefault.
move => -> ->.
rewrite /= /is_act_return /is_act_send /=; by apply ActRelDefault.
move => -> ->.
rewrite /= /is_act_return /is_act_send /=; by apply ActRelDefault.
move => -> ->.
rewrite /= /is_act_return /is_act_send /= oget_some /=.
by apply ActRelFw1SendToEnv.
move => -> ->.
rewrite /= /is_act_return /is_act_send /= oget_some /=.
by apply ActRelFw2SendToEnv.
move => -> ->.
rewrite /= /is_act_return /is_act_send /= oget_some /=; by apply ActRelDefault.
move => -> ->.
rewrite /= /is_act_return /is_act_send /= oget_some /=; by apply ActRelDefault.
move => -> ->.
rewrite /= /is_act_return /is_act_send /= oget_some /= oget_some /=.
by apply ActRelFw1ReturnToDHParty2.
move => -> ->.
rewrite /= /is_act_return /is_act_send /= oget_some /= oget_some /=.
by apply ActRelFw2ReturnToDHParty1.
move => id id_range -> ->.
rewrite /= /is_act_return /is_act_send /= oget_some /= oget_some /=.
have -> /= : (1 <= id <= 2) = false by smt().
by apply ActRelDefault.
qed.

lemma act_rel_guard_range_lr (a1 a2 : act, exp1 exp2 : exp) :
  act_rel a1 a2 exp1 exp2 =>
  act_for_id_range 1 4 (guard a1 1) =>
  act_for_id_range 1 4 (guard a2 1).
proof.
case; first 9 smt().
move => -> ->; rewrite /guard /=.
have -> /= : is_act_send (ActReturn (1, UnivKey (g ^ exp2))) = false
  by trivial.
have -> // : is_act_return (ActReturn (1, UnivKey (g ^ exp2))) = true
  by trivial.
move => -> ->; rewrite /guard /=.
have -> /= : is_act_send (ActReturn (1, UnivKey (g ^ exp2))) = false
  by trivial.
have -> // : is_act_return (ActReturn (1, UnivKey (g ^ exp2))) = true
  by trivial.
move => id id_range -> -> /#.
qed.

lemma act_rel_guard_range_rl (a1 a2 : act, exp1 exp2 : exp) :
  act_rel a1 a2 exp1 exp2 =>
  act_for_id_range 1 4 (guard a2 1) =>
  act_for_id_range 1 4 (guard a1 1).
proof.
case; first 9 smt().
move => -> ->.
rewrite /guard /=.
have -> /= : is_act_send (ActReturn (2, UnivKey (g ^ exp1))) = false
  by trivial.
have -> // : is_act_return (ActReturn (2, UnivKey (g ^ exp1))) = true
  by trivial.
move => -> ->.
rewrite /guard /=.
have -> /= : is_act_send (ActReturn (1, UnivKey (g ^ exp2))) = false
  by trivial.
have -> // : is_act_return (ActReturn (1, UnivKey (g ^ exp2))) = true
  by trivial.
move => id id_range -> -> /#.
qed.

lemma act_rel_forward1_wait_state (a1 a2 : act, exp1 exp2 : exp) :
  act_rel a1 a2 exp1 exp2 =>
  act_for_id 3 a1 => is_act_call_pair_id a1 =>
  forward_rel1
  (Fw1.ForwStateWait
   ((oget (dec_act_call_pair_id a1)).`3, (oget (dec_act_call_pair_id a1)).`4))
  SimStateWait
  exp1.
proof.
move => act_rel act_for3 call_pair_id.
(case act_rel; first 3 smt); last 7 smt().
move => -> _.
by rewrite /enc_univ_pair_id_key
           -/(enc_act_call_pair_id 3 1 2 (UnivKey(g ^ exp1)))
           (act_call_pair_id_enc_dec 3 1 2 (UnivKey(g ^ exp1))) oget_some.
move => ->> _; smt(act_for_id_call).
qed.

lemma act_rel_forward2_wait_state (a1 a2 : act, exp1 exp2 : exp) :
  act_rel a1 a2 exp1 exp2 =>
  act_for_id 4 a1 => is_act_call_pair_id a1 =>
  forward_rel2
  (Fw2.ForwStateWait
   ((oget (dec_act_call_pair_id a1)).`3, (oget (dec_act_call_pair_id a1)).`4))
  SimStateWait
  exp2.
proof.
move => act_rel act_for4 call_pair_id.
(case act_rel; first 3 smt); last 7 smt().
move => ->> _; smt(act_for_id_call).
move => -> _.
by rewrite /enc_univ_pair_id_key
           -/(enc_act_call_pair_id 4 2 1 (UnivKey(g ^ exp2)))
           (act_call_pair_id_enc_dec 4 2 1 (UnivKey(g ^ exp2))) oget_some.
qed.

lemma act_rel_sent_to_env1 (a1 a2 : act, exp1 exp2 : exp) :
  act_rel a1 a2 exp1 exp2 =>
  act_for_id 3 a1 => is_act_call_pair_id a1 =>
  act_rel
  (enc_act_send_pair_id 0 3
   (enc_univ_pair_id
    (oget (dec_act_call_pair_id a1)).`3
    (oget (dec_act_call_pair_id a1)).`4))
  (enc_act_send_pair_id 0 3
   (enc_univ_pair_id 2 (UnivKey (g ^ exp1))))
  exp1 exp2.
proof.
move => act_rel act_for3 call_pair_id.
((case act_rel); first 3 smt()); last 7 smt().
move => -> _.
by rewrite /enc_univ_pair_id_key
           -/(enc_act_call_pair_id 3 1 2 (UnivKey(g ^ exp1)))
           (act_call_pair_id_enc_dec 3 1 2 (UnivKey(g ^ exp1))) oget_some /=
           ActRelFw1SendToEnv.
move => ->> _; smt(act_for_id_call).
qed.

lemma act_rel_send_to_env2 (a1 a2 : act, exp1 exp2 : exp) :
  act_rel a1 a2 exp1 exp2 =>
  act_for_id 4 a1 => is_act_call_pair_id a1 =>
  act_rel
  (enc_act_send_pair_id 0 4
   (enc_univ_pair_id
    (oget (dec_act_call_pair_id a1)).`3
    (oget (dec_act_call_pair_id a1)).`4))
  (enc_act_send_pair_id 0 4
   (enc_univ_pair_id 1 (UnivKey (g ^ exp2))))
  exp1 exp2.
proof.
move => act_rel act_for4 call_pair_id.
((case act_rel); first 3 smt()); last 7 smt().
move => ->> _; smt(act_for_id_call).
move => -> _.
by rewrite /enc_univ_pair_id_key
           -/(enc_act_call_pair_id 4 2 1 (UnivKey(g ^ exp2)))
           (act_call_pair_id_enc_dec 4 2 1 (UnivKey(g ^ exp2))) oget_some /=
           ActRelFw2SendToEnv.
qed.

lemma act_rel_dh_party1_call_to_fwd1 (exp1 exp2 : exp) :
  act_rel (enc_act_call_pair_id_key 3 1 2 (g ^ exp1))
          (enc_act_call_unit 3 1) exp1 exp2.
proof.
by rewrite /enc_act_call_pair_id_key /enc_act_call_pair_id
           -/(enc_univ_pair_id_key 2 (g ^ exp1))
           /enc_act_call_unit ActRelDHParty1CallToFwd1.
qed.

lemma act_rel_dh_party2_call_to_fwd2 (exp1 exp2 : exp) :
  act_rel (enc_act_call_pair_id_key 4 2 1 (g ^ exp2))
          (enc_act_call_unit 4 2) exp1 exp2.
proof.
by rewrite /enc_act_call_pair_id_key /enc_act_call_pair_id
           -/(enc_univ_pair_id_key 1 (g ^ exp2))
           /enc_act_call_unit ActRelDHParty2CallToFwd2.
qed.

(*************** Section with Constrained Env Declared Locally ****************)

section.

declare module Env : ENV{DH, Fw1.Forw, Fw2.Forw, IF, Sim, DDHAdv}.

(* working up to proving first half of security:

lemma Exper_DH_Fw1_Fw2_DDH1_DDHAdv &m :
  Pr[Exper(DH(Fw1.Forw, Fw2.Forw), Env).main() @ &m : res] =
  Pr[DDH1(DDHAdv(Env)).main() @ &m : res].
*)

lemma DH_Fw1_Fw2_DDHAdv_Fun_party :
  equiv
  [DH(Fw1.Forw, Fw2.Forw).party ~ DDHAdv(Env).Fun.party :
   ={self_id} /\ 1 <= self_id{1} <= 2 /\
   ={id1, states}(DH, DDHAdv.Fun) /\
   DH.id1{1} = 1 /\ dh_states_pred DH.states{1} /\
   two_fmap DH.exps{1} 1 2 /\
   g ^ oget(DH.exps{1}.[1]) = DDHAdv.key1{2} /\
   g ^ oget(DH.exps{1}.[2]) = DDHAdv.key2{2} /\
   g ^ oget(DH.exps{1}.[1]) ^ oget(DH.exps{1}.[2]) = DDHAdv.key3{2} /\
   act_rel a{1} a{2} (oget DH.exps{1}.[1]) (oget DH.exps{1}.[2]) /\
   act_for_id self_id{1} a{1} ==>
   ={id1, states}(DH, DDHAdv.Fun) /\
   DH.id1{1} = 1 /\ dh_states_pred DH.states{1} /\
   two_fmap DH.exps{1} 1 2 /\
   g ^ oget(DH.exps{1}.[1]) = DDHAdv.key1{2} /\
   g ^ oget(DH.exps{1}.[2]) = DDHAdv.key2{2} /\
   g ^ oget(DH.exps{1}.[1]) ^ oget(DH.exps{1}.[2]) = DDHAdv.key3{2} /\
   act_rel res{1} res{2} (oget DH.exps{1}.[1]) (oget DH.exps{1}.[2])].
proof.
proc.
auto; progress [-delta].
by rewrite
     (act_rel_act_for_1_or_2_call_unit_eq a{1} a{2}
      (oget DH.exps{1}.[1]) (oget DH.exps{1}.[2]) self_id{2}).
apply dh_states_pred_update => //;
  [smt(in_fsetU in_fset1) |
   smt(act_rel_call_unit_ret_outside_range)].
have [->> /= | ->> /=] : self_id{2} = 1 \/ self_id{2} = 2 by smt().
rewrite act_rel_dh_party1_call_to_fwd1.
rewrite act_rel_dh_party2_call_to_fwd2.
smt(act_rel_act_for_1_or_2_call_unit).
smt(act_rel_act_for_1_or_2_call_unit).
smt(act_rel_act_for_1_or_2_call_unit).
smt(act_rel_act_for_1_or_2_call_unit).
smt(act_rel_act_for_1_or_2_call_unit).
smt(act_rel_act_for_1_or_2_call_unit).
smt(act_rel_act_for_1_or_2_call_unit).
smt(act_rel_act_for_1_or_2_call_unit).
smt(dh_states_pred_update).
by rewrite ActRelDefault.
smt(act_rel_return_unit2_imp_return_key1).
by rewrite ActRelDefault.
smt(act_rel_act_for_1_or_2_call_unit).
smt(act_rel_act_for_1_or_2_call_unit).
smt(act_rel_act_for_1_or_2_call_unit).
smt(act_rel_act_for_1_or_2_return_key1_imp_return_unit2).
smt(dh_states_pred_update).
by rewrite ActRelDefault.
by rewrite ActRelDefault.
smt(dh_states_pred_update).
have [->> | ->>] : self_id{2} = 1 \/ self_id{2} = 2 by smt().
by rewrite
     (act_rel_act_for1_return_key_unit_act_key a{1} a{2}
      (oget DH.exps{1}.[1]) (oget DH.exps{1}.[2])) //
     (act_rel_return_key a{1} a{2}
      (oget DH.exps{1}.[1]) (oget DH.exps{1}.[2])
      (oget (dec_dhs_sent (oget DDHAdv.Fun.states{2}.[1])))) //
     (dh_states_pred_sent_outside 1 DDHAdv.Fun.states{2}).
by rewrite
     (act_rel_act_for2_return_key_unit_act_key a{1} a{2}
      (oget DH.exps{1}.[1]) (oget DH.exps{1}.[2])) //
     {1}pow_pow_comm
     (act_rel_return_key a{1} a{2}
      (oget DH.exps{1}.[1]) (oget DH.exps{1}.[2])
      (oget (dec_dhs_sent (oget DDHAdv.Fun.states{2}.[2])))) //
     (dh_states_pred_sent_outside 2 DDHAdv.Fun.states{2}).
smt(act_rel_return_unit2_imp_return_key1).
smt(act_rel_return_unit2_imp_return_key1).
smt(act_rel_act_for_1_or_2_return_key1_imp_return_unit2).
smt(act_rel_act_for_1_or_2_return_key1_imp_return_unit2).
smt(act_rel_act_for_1_or_2_return_key1_imp_return_unit2).
by rewrite ActRelDefault.
by rewrite ActRelDefault.
qed.

lemma Fw1_DDHAdv_Sim_invoke :
  equiv
  [Fw1.Forw.invoke ~ DDHAdv(Env).Sim.invoke :
   ={id1, states}(DH, DDHAdv.Fun) /\
   DH.id1{1} = 1 /\ dh_states_pred DH.states{1} /\
   Fw1.Forw.self_id{1} = DDHAdv.Sim.id1{2} /\
   Fw1.Forw.self_id{1} = 3 /\
   Fw2.Forw.self_id{1} = DDHAdv.Sim.id1{2} + 1 /\
   Fw2.Forw.self_id{1} = 4 /\
   two_fmap DDHAdv.Sim.states{2} 3 4 /\
   forward_rel1 Fw1.Forw.st{1} (oget DDHAdv.Sim.states{2}.[3])
                (oget DH.exps{1}.[1]) /\
   forward_rel2 Fw2.Forw.st{1} (oget DDHAdv.Sim.states{2}.[4])
                (oget DH.exps{1}.[2]) /\
   two_fmap DH.exps{1} 1 2 /\
   g ^ oget(DH.exps{1}.[1]) = DDHAdv.key1{2} /\
   g ^ oget(DH.exps{1}.[2]) = DDHAdv.key2{2} /\
   g ^ oget(DH.exps{1}.[1]) ^ oget(DH.exps{1}.[2]) = DDHAdv.key3{2} /\
   act_rel a{1} a{2} (oget DH.exps{1}.[1]) (oget DH.exps{1}.[2]) /\
   act_for_id (DH.id1{1} + 2) a{1} ==>
   ={id1, states}(DH, DDHAdv.Fun) /\
   DH.id1{1} = 1 /\ dh_states_pred DH.states{1} /\
   Fw1.Forw.self_id{1} = DDHAdv.Sim.id1{2} /\
   Fw1.Forw.self_id{1} = 3 /\
   Fw2.Forw.self_id{1} = DDHAdv.Sim.id1{2} + 1 /\
   Fw2.Forw.self_id{1} = 4 /\
   two_fmap DDHAdv.Sim.states{2} 3 4 /\
   forward_rel1 Fw1.Forw.st{1} (oget DDHAdv.Sim.states{2}.[3])
                (oget DH.exps{1}.[1]) /\
   forward_rel2 Fw2.Forw.st{1} (oget DDHAdv.Sim.states{2}.[4])
                (oget DH.exps{1}.[2]) /\
   two_fmap DH.exps{1} 1 2 /\
   g ^ oget(DH.exps{1}.[1]) = DDHAdv.key1{2} /\
   g ^ oget(DH.exps{1}.[2]) = DDHAdv.key2{2} /\
   g ^ oget(DH.exps{1}.[1]) ^ oget(DH.exps{1}.[2]) = DDHAdv.key3{2} /\
   act_rel res{1} res{2} (oget DH.exps{1}.[1]) (oget DH.exps{1}.[2])].
proof.
proc.
seq 1 3 :
  (={id1, states}(DH, DDHAdv.Fun) /\
   DH.id1{1} = 1 /\ dh_states_pred DH.states{1} /\
   Fw1.Forw.self_id{1} = DDHAdv.Sim.id1{2} /\
   Fw1.Forw.self_id{1} = 3 /\
   Fw2.Forw.self_id{1} = DDHAdv.Sim.id1{2} + 1 /\
   Fw2.Forw.self_id{1} = 4 /\
   two_fmap DDHAdv.Sim.states{2} 3 4 /\
   forward_rel1 Fw1.Forw.st{1} (oget DDHAdv.Sim.states{2}.[3])
                (oget DH.exps{1}.[1]) /\
   forward_rel2 Fw2.Forw.st{1} (oget DDHAdv.Sim.states{2}.[4])
                (oget DH.exps{1}.[2]) /\
   two_fmap DH.exps{1} 1 2 /\
   g ^ oget(DH.exps{1}.[1]) = DDHAdv.key1{2} /\
   g ^ oget(DH.exps{1}.[2]) = DDHAdv.key2{2} /\
   g ^ oget(DH.exps{1}.[1]) ^ oget(DH.exps{1}.[2]) = DDHAdv.key3{2} /\
   act_rel a{1} a{2} (oget DH.exps{1}.[1]) (oget DH.exps{1}.[2]) /\
   act_for_id (DH.id1{1} + 2) a{1} /\
   self_id{2} = 3 /\
   st{2} = oget DDHAdv.Sim.states{2}.[3] /\
   forward_rel1 Fw1.Forw.st{1} st{2} (oget DH.exps{1}.[1]) /\
   ={a'} /\ a'{1} = act_def).
auto; progress [-delta]; smt(act_rel_act_for_id).
if; first smt().
if.
progress [-delta].
apply (act_rel_call_pair_id_imp_call_unit a{1} a{2} 
       (oget DH.exps{1}.[1]) (oget DH.exps{1}.[2])) => //.
by rewrite
     (act_rel_act_for3_call_unit_imp_call_pair_id a{1} a{2} 
      (oget DH.exps{1}.[1]) (oget DH.exps{1}.[2])) //
     -(act_rel_act_for_id a{1} a{2} 
       (oget DH.exps{1}.[1]) (oget DH.exps{1}.[2])).
rcondt{1} 2.
auto; progress [-delta].
by rewrite (act_for_id_call_pair_id 3 a{hr}).
smt(act_rel_call_pair_id2).
auto; progress [-delta].
by rewrite two_fmap_update.
rewrite getP_eq oget_some.
by apply
     (act_rel_forward1_wait_state
      a{1} a{2} (oget DH.exps{1}.[1]) (oget DH.exps{1}.[2])).
by rewrite getP.
by apply
     (act_rel_sent_to_env1 a{1} a{2}
      (oget DH.exps{1}.[1]) (oget DH.exps{1}.[2])).
auto; progress [-delta]; by rewrite ActRelDefault.
if; first progress [-delta]; [smt() | smt(forward_rel1_wait)].
sp 1 0.
if; first progress [-delta]; smt(act_rel_send_unit_iff).
auto; progress [-delta]; last 4
  smt(act_for_id_send is_act_send_unit_up dec_act_send_unit_up).
by rewrite two_fmap_update.
by rewrite getP_eq oget_some.
by rewrite getP.
smt(act_rel_return_key_unit1).
auto; progress [-delta]; by rewrite ActRelDefault.
auto; progress [-delta]; by rewrite ActRelDefault.
qed.

lemma Fw2_DDHAdv_Sim_invoke :
  equiv
  [Fw2.Forw.invoke ~ DDHAdv(Env).Sim.invoke :
   ={id1, states}(DH, DDHAdv.Fun) /\
   DH.id1{1} = 1 /\ dh_states_pred DH.states{1} /\
   Fw1.Forw.self_id{1} = DDHAdv.Sim.id1{2} /\
   Fw1.Forw.self_id{1} = 3 /\
   Fw2.Forw.self_id{1} = DDHAdv.Sim.id1{2} + 1 /\
   Fw2.Forw.self_id{1} = 4 /\
   two_fmap DDHAdv.Sim.states{2} 3 4 /\
   forward_rel1 Fw1.Forw.st{1} (oget DDHAdv.Sim.states{2}.[3])
                (oget DH.exps{1}.[1]) /\
   forward_rel2 Fw2.Forw.st{1} (oget DDHAdv.Sim.states{2}.[4])
                (oget DH.exps{1}.[2]) /\
   two_fmap DH.exps{1} 1 2 /\
   g ^ oget(DH.exps{1}.[1]) = DDHAdv.key1{2} /\
   g ^ oget(DH.exps{1}.[2]) = DDHAdv.key2{2} /\
   g ^ oget(DH.exps{1}.[1]) ^ oget(DH.exps{1}.[2]) = DDHAdv.key3{2} /\
   act_rel a{1} a{2} (oget DH.exps{1}.[1]) (oget DH.exps{1}.[2]) /\
   act_for_id (DH.id1{1} + 3) a{1} ==>
   ={id1, states}(DH, DDHAdv.Fun) /\
   DH.id1{1} = 1 /\ dh_states_pred DH.states{1} /\
   Fw1.Forw.self_id{1} = DDHAdv.Sim.id1{2} /\
   Fw1.Forw.self_id{1} = 3 /\
   Fw2.Forw.self_id{1} = DDHAdv.Sim.id1{2} + 1 /\
   Fw2.Forw.self_id{1} = 4 /\
   two_fmap DDHAdv.Sim.states{2} 3 4 /\
   forward_rel1 Fw1.Forw.st{1} (oget DDHAdv.Sim.states{2}.[3])
                (oget DH.exps{1}.[1]) /\
   forward_rel2 Fw2.Forw.st{1} (oget DDHAdv.Sim.states{2}.[4])
                (oget DH.exps{1}.[2]) /\
   two_fmap DH.exps{1} 1 2 /\
   g ^ oget(DH.exps{1}.[1]) = DDHAdv.key1{2} /\
   g ^ oget(DH.exps{1}.[2]) = DDHAdv.key2{2} /\
   g ^ oget(DH.exps{1}.[1]) ^ oget(DH.exps{1}.[2]) = DDHAdv.key3{2} /\
   act_rel res{1} res{2} (oget DH.exps{1}.[1]) (oget DH.exps{1}.[2])].
proof.
proc.
seq 1 3 :
  (={id1, states}(DH, DDHAdv.Fun) /\
   DH.id1{1} = 1 /\ dh_states_pred DH.states{1} /\
   Fw1.Forw.self_id{1} = DDHAdv.Sim.id1{2} /\
   Fw1.Forw.self_id{1} = 3 /\
   Fw2.Forw.self_id{1} = DDHAdv.Sim.id1{2} + 1 /\
   Fw2.Forw.self_id{1} = 4 /\
   two_fmap DDHAdv.Sim.states{2} 3 4 /\
   forward_rel1 Fw1.Forw.st{1} (oget DDHAdv.Sim.states{2}.[3])
                (oget DH.exps{1}.[1]) /\
   forward_rel2 Fw2.Forw.st{1} (oget DDHAdv.Sim.states{2}.[4])
                (oget DH.exps{1}.[2]) /\
   two_fmap DH.exps{1} 1 2 /\
   g ^ oget(DH.exps{1}.[1]) = DDHAdv.key1{2} /\
   g ^ oget(DH.exps{1}.[2]) = DDHAdv.key2{2} /\
   g ^ oget(DH.exps{1}.[1]) ^ oget(DH.exps{1}.[2]) = DDHAdv.key3{2} /\
   act_rel a{1} a{2} (oget DH.exps{1}.[1]) (oget DH.exps{1}.[2]) /\
   act_for_id (DH.id1{1} + 3) a{1} /\
   self_id{2} = 4 /\
   st{2} = oget DDHAdv.Sim.states{2}.[4] /\
   forward_rel2 Fw2.Forw.st{1} st{2} (oget DH.exps{1}.[2]) /\
   ={a'} /\ a'{1} = act_def).
auto; progress [-delta]; smt(act_rel_act_for_id act_for_id_exclusive).
if; first smt().
if.
progress [-delta].
apply (act_rel_call_pair_id_imp_call_unit a{1} a{2} 
       (oget DH.exps{1}.[1]) (oget DH.exps{1}.[2])) => //.
by rewrite
     (act_rel_act_for4_call_unit_imp_call_pair_id a{1} a{2} 
      (oget DH.exps{1}.[1]) (oget DH.exps{1}.[2])) //
     -(act_rel_act_for_id a{1} a{2} 
       (oget DH.exps{1}.[1]) (oget DH.exps{1}.[2])).
rcondt{1} 2.
auto; progress [-delta].
by rewrite (act_for_id_call_pair_id 4 a{hr}).
smt(act_rel_call_pair_id2).
auto; progress [-delta].
by rewrite two_fmap_update.
by rewrite getP /=.
rewrite getP /= oget_some.
by apply
     (act_rel_forward2_wait_state
      a{1} a{2} (oget DH.exps{1}.[1]) (oget DH.exps{1}.[2])).
by apply
     (act_rel_send_to_env2 a{1} a{2}
      (oget DH.exps{1}.[1]) (oget DH.exps{1}.[2])).
auto; progress [-delta]; by rewrite ActRelDefault.
if; first progress [-delta]; [smt() | smt(forward_rel2_wait)].
sp 1 0.
if; first progress [-delta]; smt(act_rel_send_unit_iff).
auto; progress [-delta]; last 4
  smt(act_for_id_send is_act_send_unit_up dec_act_send_unit_up).
by rewrite two_fmap_update.
by rewrite getP.
by rewrite getP_eq oget_some.
smt(act_rel_return_key_unit2).
auto; progress [-delta]; by rewrite ActRelDefault.
auto; progress [-delta]; by rewrite ActRelDefault.
qed.

lemma DH_Fw1_Fw2_DDHAdv_Fun_loop :
  equiv
  [DH(Fw1.Forw, Fw2.Forw).loop ~ DDHAdv(Env).Fun.loop :
   ={id1, states}(DH, DDHAdv.Fun) /\
   DH.id1{1} = 1 /\ dh_states_pred DH.states{1} /\
   Fw1.Forw.self_id{1} = DDHAdv.Sim.id1{2} /\
   Fw1.Forw.self_id{1} = 3 /\
   Fw2.Forw.self_id{1} = DDHAdv.Sim.id1{2} + 1 /\
   Fw2.Forw.self_id{1} = 4 /\
   two_fmap DDHAdv.Sim.states{2} 3 4 /\
   forward_rel1 Fw1.Forw.st{1} (oget DDHAdv.Sim.states{2}.[3])
                (oget DH.exps{1}.[1]) /\
   forward_rel2 Fw2.Forw.st{1} (oget DDHAdv.Sim.states{2}.[4])
                (oget DH.exps{1}.[2]) /\
   two_fmap DH.exps{1} 1 2 /\
   g ^ oget(DH.exps{1}.[1]) = DDHAdv.key1{2} /\
   g ^ oget(DH.exps{1}.[2]) = DDHAdv.key2{2} /\
   g ^ oget(DH.exps{1}.[1]) ^ oget(DH.exps{1}.[2]) = DDHAdv.key3{2} /\
   act_rel a{1} a{2} (oget DH.exps{1}.[1]) (oget DH.exps{1}.[2]) ==>
   ={res} /\
   ={id1, states}(DH, DDHAdv.Fun) /\
   DH.id1{1} = 1 /\ dh_states_pred DH.states{1} /\
   Fw1.Forw.self_id{1} = DDHAdv.Sim.id1{2} /\
   Fw1.Forw.self_id{1} = 3 /\
   Fw2.Forw.self_id{1} = DDHAdv.Sim.id1{2} + 1 /\
   Fw2.Forw.self_id{1} = 4 /\
   two_fmap DDHAdv.Sim.states{2} 3 4 /\
   forward_rel1 Fw1.Forw.st{1} (oget DDHAdv.Sim.states{2}.[3])
                (oget DH.exps{1}.[1]) /\
   forward_rel2 Fw2.Forw.st{1} (oget DDHAdv.Sim.states{2}.[4])
                (oget DH.exps{1}.[2]) /\
   two_fmap DH.exps{1} 1 2 /\
   g ^ oget(DH.exps{1}.[1]) = DDHAdv.key1{2} /\
   g ^ oget(DH.exps{1}.[2]) = DDHAdv.key2{2} /\
   g ^ oget(DH.exps{1}.[1]) ^ oget(DH.exps{1}.[2]) = DDHAdv.key3{2}].
proof.
proc.
while
  (={id1, states}(DH, DDHAdv.Fun) /\
   DH.id1{1} = 1 /\ dh_states_pred DH.states{1} /\
   Fw1.Forw.self_id{1} = DDHAdv.Sim.id1{2} /\
   Fw1.Forw.self_id{1} = 3 /\
   Fw2.Forw.self_id{1} = DDHAdv.Sim.id1{2} + 1 /\
   Fw2.Forw.self_id{1} = 4 /\
   two_fmap DDHAdv.Sim.states{2} 3 4 /\
   forward_rel1 Fw1.Forw.st{1} (oget DDHAdv.Sim.states{2}.[3])
                (oget DH.exps{1}.[1]) /\
   forward_rel2 Fw2.Forw.st{1} (oget DDHAdv.Sim.states{2}.[4])
                (oget DH.exps{1}.[2]) /\
   two_fmap DH.exps{1} 1 2 /\
   g ^ oget(DH.exps{1}.[1]) = DDHAdv.key1{2} /\
   g ^ oget(DH.exps{1}.[2]) = DDHAdv.key2{2} /\
   g ^ oget(DH.exps{1}.[1]) ^ oget(DH.exps{1}.[2]) = DDHAdv.key3{2} /\
   act_rel a{1} a{2} (oget DH.exps{1}.[1]) (oget DH.exps{1}.[2])).
if => //.
progress [-delta]; smt(act_rel_act_for_id).
call DH_Fw1_Fw2_DDHAdv_Fun_party.
auto; progress [-delta]; smt(act_rel_act_for_id_range).
if => //.
progress [-delta]; smt(act_rel_act_for_id).
call DH_Fw1_Fw2_DDHAdv_Fun_party.
auto; progress [-delta]; smt(act_rel_act_for_id_range).
wp; if{1}.
simplify.
call Fw1_DDHAdv_Sim_invoke.
auto; progress [-delta].
apply (act_rel_guard result_L result_R (oget DH.exps{1}.[1])
       (oget DH.exps{1}.[2])) => //.
apply (act_rel_guard_range_lr result_L result_R (oget DH.exps{1}.[1])
       (oget DH.exps{1}.[2])) => //.
apply (act_rel_guard_range_rl result_L result_R (oget DH.exps{1}.[1])
       (oget DH.exps{1}.[2])) => //.
call Fw2_DDHAdv_Sim_invoke.
auto; progress [-delta].
apply act_for_id_range_1_4_not_3 => //.
apply (act_rel_guard result_L result_R (oget DH.exps{1}.[1])
       (oget DH.exps{1}.[2])) => //.
apply (act_rel_guard_range_lr result_L result_R (oget DH.exps{1}.[1])
       (oget DH.exps{1}.[2])) => //.
apply (act_rel_guard_range_rl result_L result_R (oget DH.exps{1}.[1])
       (oget DH.exps{1}.[2])) => //.
auto; progress [-delta].
smt(act_rel_act_for_id_range).
smt(act_rel_act_for_id_range).
smt(act_rel_not_act_for_range_eq).
qed.

lemma DH_Fw1_Fw2_DDHAdv_Fun_invoke :
  equiv
  [DH(Fw1.Forw, Fw2.Forw).invoke ~ DDHAdv(Env).Fun.invoke :
   ={a} /\
   ={id1, states}(DH, DDHAdv.Fun) /\
   DH.id1{1} = 1 /\ dh_states_pred DH.states{1} /\
   Fw1.Forw.self_id{1} = DDHAdv.Sim.id1{2} /\
   Fw1.Forw.self_id{1} = 3 /\
   Fw2.Forw.self_id{1} = DDHAdv.Sim.id1{2} + 1 /\
   Fw2.Forw.self_id{1} = 4 /\
   two_fmap DDHAdv.Sim.states{2} 3 4 /\
   forward_rel1 Fw1.Forw.st{1} (oget DDHAdv.Sim.states{2}.[3])
                (oget DH.exps{1}.[1]) /\
   forward_rel2 Fw2.Forw.st{1} (oget DDHAdv.Sim.states{2}.[4])
                (oget DH.exps{1}.[2]) /\
   two_fmap DH.exps{1} 1 2 /\
   g ^ oget(DH.exps{1}.[1]) = DDHAdv.key1{2} /\
   g ^ oget(DH.exps{1}.[2]) = DDHAdv.key2{2} /\
   g ^ oget(DH.exps{1}.[1]) ^ oget(DH.exps{1}.[2]) = DDHAdv.key3{2} ==>
   ={res} /\
   ={id1, states}(DH, DDHAdv.Fun) /\
   DH.id1{1} = 1 /\ dh_states_pred DH.states{1} /\
   Fw1.Forw.self_id{1} = DDHAdv.Sim.id1{2} /\
   Fw1.Forw.self_id{1} = 3 /\
   Fw2.Forw.self_id{1} = DDHAdv.Sim.id1{2} + 1 /\
   Fw2.Forw.self_id{1} = 4 /\
   two_fmap DDHAdv.Sim.states{2} 3 4 /\
   forward_rel1 Fw1.Forw.st{1} (oget DDHAdv.Sim.states{2}.[3])
                (oget DH.exps{1}.[1]) /\
   forward_rel2 Fw2.Forw.st{1} (oget DDHAdv.Sim.states{2}.[4])
                (oget DH.exps{1}.[2]) /\
   two_fmap DH.exps{1} 1 2 /\
   g ^ oget(DH.exps{1}.[1]) = DDHAdv.key1{2} /\
   g ^ oget(DH.exps{1}.[2]) = DDHAdv.key2{2} /\
   g ^ oget(DH.exps{1}.[1]) ^ oget(DH.exps{1}.[2]) = DDHAdv.key3{2}].
proof.
proc.
seq 2 2 :
  (={a, ignore} /\
   ={id1, states}(DH, DDHAdv.Fun) /\
   DH.id1{1} = 1 /\ dh_states_pred DH.states{1} /\
   Fw1.Forw.self_id{1} = DDHAdv.Sim.id1{2} /\
   Fw1.Forw.self_id{1} = 3 /\
   Fw2.Forw.self_id{1} = DDHAdv.Sim.id1{2} + 1 /\
   Fw2.Forw.self_id{1} = 4 /\
   two_fmap DDHAdv.Sim.states{2} 3 4 /\
   forward_rel1 Fw1.Forw.st{1} (oget DDHAdv.Sim.states{2}.[3])
                (oget DH.exps{1}.[1]) /\
   forward_rel2 Fw2.Forw.st{1} (oget DDHAdv.Sim.states{2}.[4])
                (oget DH.exps{1}.[2]) /\
   two_fmap DH.exps{1} 1 2 /\
   g ^ oget(DH.exps{1}.[1]) = DDHAdv.key1{2} /\
   g ^ oget(DH.exps{1}.[2]) = DDHAdv.key2{2} /\
   g ^ oget(DH.exps{1}.[1]) ^ oget(DH.exps{1}.[2]) = DDHAdv.key3{2} /\
   (! ignore{1} => 
    act_rel a{1} a{2} (oget DH.exps{1}.[1]) (oget DH.exps{1}.[2]))).
auto; progress [-delta].
apply act_rel_init_call_unit => //.
apply act_rel_init_send_unit => //.
if => //; first auto.
call DH_Fw1_Fw2_DDHAdv_Fun_loop; auto; progress [-delta]; smt().
qed.

lemma Exper_DH_Fw1_Fw2_DDH1_DDHAdv &m :
  Pr[Exper(DH(Fw1.Forw, Fw2.Forw), Env).main() @ &m : res] =
  Pr[DDH1(DDHAdv(Env)).main() @ &m : res].
proof.
byequiv => //.
proc.
inline DH(Fw1.Forw, Fw2.Forw).init Fw1.Forw.init Fw2.Forw.init.
inline DDHAdv(Env).main DDHAdv(Env).Fun.init DDHAdv(Env).Sim.init.
wp.
seq 12 14 :
  (={id1, states}(DH, DDHAdv.Fun) /\
   DH.id1{1} = 1 /\ dh_states_pred DH.states{1} /\
   Fw1.Forw.self_id{1} = DDHAdv.Sim.id1{2} /\
   Fw1.Forw.self_id{1} = 3 /\
   Fw2.Forw.self_id{1} = DDHAdv.Sim.id1{2} + 1 /\
   Fw2.Forw.self_id{1} = 4 /\
   two_fmap DDHAdv.Sim.states{2} 3 4 /\
   forward_rel1 Fw1.Forw.st{1} (oget DDHAdv.Sim.states{2}.[3])
                (oget DH.exps{1}.[1]) /\
   forward_rel2 Fw2.Forw.st{1} (oget DDHAdv.Sim.states{2}.[4])
                (oget DH.exps{1}.[2]) /\
   two_fmap DH.exps{1} 1 2 /\
   g ^ oget(DH.exps{1}.[1]) = DDHAdv.key1{2} /\
   g ^ oget(DH.exps{1}.[2]) = DDHAdv.key2{2} /\
   g ^ oget(DH.exps{1}.[1]) ^ oget(DH.exps{1}.[2]) = DDHAdv.key3{2}).
swap{1} [3..4] -2.
auto; progress [-delta].
rewrite dh_states_pred_init.
by rewrite two_fmap_init.
by rewrite two_fmap_init_get1.
by rewrite two_fmap_init_get2.
by rewrite two_fmap_init.
by rewrite two_fmap_init_get1.
by rewrite two_fmap_init_get2.
by rewrite two_fmap_init_get1 // two_fmap_init_get2.
call
  (_ :
   ={id1, states}(DH, DDHAdv.Fun) /\
   DH.id1{1} = 1 /\ dh_states_pred DH.states{1} /\
   Fw1.Forw.self_id{1} = DDHAdv.Sim.id1{2} /\
   Fw1.Forw.self_id{1} = 3 /\
   Fw2.Forw.self_id{1} = DDHAdv.Sim.id1{2} + 1 /\
   Fw2.Forw.self_id{1} = 4 /\
   two_fmap DDHAdv.Sim.states{2} 3 4 /\
   forward_rel1 Fw1.Forw.st{1} (oget DDHAdv.Sim.states{2}.[3])
                (oget DH.exps{1}.[1]) /\
   forward_rel2 Fw2.Forw.st{1} (oget DDHAdv.Sim.states{2}.[4])
                (oget DH.exps{1}.[2]) /\
   two_fmap DH.exps{1} 1 2 /\
   g ^ oget(DH.exps{1}.[1]) = DDHAdv.key1{2} /\
   g ^ oget(DH.exps{1}.[2]) = DDHAdv.key2{2} /\
   g ^ oget(DH.exps{1}.[1]) ^ oget(DH.exps{1}.[2]) = DDHAdv.key3{2}).
conseq DH_Fw1_Fw2_DDHAdv_Fun_invoke.
auto.
qed.

(* working up to proving second half of security:

lemma DDH2_DDHAdv_Exper_IF_Sim &m :
  Pr[DDH2(DDHAdv(Env)).main() @ &m : res] =
  Pr[Exper(IF(Sim), Env).main() @ &m : res].
*)

lemma DDHAdv_Sim_Sim_party :
  equiv
  [DDHAdv(Env).Sim.invoke ~ Sim.invoke :
   ={a} /\ ={id1, states}(DDHAdv.Sim, Sim) /\
   DDHAdv.Sim.id1{1} = 3 /\ act_for_id_range 3 4 a{1} /\
   two_fmap Sim.exps{2} 3 4 /\
   DDHAdv.key1{1} = g ^ oget(Sim.exps{2}.[3]) /\
   DDHAdv.key2{1} = g ^ oget(Sim.exps{2}.[4]) ==>
   ={res} /\ act_for_id_range 0 4 res{1} /\
   ={id1, states}(DDHAdv.Sim, Sim)].
proof.
proc; auto; progress [-delta].
by case (act_for_id 3 a{2}).
by case (act_for_id 3 a{2}).
qed.

lemma DDHAdv_Fun_IF_Sim_party :
  equiv
  [DDHAdv(Env).Fun.party ~ IF(Sim).party :
   ={a, self_id} /\ 1 <= self_id{1} <= 2 /\
   ={id1, states}(DDHAdv.Fun, IF) /\ DDHAdv.Fun.id1{1} = 1 /\
   DDHAdv.key3{1} = g ^ IF.exp{2} ==>
   ={res} /\ ={id1, states}(DDHAdv.Fun, IF)].
proof.
proc; auto.
qed.

lemma DDHAdv_Fun_IF_Sim_loop :
  equiv
  [DDHAdv(Env).Fun.loop ~ IF(Sim).loop :
   ={a} /\ ={id1, states}(DDHAdv.Fun, IF) /\
   ={id1, states}(DDHAdv.Sim, Sim) /\
   DDHAdv.Fun.id1{1} = 1 /\ DDHAdv.Sim.id1{1} = 3 /\
   two_fmap Sim.exps{2} 3 4 /\
   DDHAdv.key1{1} = g ^ oget(Sim.exps{2}.[3]) /\
   DDHAdv.key2{1} = g ^ oget(Sim.exps{2}.[4]) /\
   DDHAdv.key3{1} = g ^ IF.exp{2} ==>
   ={res} /\ ={id1, states}(DDHAdv.Fun, IF) /\
   ={id1, states}(DDHAdv.Sim, Sim)].
proof.
proc.
while
  (={a} /\ ={id1, states}(DDHAdv.Fun, IF) /\
   ={id1, states}(DDHAdv.Sim, Sim) /\
   DDHAdv.Fun.id1{1} = 1 /\ DDHAdv.Sim.id1{1} = 3 /\
   two_fmap Sim.exps{2} 3 4 /\
   DDHAdv.key1{1} = g ^ oget(Sim.exps{2}.[3]) /\
   DDHAdv.key2{1} = g ^ oget(Sim.exps{2}.[4]) /\
   DDHAdv.key3{1} = g ^ IF.exp{2}).
if => //.
call DDHAdv_Fun_IF_Sim_party; auto.
if => //.
call DDHAdv_Fun_IF_Sim_party; auto.
wp; call DDHAdv_Sim_Sim_party; auto; progress [-delta].
progress [-delta]; by apply act_for_id_range_1_4_not_1_2.
auto.
qed.

lemma DDHAdv_Fun_IF_Sim_invoke :
  equiv
  [DDHAdv(Env).Fun.invoke ~ IF(Sim).invoke :
   ={a} /\ ={id1, states}(DDHAdv.Fun, IF) /\
   ={id1, states}(DDHAdv.Sim, Sim) /\
   DDHAdv.Fun.id1{1} = 1 /\ DDHAdv.Sim.id1{1} = 3 /\
   two_fmap Sim.exps{2} 3 4 /\
   DDHAdv.key1{1} = g ^ oget(Sim.exps{2}.[3]) /\
   DDHAdv.key2{1} = g ^ oget(Sim.exps{2}.[4]) /\
   DDHAdv.key3{1} = g ^ IF.exp{2} ==>
   ={res} /\ ={id1, states}(DDHAdv.Fun, IF) /\
   ={id1, states}(DDHAdv.Sim, Sim) /\
   DDHAdv.Fun.id1{1} = 1 /\ DDHAdv.Sim.id1{1} = 3 /\
   two_fmap Sim.exps{2} 3 4 /\
   DDHAdv.key1{1} = g ^ oget(Sim.exps{2}.[3]) /\
   DDHAdv.key2{1} = g ^ oget(Sim.exps{2}.[4]) /\
   DDHAdv.key3{1} = g ^ IF.exp{2}].
proof.
proc.
seq 2 2 :
  (={a, ignore} /\ ={id1, states}(DDHAdv.Fun, IF) /\
   ={id1, states}(DDHAdv.Sim, Sim) /\
   DDHAdv.Fun.id1{1} = 1 /\ DDHAdv.Sim.id1{1} = 3 /\
   two_fmap Sim.exps{2} 3 4 /\
   DDHAdv.key1{1} = g ^ oget(Sim.exps{2}.[3]) /\
   DDHAdv.key2{1} = g ^ oget(Sim.exps{2}.[4]) /\
   DDHAdv.key3{1} = g ^ IF.exp{2}); first auto.
if => //; first auto.
call DDHAdv_Fun_IF_Sim_loop; auto.
qed.

lemma DDH2_DDHAdv_Exper_IF_Sim &m :
  Pr[DDH2(DDHAdv(Env)).main() @ &m : res] =
  Pr[Exper(IF(Sim), Env).main() @ &m : res].
proof.
byequiv => //; proc.
inline DDHAdv(Env).main DDHAdv(Env).Fun.init DDHAdv(Env).Sim.init.
inline IF(Sim).init Sim.init.
wp.
seq 15 10 :
  (={id1, states}(DDHAdv.Fun, IF) /\ ={id1, states}(DDHAdv.Sim, Sim) /\
   DDHAdv.Fun.id1{1} = 1 /\ DDHAdv.Sim.id1{1} = 3 /\
   two_fmap Sim.exps{2} 3 4 /\
   DDHAdv.key1{1} = g ^ oget(Sim.exps{2}.[3]) /\
   DDHAdv.key2{1} = g ^ oget(Sim.exps{2}.[4]) /\
   DDHAdv.key3{1} = g ^ IF.exp{2}).
swap{2} [8 .. 9] -5.
auto; progress [-delta].
by rewrite two_fmap_init.
by rewrite two_fmap_init_get1.
by rewrite two_fmap_init_get2.
call
  (_ :
   ={id1, states}(DDHAdv.Fun, IF) /\ ={id1, states}(DDHAdv.Sim, Sim) /\
   DDHAdv.Fun.id1{1} = 1 /\ DDHAdv.Sim.id1{1} = 3 /\
   two_fmap Sim.exps{2} 3 4 /\
   DDHAdv.key1{1} = g ^ oget(Sim.exps{2}.[3]) /\
   DDHAdv.key2{1} = g ^ oget(Sim.exps{2}.[4]) /\
   DDHAdv.key3{1} = g ^ IF.exp{2}).
conseq DDHAdv_Fun_IF_Sim_invoke => //.
auto.
qed.

(* putting both halves together: *)

lemma Sec &m :
  `| Pr[Exper(DH(Fw1.Forw, Fw2.Forw), Env).main() @ &m : res] -
     Pr[Exper(IF(Sim), Env).main() @ &m : res] | =
   `| Pr[DDH1(DDHAdv(Env)).main() @ &m : res] -
      Pr[DDH2(DDHAdv(Env)).main() @ &m : res] |.
proof.
by rewrite (DDH2_DDHAdv_Exper_IF_Sim &m)
           (Exper_DH_Fw1_Fw2_DDH1_DDHAdv &m).
qed.

end section.

lemma Security (Env <: ENV{DH, Fw1.Forw, Fw2.Forw, IF, Sim, DDHAdv}) &m :
    `|Pr[Exper(DH(Fw1.Forw, Fw2.Forw), Env).main() @ &m : res] -
      Pr[Exper(IF(Sim), Env).main() @ &m : res]| =
    `|Pr[DDH1(DDHAdv(Env)).main() @ &m : res] -
      Pr[DDH2(DDHAdv(Env)).main() @ &m : res]|.
proof. apply (Sec Env &m). qed.
