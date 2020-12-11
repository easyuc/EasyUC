(* Forward.ec *)

(* Ideal Forwarding Functionality *)

(* This functionality implements authenticated forwarding (Fauth),
   where the adversary is asked to approve the forwarding of a value,
   but may not corrupt either the value or its destination/source *)

prover quorum=2 ["Alt-Ergo" "Z3"].

require import AllCore List UCCore.

(* begin theory parameters *)

(* port index of adversary that functionality communicates with *)

op adv_pi : int.

axiom fwd_pi_uniq : uniq [adv_pi; 0].

(* end theory parameters *)

(* basic direct interface for the single party, with port index 1 *)

theory FwDir_.

(* input message: request sent to port index 1 of forwarding
   functionality: pt1 is asking to forward u to pt2 *)

type fw_req =
  {fw_req_func : addr;   (* address of functionality *)
   fw_req_pt1  : port;   (* source = port requesting forwarding *)
   (* data: *)
   fw_req_pt2  : port;   (* port being forwarded to *)
   fw_req_u    : univ}.  (* universe value to be forwarded *)

op enc_fw_req (x : fw_req) : msg =
  (Dir, (x.`fw_req_func, 1), x.`fw_req_pt1,
   0,  (* no messages from which this must be distinct *)
   (epdp_pair_univ epdp_port_univ epdp_id).`enc
    (x.`fw_req_pt2, x.`fw_req_u)).

op nosmt dec_fw_req (m : msg) : fw_req option =
  let (mod, pt1, pt2, tag, v) = m
  in (mod = Adv \/ pt1.`2 <> 1 \/ tag <> 0) ?
     None :
     match (epdp_pair_univ epdp_port_univ epdp_id).`dec v with
     | None   => None
     | Some p =>
         let (pt2', u) = p
         in Some
            {|fw_req_func = pt1.`1; fw_req_pt1 = pt2;
              fw_req_pt2 = pt2'; fw_req_u = u|}
     end.

op epdp_fw_req_msg = {|enc = enc_fw_req; dec = dec_fw_req|}.

lemma valid_epdp_fw_req_msg : valid_epdp epdp_fw_req_msg.
proof.
apply epdp_intro.
move => x.
rewrite /epdp_fw_req_msg /= /dec_fw_req /enc_fw_req /=
        !(epdp, epdp_sub) /=.
by case x.
move => [mod pt1 pt2 tag u] v.
rewrite /epdp_fw_req_msg /dec_fw_req /enc_fw_req /=.
case (mod = Adv \/ pt1.`2 <> 1 \/ tag <> 0) => //.
rewrite !negb_or /= not_adv => [#] -> pt1_2 -> match_eq_some /=.
have val_u :
  (epdp_pair_univ epdp_port_univ epdp_id).`dec u =
  Some (v.`fw_req_pt2, v.`fw_req_u).
  move : match_eq_some.
  case ((epdp_pair_univ epdp_port_univ epdp_id).`dec u) => //.
  by case.
move : match_eq_some.
rewrite val_u /= => <- /=.
split; first move : pt1_2; by case pt1.
by rewrite (epdp_dec_enc _ _ u) 1:!epdp_sub.
qed.

hint simplify [eqtrue] valid_epdp_fw_req_msg.
hint rewrite epdp : valid_epdp_fw_req_msg.

lemma eq_of_valid_fw_req (m : msg) :
  is_valid epdp_fw_req_msg m =>
  m =
  let x = oget (epdp_fw_req_msg.`dec m) in
  (Dir,
   (x.`fw_req_func, 1),
   x.`fw_req_pt1,
   0,
   (epdp_pair_univ epdp_port_univ epdp_id).`enc
    (x.`fw_req_pt2, x.`fw_req_u)).
proof.
rewrite /is_valid.
move => val_m.
have [] x : exists (x : fw_req), epdp_fw_req_msg.`dec m = Some x.
  exists (oget (dec_fw_req m)); by rewrite -some_oget.
case x => x1 x2 x3 x4.
move => /(epdp_dec_enc _ _ _ valid_epdp_fw_req_msg) <-.
by rewrite !epdp.
qed.

(* output message: response sent from port index 1 of forwarding
   functionality to pt2, completing the forwarding of u that was
   requested by pt1 *)

type fw_rsp =
  {fw_rsp_func : addr;   (* address of functionality *)
   fw_rsp_pt2  : port;   (* destination = port being forwarded to *)
   (* data: *)
   fw_rsp_pt1  : port;   (* port requesting forwarding *)
   fw_rsp_u    : univ}.  (* universe value to be forwarded *)

op enc_fw_rsp (x : fw_rsp) : msg =
  (Dir, x.`fw_rsp_pt2, (x.`fw_rsp_func, 1),
   0,  (* no messages from which this must be distinct *)
   (epdp_pair_univ epdp_port_univ epdp_id).`enc (x.`fw_rsp_pt1, x.`fw_rsp_u)).

op nosmt dec_fw_rsp (m : msg) : fw_rsp option =
  let (mod, pt1, pt2, tag, v) = m
  in (mod = Adv \/ pt2.`2 <> 1 \/ tag <> 0) ?
     None :
     match (epdp_pair_univ epdp_port_univ epdp_id).`dec v with
     | None   => None
     | Some p =>
         let (pt1', u) = p
         in Some
            {|fw_rsp_func = pt2.`1; fw_rsp_pt1 = pt1';
              fw_rsp_pt2 = pt1; fw_rsp_u = u|}
     end.

op epdp_fw_rsp_msg = {|enc = enc_fw_rsp; dec = dec_fw_rsp|}.

lemma valid_epdp_fw_rsp_msg : valid_epdp epdp_fw_rsp_msg.
proof.
apply epdp_intro.
move => x.
rewrite /epdp_fw_rsp_msg /= /dec_fw_rsp /enc_fw_rsp /=
        !(epdp, epdp_sub) /=.
by case x.
move => [mod pt1 pt2 tag u] v.
rewrite /epdp_fw_rsp_msg /dec_fw_rsp /enc_fw_rsp /=.
case (mod = Adv \/ pt2.`2 <> 1 \/ tag <> 0) => //.
rewrite !negb_or /= not_adv => [#] -> pt2_2 -> match_eq_some /=.
have val_u :
  (epdp_pair_univ epdp_port_univ epdp_id).`dec u =
  Some (v.`fw_rsp_pt1, v.`fw_rsp_u).
  move : match_eq_some.
  case ((epdp_pair_univ epdp_port_univ epdp_id).`dec u) => //.
  by case.
move : match_eq_some.
rewrite val_u /= => <- /=.
split; first move : pt2_2; by case pt2.
by rewrite (epdp_dec_enc _ _ u) 1:!epdp_sub.
qed.

hint simplify [eqtrue] valid_epdp_fw_rsp_msg.
hint rewrite epdp : valid_epdp_fw_rsp_msg.

lemma eq_of_valid_fw_rsp (m : msg) :
  is_valid epdp_fw_rsp_msg m =>
  m =
  let x = oget (epdp_fw_rsp_msg.`dec m) in
  (Dir,
   x.`fw_rsp_pt2,
   (x.`fw_rsp_func, 1),
   0,
   (epdp_pair_univ epdp_port_univ epdp_id).`enc
    (x.`fw_rsp_pt1, x.`fw_rsp_u)).
proof.
rewrite /is_valid.
move => val_m.
have [] x : exists (x : fw_rsp), epdp_fw_rsp_msg.`dec m = Some x.
  exists (oget (dec_fw_rsp m)); by rewrite -some_oget.
case x => x1 x2 x3 x4.
move => /(epdp_dec_enc _ _ _ valid_epdp_fw_rsp_msg) <-.
by rewrite !epdp.
qed.

end FwDir_.

theory FwDir.  (* composite direct interface *)

clone FwDir_ as D.

end FwDir.

(* basic adversarial interface, with port index 2 (number of parties +
   1) *)

theory FwAdv.

(* message from forwarding functionality to adversary, letting it
   observe that the functionality is proposing to forward u to
   pt2 on behalf of pt1 *)

type fw_obs =
  {fw_obs_func : addr;   (* address of functionality *)
   fw_obs_adv  : addr;   (* address of adversary *)
   (* data: *)
   fw_obs_pt1  : port;   (* port requesting forwarding *)
   fw_obs_pt2  : port;   (* port being forwarded to *)
   fw_obs_u    : univ}.  (* universe value to be forwarded *)

op enc_fw_obs (x : fw_obs) : msg =
  (Adv, (x.`fw_obs_adv, adv_pi), (x.`fw_obs_func, 2),
   0,  (* no messages from which this must be distinct *)
   (epdp_triple_univ epdp_port_univ epdp_port_univ epdp_id).`enc
    (x.`fw_obs_pt1, x.`fw_obs_pt2, x.`fw_obs_u)).

op nosmt dec_fw_obs (m : msg) : fw_obs option =
  let (mod, pt1, pt2, tag, v) = m
  in (mod = Dir \/ pt1.`2 <> adv_pi \/ pt2.`2 <> 2 \/ tag <> 0) ?
     None :
     match (epdp_triple_univ epdp_port_univ epdp_port_univ
            epdp_id).`dec v with
     | None   => None
     | Some t =>
         let (pt1', pt2', u) = t
         in Some
            {|fw_obs_func = pt2.`1; fw_obs_adv = pt1.`1;
              fw_obs_pt1 = pt1'; fw_obs_pt2 = pt2'; fw_obs_u = u|}
     end.

op epdp_fw_obs_msg = {|enc = enc_fw_obs; dec = dec_fw_obs|}.

lemma valid_epdp_fw_obs_msg : valid_epdp epdp_fw_obs_msg.
proof.
apply epdp_intro.
move => x.
rewrite /epdp_fw_obs_msg /= /dec_fw_obs /enc_fw_obs /=
        !(epdp, epdp_sub) /=.
by case x.
move => [mod pt1 pt2 tag u] v.
rewrite /epdp_fw_obs_msg /dec_fw_obs /enc_fw_obs /=.
case (mod = Dir \/ pt1.`2 <> adv_pi \/ pt2.`2 <> 2 \/ tag <> 0) => //.
rewrite !negb_or /= not_dir => [#] -> pt1_2 pt2_2 -> match_eq_some /=.
have val_u :
  (epdp_triple_univ epdp_port_univ epdp_port_univ epdp_id).`dec u =
  Some (v.`fw_obs_pt1, v.`fw_obs_pt2, v.`fw_obs_u).
  move : match_eq_some.
  case ((epdp_triple_univ epdp_port_univ epdp_port_univ epdp_id).`dec u) => //.
  by case.
move : match_eq_some.
rewrite val_u /= => <- /=.
split; first move : pt1_2; by case pt1.
split; first move : pt2_2; by case pt2.
by rewrite (epdp_dec_enc _ _ u) 1:!epdp_sub.
qed.

hint simplify [eqtrue] valid_epdp_fw_obs_msg.
hint rewrite epdp : valid_epdp_fw_obs_msg.

lemma eq_of_valid_fw_obs (m : msg) :
  is_valid epdp_fw_obs_msg m =>
  m =
  let x = oget (epdp_fw_obs_msg.`dec m) in
  (Adv,
   (x.`fw_obs_adv, adv_pi),
   (x.`fw_obs_func, 2),
   0,
   (epdp_triple_univ epdp_port_univ epdp_port_univ epdp_id).`enc
    (x.`fw_obs_pt1, x.`fw_obs_pt2, x.`fw_obs_u)).
proof.
rewrite /is_valid.
move => val_m.
have [] x : exists (x : fw_obs), epdp_fw_obs_msg.`dec m = Some x.
  exists (oget (dec_fw_obs m)); by rewrite -some_oget.
case x => x1 x2 x3 x4 x5.
move => /(epdp_dec_enc _ _ _ valid_epdp_fw_obs_msg) <-.
by rewrite !epdp.
qed.

(* message from adversary telling forwarding functionality it may
   proceed with forwarding *)

type fw_ok =
  {fw_ok_func : addr;   (* address of functionality *)
   fw_ok_adv  : addr    (* address of adversary *)
   (* data: (none) *)
  }.

op enc_fw_ok (x : fw_ok) : msg =
  (Adv, (x.`fw_ok_func, 2), (x.`fw_ok_adv, adv_pi),
   0,  (* no messages from which this must be distinct *)
   epdp_unit_univ.`enc ()).

op nosmt dec_fw_ok (m : msg) : fw_ok option =
  let (mod, pt1, pt2, tag, v) = m
  in (mod = Dir \/ pt1.`2 <> 2 \/ pt2.`2 <> adv_pi \/ tag <> 0) ?
     None :
     match epdp_unit_univ.`dec v with
     | None   => None
     | Some _ => Some {|fw_ok_func = pt1.`1; fw_ok_adv = pt2.`1|}
     end.

op epdp_fw_ok_msg = {|enc = enc_fw_ok; dec = dec_fw_ok|}.

lemma valid_epdp_fw_ok_msg : valid_epdp epdp_fw_ok_msg.
proof.
apply epdp_intro.
move => x.
rewrite /epdp_fw_ok_msg /= /dec_fw_ok /enc_fw_ok /=
        !(epdp, epdp_sub) /=.
by case x.
move => [mod pt1 pt2 tag u] v.
rewrite /epdp_fw_ok_msg /dec_fw_ok /enc_fw_ok /=.
case (mod = Dir \/ pt1.`2 <> 2 \/ pt2.`2 <> adv_pi \/ tag <> 0) => //.
rewrite !negb_or /= not_dir => [#] -> pt1_2 pt2_2 -> match_eq_some /=.
have val_u : epdp_unit_univ.`dec u = Some ().
  move : match_eq_some.
  case (epdp_unit_univ.`dec u) => //.
move : match_eq_some.
rewrite val_u /= => <- /=.
split; first move : pt1_2; by case pt1.
split; first move : pt2_2; by case pt2.
by rewrite (epdp_dec_enc _ _ u).
qed.

hint simplify [eqtrue] valid_epdp_fw_ok_msg.
hint rewrite epdp : valid_epdp_fw_ok_msg.

lemma eq_of_valid_fw_ok (m : msg) :
  is_valid epdp_fw_ok_msg m =>
  m =
  let x = oget (epdp_fw_ok_msg.`dec m) in
  (Adv,
   (x.`fw_ok_func, 2),
   (x.`fw_ok_adv, adv_pi),
   0,
   epdp_unit_univ.`enc ()).
proof.
rewrite /is_valid.
move => val_m.
have [] x : exists (x : fw_ok), epdp_fw_ok_msg.`dec m = Some x.
  exists (oget (dec_fw_ok m)); by rewrite -some_oget.
case x => x1 x2.
move => /(epdp_dec_enc _ _ _ valid_epdp_fw_ok_msg) <-.
by rewrite !epdp.
qed.

end FwAdv.

type fw_state = [
  | FwStateInit
  | FwStateWait of port & port & univ
  | FwStateFinal
].

module Forw : FUNC = {
  var self, adv : addr
  var st : fw_state

  proc init(self_ adv_ : addr) : unit = {
    self <- self_; adv <- adv_; st <- FwStateInit;
  }

  proc parties(m : msg) : msg option = {
    var r : msg option <- None;
    match st with
      FwStateInit => {
        match FwDir.D.epdp_fw_req_msg.`dec m with
          Some x => {
            (* x.`FwDir.D.fw_req_func = self /\
               envport self adv x.`FwDir.D.fw_req_pt1 *)
            if (envport self adv x.`FwDir.D.fw_req_pt2) {
              r <-
                Some
                (FwAdv.epdp_fw_obs_msg.`enc
                 {|FwAdv.fw_obs_func = self; FwAdv.fw_obs_adv = adv;
                   FwAdv.fw_obs_pt1 = x.`FwDir.D.fw_req_pt1;
                   FwAdv.fw_obs_pt2 = x.`FwDir.D.fw_req_pt2;
                   FwAdv.fw_obs_u = x.`FwDir.D.fw_req_u|});
              st <-
                FwStateWait x.`FwDir.D.fw_req_pt1 x.`FwDir.D.fw_req_pt2
                x.`FwDir.D.fw_req_u;
            }
          }
        | None => { }
        end;
      }
    | FwStateWait pt1 pt2 u => {
        match FwAdv.epdp_fw_ok_msg.`dec m with
          Some x => {
            (* x.`FwAdv.fw_ok_func = self /\ x.`FwAdv.fw_ok_adv = adv *)
            r <-
              Some
              (FwDir.D.epdp_fw_rsp_msg.`enc
               {|FwDir.D.fw_rsp_func = self; FwDir.D.fw_rsp_pt1 = pt1;
                 FwDir.D.fw_rsp_pt2 = pt2; FwDir.D.fw_rsp_u = u|});
            st <- FwStateFinal;
          }
        | None => { }
        end;
      }
    | FwStateFinal => { }
    end;
    return r;
  }

  proc invoke(m : msg) : msg option = {
    var r : msg option <- None;
    if ((m.`1 = Dir /\ m.`2.`1 = self /\ m.`2.`2 = 1 /\
         envport self adv m.`3) \/
        (m.`1 = Adv /\ m.`2.`1 = self /\ m.`2.`2 = 2 /\
         m.`3.`1 = adv)) {
      r <@ parties(m);
    }
    return r;
  }
}.

(* termination metric and proof *)

op term_metric_max : int = 2.

(* FIXME when better glob type

   print glob Forw:
   1: Forw.st : fw_state
   2: Forw.adv : addr
   3: Forw.self : addr *)

op term_metric (g : glob Forw) : int =
     match g.`1 with
       FwStateInit       => 2
     | FwStateWait _ _ _ => 1
     | FwStateFinal      => 0
     end.

lemma ge0_term_metric (g : glob Forw) : 0 <= term_metric g.
proof.
rewrite /term_metric.
smt().
qed.

lemma init :
  equiv
  [Forw.init ~ Forw.init :
   ={self_, adv_} ==> ={res, glob Forw}].
proof.
proc; auto.
qed.

lemma term_init :
  equiv
  [Forw.init ~ Forw.init :
   ={self_, adv_} ==>
   ={res, glob Forw} /\
   term_metric (glob Forw){1} = term_metric_max].
proof.
proc; auto.
qed.

lemma term_invoke (n : int) :
  equiv
  [Forw.invoke ~ Forw.invoke :
   ={m, glob Forw} /\
   term_metric (glob Forw){1} = n ==>
   ={res, glob Forw} /\
   (res{1} = None \/ term_metric (glob Forw){1} < n)].
proof.
proc; sp 1 1.
if => //.
inline Forw.parties.
sp 2 2.
match => //.
match => //.
auto.
move => x x'.
if; first move => /> &2 -> /= -> />.
auto; first move => /> &2 -> /= -> />.
auto.
move => pt1 pt2 u pt1' pt2' u'.
match => //.
auto.
move => x x'.
auto.
auto.
qed.

(* phoare lemmas for invoke *)

pred forw_invoke_init_fw_req (self adv : addr, m : msg) =
  is_valid FwDir.D.epdp_fw_req_msg m /\
  (oget (FwDir.D.epdp_fw_req_msg.`dec m)).`FwDir.D.fw_req_func = self /\
  envport self adv (oget (FwDir.D.dec_fw_req m)).`FwDir.D.fw_req_pt1 /\
  envport self adv (oget (FwDir.D.dec_fw_req m)).`FwDir.D.fw_req_pt2.

lemma Forw_invoke_init_fw_req (m' : msg) :
  phoare
  [Forw.invoke :
   m' = m /\ Forw.st = FwStateInit /\
   forw_invoke_init_fw_req Forw.self Forw.adv m ==>
   let fwr = oget (FwDir.D.dec_fw_req m') in
   res =
   Some
   (FwAdv.enc_fw_obs
    {|FwAdv.fw_obs_func = fwr.`FwDir.D.fw_req_func;
      FwAdv.fw_obs_adv  = Forw.adv;
      FwAdv.fw_obs_pt1  = fwr.`FwDir.D.fw_req_pt1;
      FwAdv.fw_obs_pt2  = fwr.`FwDir.D.fw_req_pt2;
      FwAdv.fw_obs_u    = fwr.`FwDir.D.fw_req_u|}) /\
   Forw.st =
     FwStateWait fwr.`FwDir.D.fw_req_pt1 fwr.`FwDir.D.fw_req_pt2
     fwr.`FwDir.D.fw_req_u] = 1%r.
proof.
proc.
sp 1.
rcondt 1; first auto; smt(FwDir.D.eq_of_valid_fw_req).
inline Forw.parties.
sp 2.
match FwStateInit 1; first auto; smt().
match Some 1.
auto; smt(some_oget).
rcondt 1; first auto; progress; smt().
auto.
auto; smt(oget_some).
qed.

lemma Forw_invoke_init_bad :
  phoare
  [Forw.invoke :
   Forw.st = FwStateInit /\
   ! forw_invoke_init_fw_req Forw.self Forw.adv m ==>
   res = None /\ Forw.st = FwStateInit] = 1%r.
proof.
proc.
sp 1.
if.
inline Forw.parties.
sp 2.
match FwStateInit 1; first auto; smt().
case (FwDir.D.epdp_fw_req_msg.`dec m0 = None).
match None 1; first auto.
auto.
match Some 1; first auto; smt().
rcondf 1; first auto; smt(FwDir.D.eq_of_valid_fw_req).
auto.
auto.
qed.

pred forw_invoke_wait_fw_ok (self adv : addr, m : msg) =
  is_valid FwAdv.epdp_fw_ok_msg m /\
  (oget (FwAdv.epdp_fw_ok_msg.`dec m)).`FwAdv.fw_ok_func = self /\
  (oget (FwAdv.epdp_fw_ok_msg.`dec m)).`FwAdv.fw_ok_adv = adv.

lemma Forw_invoke_wait_fw_ok (st' : fw_state, m' : msg) :
  phoare
  [Forw.invoke :
   st' = Forw.st /\ m' = m /\ get_as_FwStateWait Forw.st <> None /\
   forw_invoke_wait_fw_ok Forw.self Forw.adv m ==>
   let wait = oget (get_as_FwStateWait st') in
   res =
   Some
   (FwDir.D.epdp_fw_rsp_msg.`enc
    {|FwDir.D.fw_rsp_func = Forw.self; FwDir.D.fw_rsp_pt1 = wait.`1;
      FwDir.D.fw_rsp_pt2 = wait.`2; FwDir.D.fw_rsp_u = wait.`3|}) /\
   Forw.st = FwStateFinal] = 1%r.
proof.
proc.
sp 1.
rcondt 1; first auto; smt(FwAdv.eq_of_valid_fw_ok).
inline Forw.parties.
sp 2.
match FwStateWait 1.
auto => /> &hr.
rewrite /get_as_FwStateWait.
case (Forw.st{hr}) => // pt1 pt2 u /= _.
by exists pt1 pt2 u.
match Some 1; first auto; smt().
auto; by rewrite /get_as_FwStateWait.
qed.

lemma Forw_invoke_wait_bad (st' : fw_state) :
  phoare
  [Forw.invoke :
   st' = Forw.st /\ get_as_FwStateWait Forw.st <> None /\
   ! forw_invoke_wait_fw_ok Forw.self Forw.adv m ==>
   res = None /\ Forw.st = st'] = 1%r.
proof.
proc.
sp 1.
if.
inline Forw.parties.
sp 2.
match FwStateWait 1.
auto => /> &hr.
rewrite /get_as_FwStateWait.
case (Forw.st{hr}) => // pt1 pt2 u /= _ _.
by exists pt1 pt2 u.
case (FwAdv.epdp_fw_ok_msg.`dec m0 = None).
match None 1; first auto.
auto.
match Some 1.
auto; smt().
exfalso; smt(FwAdv.eq_of_valid_fw_ok).
auto.
qed.

lemma Forw_invoke_final :
  phoare
  [Forw.invoke :
   Forw.st = FwStateFinal ==>
   res = None /\ Forw.st = FwStateFinal] = 1%r.
proof.
proc.
sp 1.
if.
inline Forw.parties.
sp 2.
match FwStateFinal 1; first auto; smt().
auto.
auto.
qed.
