(* Forward.ec *)

(* Forwarding Functionality *)

(* This functionality implements authenticated forwarding (Fauth),
   where the adversary is asked to approve the forwarding of a value,
   but may not corrupt either the value or its destination/source *)

prover quorum=2 ["Alt-Ergo" "Z3"].

require import AllCore List ListPO Encoding UCCore.

(* begin theory parameters *)

(* port index of adversary that functionality communicates with *)

op adv_pi : int.

axiom fwd_pi_uniq : uniq [adv_pi; 0].

(* end theory parameters *)

(* request sent to port index 1 of forwarding functionality: pt1 is
   asking to forward u to pt2 *)

type fw_req =
  {fw_req_func : addr;   (* address of functionality *)
   fw_req_pt1  : port;   (* source = port requesting forwarding *)
   (* data: *)
   fw_req_pt2  : port;   (* port being forwarded to *)
   fw_req_u    : univ}.  (* universe value to be forwarded *)

op fw_req (x : fw_req) : msg =
     (Dir, (x.`fw_req_func, 1), x.`fw_req_pt1,
      EPDP_Univ_PortUniv.enc (x.`fw_req_pt2, x.`fw_req_u)).

op nosmt dec_fw_req (m : msg) : fw_req option =
     let (mod, pt1, pt2, v) = m
     in (mod = Adv \/ pt1.`2 <> 1 \/ ! EPDP_Univ_PortUniv.valid v) ?
        None :
        let (pt2', u) = oget (EPDP_Univ_PortUniv.dec v)
        in Some {|fw_req_func = pt1.`1; fw_req_pt1 = pt2;
                  fw_req_pt2 = pt2'; fw_req_u = u|}.

lemma epdp_fw_req : epdp fw_req dec_fw_req.
proof.
apply epdp_intro.
move => m.
rewrite /fw_req /dec_fw_req /= EPDP_Univ_PortUniv.valid_enc /=.
by case m.
move => [mod pt1 pt2 u] v.
rewrite /fw_req /dec_fw_req /=.
case (mod = Adv \/ pt1.`2 <> 1 \/ ! (EPDP_Univ_PortUniv.valid u)) => //.
rewrite !negb_or /= not_adv => [#] -> pt1_2 val_u.
have [] p : exists (p : port * univ), EPDP_Univ_PortUniv.dec u = Some p.
  exists (oget (EPDP_Univ_PortUniv.dec u)); by rewrite -some_oget.
move => /EPDP_Univ_PortUniv.dec_enc <-.
rewrite EPDP_Univ_PortUniv.enc_dec oget_some /#.
qed.

lemma fw_req_enc_dec (x : fw_req) :
  dec_fw_req (fw_req x) = Some x.
proof.
apply (epdp_enc_dec _ _ _ epdp_fw_req).
qed.

hint simplify fw_req_enc_dec.

op dec_fw_req_check (m : msg, func : addr) : fw_req option =
  match dec_fw_req m with
    None   => None
  | Some x => (x.`fw_req_func = func) ? Some x : None
  end.

lemma mode_valid_fw_req (m : msg) :
  dec2valid dec_fw_req m => m.`1 = Dir.
proof.
move => val_m.
have [] x : exists (x : fw_req), dec_fw_req m = Some x.
  exists (oget (dec_fw_req m)); by rewrite -some_oget.
case x => x1 x2 x3 x4.
move => /(epdp_dec_enc _ _ _ _ epdp_fw_req) <- //.
qed.

lemma dest_valid_fw_req (m : msg) :
  dec2valid dec_fw_req m =>
  m.`2.`1 = (oget (dec_fw_req m)).`fw_req_func /\ m.`2.`2 = 1.
proof.
move => val_m.
have [] x : exists (x : fw_req), dec_fw_req m = Some x.
  exists (oget (dec_fw_req m)); by rewrite -some_oget.
case x => x1 x2 x3 x4.
move => /(epdp_dec_enc _ _ _ _ epdp_fw_req) <-.
by rewrite (epdp_enc_dec _ _ _ epdp_fw_req).
qed.

lemma source_valid_fw_req (m : msg) :
  dec2valid dec_fw_req m =>
  m.`3 = (oget (dec_fw_req m)).`fw_req_pt1.
proof.
move => val_m.
have [] x : exists (x : fw_req), dec_fw_req m = Some x.
  exists (oget (dec_fw_req m)); by rewrite -some_oget.
case x => x1 x2 x3 x4.
move => /(epdp_dec_enc _ _ _ _ epdp_fw_req) <-.
by rewrite (epdp_enc_dec _ _ _ epdp_fw_req).
qed.

(* response sent from port index 1 of forwarding functionality to pt2,
   completing the forwarding of u that was requested by pt1 *)

type fw_rsp =
  {fw_rsp_func : addr;   (* address of functionality *)
   fw_rsp_pt2  : port;   (* destination = port being forwarded to *)
   (* data: *)
   fw_rsp_pt1  : port;   (* port requesting forwarding *)
   fw_rsp_u    : univ}.  (* universe value to be forwarded *)

op fw_rsp (x : fw_rsp) : msg =
     (Dir, x.`fw_rsp_pt2, (x.`fw_rsp_func, 1),
      EPDP_Univ_PortUniv.enc (x.`fw_rsp_pt1, x.`fw_rsp_u)).

op nosmt dec_fw_rsp (m : msg) : fw_rsp option =
     let (mod, pt1, pt2, v) = m
     in (mod = Adv \/ pt2.`2 <> 1 \/ ! EPDP_Univ_PortUniv.valid v) ?
        None :
        let (pt1', u) = oget (EPDP_Univ_PortUniv.dec v)
        in Some {|fw_rsp_func = pt2.`1; fw_rsp_pt1 = pt1';
                  fw_rsp_pt2 = pt1; fw_rsp_u = u|}.

lemma epdp_fw_rsp : epdp fw_rsp dec_fw_rsp.
proof.
apply epdp_intro.
move => m.
rewrite /fw_rsp /dec_fw_rsp /= EPDP_Univ_PortUniv.valid_enc /=.
by case m.
move => [mod pt1 pt2 u] v.
rewrite /fw_rsp /dec_fw_rsp /=.
case (mod = Adv \/ pt2.`2 <> 1 \/ ! (EPDP_Univ_PortUniv.valid u)) => //.
rewrite !negb_or /= not_adv => [#] -> pt2_2 val_u.
have [] p : exists (p : port * univ), EPDP_Univ_PortUniv.dec u = Some p.
  exists (oget (EPDP_Univ_PortUniv.dec u)); by rewrite -some_oget.
move => /EPDP_Univ_PortUniv.dec_enc <-.
rewrite EPDP_Univ_PortUniv.enc_dec oget_some /#.
qed.

lemma fw_rsp_enc_dec (x : fw_rsp) :
  dec_fw_rsp (fw_rsp x) = Some x.
proof.
apply (epdp_enc_dec _ _ _ epdp_fw_rsp).
qed.

hint simplify fw_rsp_enc_dec.

op dec_fw_rsp_check (m : msg, func : addr, pt2 : port) : fw_rsp option =
  match dec_fw_rsp m with
    None   => None
  | Some x => (x.`fw_rsp_func = func /\ x.`fw_rsp_pt2 = pt2) ? Some x : None
  end.

lemma mode_valid_fw_rsp (m : msg) :
  dec2valid dec_fw_rsp m => m.`1 = Dir.
proof.
move => val_m.
have [] x : exists (x : fw_rsp), dec_fw_rsp m = Some x.
  exists (oget (dec_fw_rsp m)); by rewrite -some_oget.
case x => x1 x2 x3 x4.
move => /(epdp_dec_enc _ _ _ _ epdp_fw_rsp) <- //.
qed.

lemma dest_valid_fw_rsp (m : msg) :
  dec2valid dec_fw_rsp m =>
  m.`2 = (oget (dec_fw_rsp m)).`fw_rsp_pt2.
proof.
move => val_m.
have [] x : exists (x : fw_rsp), dec_fw_rsp m = Some x.
  exists (oget (dec_fw_rsp m)); by rewrite -some_oget.
case x => x1 x2 x3 x4.
move => /(epdp_dec_enc _ _ _ _ epdp_fw_rsp) <-.
by rewrite (epdp_enc_dec _ _ _ epdp_fw_rsp).
qed.

lemma source_valid_fw_rsp (m : msg) :
  dec2valid dec_fw_rsp m =>
  m.`3.`1 = (oget (dec_fw_rsp m)).`fw_rsp_func /\ m.`3.`2 = 1.
proof.
move => val_m.
have [] x : exists (x : fw_rsp), dec_fw_rsp m = Some x.
  exists (oget (dec_fw_rsp m)); by rewrite -some_oget.
case x => x1 x2 x3 x4.
move => /(epdp_dec_enc _ _ _ _ epdp_fw_rsp) <-.
by rewrite (epdp_enc_dec _ _ _ epdp_fw_rsp).
qed.

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

op nosmt fw_obs (x : fw_obs) : msg =
     (Adv, (x.`fw_obs_adv, adv_pi), (x.`fw_obs_func, 1),
      EPDP_Univ_PortPortUniv.enc (x.`fw_obs_pt1, x.`fw_obs_pt2, x.`fw_obs_u)).

op nosmt dec_fw_obs (m : msg) : fw_obs option =
     let (mod, pt1, pt2, v) = m
     in (mod = Dir \/ pt1.`2 <> adv_pi \/ pt2.`2 <> 1 \/
         ! EPDP_Univ_PortPortUniv.valid v) ?
        None :
        let (pt1', pt2', u) = oget (EPDP_Univ_PortPortUniv.dec v)
        in Some {|fw_obs_func = pt2.`1; fw_obs_adv = pt1.`1;
                  fw_obs_pt1 = pt1'; fw_obs_pt2 = pt2'; fw_obs_u = u|}.

lemma epdp_fw_obs : epdp fw_obs dec_fw_obs.
proof.
apply epdp_intro.
move => m.
rewrite /fw_obs /dec_fw_obs /= EPDP_Univ_PortPortUniv.valid_enc /=.
by case m.
move => [mod pt1 pt2 u] v.
rewrite /fw_obs /dec_fw_obs /=.
case (mod = Dir \/ pt1.`2 <> adv_pi \/ pt2.`2 <> 1 \/
      ! (EPDP_Univ_PortPortUniv.valid u)) => //.
rewrite !negb_or /= not_dir => [#] -> pt1_2 pt2_2 val_u.
have [] t : exists (t : port * port * univ), EPDP_Univ_PortPortUniv.dec u = Some t.
  exists (oget (EPDP_Univ_PortPortUniv.dec u)); by rewrite -some_oget.
move => /EPDP_Univ_PortPortUniv.dec_enc <-.
rewrite EPDP_Univ_PortPortUniv.enc_dec oget_some /= /#.
qed.

lemma fw_obs_enc_dec (x : fw_obs) :
  dec_fw_obs (fw_obs x) = Some x.
proof.
apply (epdp_enc_dec _ _ _ epdp_fw_obs).
qed.

hint simplify fw_obs_enc_dec.

op dec_fw_obs_check (m : msg, func adv : addr) : fw_obs option =
  match dec_fw_obs m with
    None   => None
  | Some x => (x.`fw_obs_func = func /\ x.`fw_obs_adv = adv) ? Some x : None
  end.

lemma mode_valid_fw_obs (m : msg) :
  dec2valid dec_fw_obs m => m.`1 = Adv.
proof.
move => val_m.
have [] x : exists (x : fw_obs), dec_fw_obs m = Some x.
  exists (oget (dec_fw_obs m)); by rewrite -some_oget.
case x => x1 x2 x3 x4 x5.
move => /(epdp_dec_enc _ _ _ _ epdp_fw_obs) <- //.
qed.

lemma dest_valid_fw_obs (m : msg) :
  dec2valid dec_fw_obs m =>
  m.`2.`1 = (oget (dec_fw_obs m)).`fw_obs_adv /\ m.`2.`2 = adv_pi.
proof.
move => val_m.
have [] x : exists (x : fw_obs), dec_fw_obs m = Some x.
  exists (oget (dec_fw_obs m)); by rewrite -some_oget.
case x => x1 x2 x3 x4 x5.
move => /(epdp_dec_enc _ _ _ _ epdp_fw_obs) <-.
by rewrite (epdp_enc_dec _ _ _ epdp_fw_obs).
qed.

lemma source_valid_fw_obs (m : msg) :
  dec2valid dec_fw_obs m =>
  m.`3.`1 = (oget (dec_fw_obs m)).`fw_obs_func /\ m.`3.`2 = 1.
proof.
move => val_m.
have [] x : exists (x : fw_obs), dec_fw_obs m = Some x.
  exists (oget (dec_fw_obs m)); by rewrite -some_oget.
case x => x1 x2 x3 x4 x5.
move => /(epdp_dec_enc _ _ _ _ epdp_fw_obs) <-.
by rewrite (epdp_enc_dec _ _ _ epdp_fw_obs).
qed.

(* message from adversary telling forwarding functionality it may
   proceed with forwarding *)

type fw_ok =
  {fw_ok_func : addr;   (* address of functionality *)
   fw_ok_adv  : addr    (* address of adversary *)
   (* data: (none) *)
  }.

op fw_ok (x : fw_ok) : msg =
     (Adv, (x.`fw_ok_func, 1), (x.`fw_ok_adv, adv_pi),
      EPDP_Univ_Unit.enc ()).

op nosmt dec_fw_ok (m : msg) : fw_ok option =
     let (mod, pt1, pt2, v) = m
     in (mod = Dir \/ pt1.`2 <> 1 \/ pt2.`2 <> adv_pi \/
         ! EPDP_Univ_Unit.valid v) ?
        None :
        Some {|fw_ok_func = pt1.`1; fw_ok_adv = pt2.`1|}.

lemma epdp_fw_ok : epdp fw_ok dec_fw_ok.
proof.
apply epdp_intro.
move => m.
rewrite /fw_ok /dec_fw_ok /= EPDP_Univ_Unit.valid_enc /=.
by case m.
move => [mod pt1 pt2 u] v.
rewrite /fw_ok /dec_fw_ok /=.
case (mod = Dir \/ pt1.`2 <> 1 \/ pt2.`2 <> adv_pi \/
      ! (EPDP_Univ_Unit.valid u)) => //.
rewrite !negb_or /= not_dir => [#] -> pt1_2 pt2_2 val_u.
have [] s : exists (s : unit), EPDP_Univ_Unit.dec u = Some s.
  exists (oget (EPDP_Univ_Unit.dec u)); by rewrite -some_oget.
move => /EPDP_Univ_Unit.dec_enc <- <- /=.
split; first move : pt1 pt1_2; by case.
split; first move : pt2 pt2_2; by case.
congr.
qed.

lemma fw_ok_enc_dec (x : fw_ok) :
  dec_fw_ok (fw_ok x) = Some x.
proof.
apply (epdp_enc_dec _ _ _ epdp_fw_ok).
qed.

hint simplify fw_ok_enc_dec.

op dec_fw_ok_check (m : msg, func adv : addr) : fw_ok option =
  match dec_fw_ok m with
    None   => None
  | Some x => (x.`fw_ok_func = func /\ x.`fw_ok_adv = adv) ? Some x : None
  end.

lemma mode_valid_fw_ok (m : msg) :
  dec2valid dec_fw_ok m => m.`1 = Adv.
proof.
move => val_m.
have [] x : exists (x : fw_ok), dec_fw_ok m = Some x.
  exists (oget (dec_fw_ok m)); by rewrite -some_oget.
case x => x1 x2.
move => /(epdp_dec_enc _ _ _ _ epdp_fw_ok) <- //.
qed.

lemma dest_valid_fw_ok (m : msg) :
  dec2valid dec_fw_ok m =>
  m.`2.`1 = (oget (dec_fw_ok m)).`fw_ok_func /\ m.`2.`2 = 1.
proof.
move => val_m.
have [] x : exists (x : fw_ok), dec_fw_ok m = Some x.
  exists (oget (dec_fw_ok m)); by rewrite -some_oget.
move => /(epdp_dec_enc _ _ _ _ epdp_fw_ok) <-.
by rewrite (epdp_enc_dec _ _ _ epdp_fw_ok).
qed.

lemma source_valid_fw_ok (m : msg) :
  dec2valid dec_fw_ok m =>
  m.`3.`1 = (oget (dec_fw_ok m)).`fw_ok_adv /\ m.`3.`2 = adv_pi.
proof.
move => val_m.
have [] x : exists (x : fw_ok), dec_fw_ok m = Some x.
  exists (oget (dec_fw_ok m)); by rewrite -some_oget.
move => /(epdp_dec_enc _ _ _ _ epdp_fw_ok) <-.
by rewrite (epdp_enc_dec _ _ _ epdp_fw_ok).
qed.

type fw_state = [
    FwStateInit
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
        match dec_fw_req_check m self with
          Some x => {
            (* envport self adv x.`fw_req_pt1 *)
            if (envport self adv x.`fw_req_pt2) {
              r <-
                Some
                (fw_obs
                 {|fw_obs_func = self; fw_obs_adv = adv;
                   fw_obs_pt1 = x.`fw_req_pt1; fw_obs_pt2 = x.`fw_req_pt2;
                   fw_obs_u = x.`fw_req_u|});
              st <- FwStateWait x.`fw_req_pt1 x.`fw_req_pt2 x.`fw_req_u;
            }
          }
        | None => { }
        end;
      }
    | FwStateWait pt1 pt2 u => {
        match dec_fw_ok_check m self adv with
          Some x => {
            r <-
              Some
              (fw_rsp
               {|fw_rsp_func = self; fw_rsp_pt1 = pt1;
                 fw_rsp_pt2 = pt2; fw_rsp_u = u|});
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
    (* we can assume (envport self adv m.`3) *)
    if ((m.`1 = Dir /\ m.`2.`1 = self /\ m.`2.`2 = 1) \/
        (m.`1 = Adv /\ m.`2.`1 = self /\ m.`2.`2 = 1)) {
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
  dec_fw_req_check m self <> None /\
  envport self adv (oget (dec_fw_req m)).`fw_req_pt2.

lemma Forw_invoke_init_fw_req (m' : msg) :
  phoare
  [Forw.invoke :
   m' = m /\ Forw.st = FwStateInit /\
   forw_invoke_init_fw_req Forw.self Forw.adv m ==>
   let fwr = oget (dec_fw_req m') in
   res =
   Some
   (fw_obs
    {|fw_obs_func = fwr.`fw_req_func; fw_obs_adv = Forw.adv;
      fw_obs_pt1 = fwr.`fw_req_pt1; fw_obs_pt2 = fwr.`fw_req_pt2;
      fw_obs_u = fwr.`fw_req_u|}) /\
   Forw.st = FwStateWait fwr.`fw_req_pt1 fwr.`fw_req_pt2 fwr.`fw_req_u] = 1%r.
proof.
proc.
sp 1.
rcondt 1; first auto; progress; smt(mode_valid_fw_req dest_valid_fw_req).
inline Forw.parties.
sp 2.
match FwStateInit 1; first auto; smt().
match Some 1.
auto; smt(some_oget).
rcondt 1; first auto; progress; smt().
auto => &hr |> dec_fw_req_chk_m.
have dec_fw_req_m : dec_fw_req m{hr} = Some x{hr} by smt().
have -> : oget (dec_fw_req m{hr}) = x{hr}
  by rewrite dec_fw_req_m oget_some.
smt().
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
case (dec_fw_req_check m0 Forw.self = None).
match None 1; first auto; smt().
auto; smt().
match Some 1; first auto; progress; smt().
rcondf 1; first auto; progress; smt().
auto; smt().
auto.
qed.

pred forw_invoke_wait_fw_ok (self adv : addr, m : msg) =
  dec_fw_ok_check m self adv <> None.

lemma Forw_invoke_wait_fw_ok (st' : fw_state, m' : msg) :
  phoare
  [Forw.invoke :
   st' = Forw.st /\ m' = m /\ get_as_FwStateWait Forw.st <> None /\
   forw_invoke_wait_fw_ok Forw.self Forw.adv m ==>
   let wait = oget (get_as_FwStateWait st') in
   res =
   Some
   (fw_rsp
    {|fw_rsp_func = Forw.self; fw_rsp_pt1 = wait.`1; fw_rsp_pt2 = wait.`2;
      fw_rsp_u = wait.`3|}) /\
   Forw.st = FwStateFinal] = 1%r.
proof.
proc.
sp 1.
rcondt 1; first auto; smt(mode_valid_fw_ok dest_valid_fw_ok).
inline Forw.parties.
sp 2.
match FwStateWait 1.
auto => /> &hr.
rewrite /get_as_FwStateWait.
case (Forw.st{hr}) => // pt1 pt2 u /= _.
by exists pt1 pt2 u.
match Some 1.
auto => &hr />.
rewrite /forw_invoke_wait_fw_ok.
case (dec_fw_ok_check m{hr} Forw.self{hr} Forw.adv{hr}) => // fwok.
progress; by exists fwok.
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
match None 1.
auto.
auto.
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
