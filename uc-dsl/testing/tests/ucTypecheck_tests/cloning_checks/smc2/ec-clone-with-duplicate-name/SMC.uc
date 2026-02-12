(* Secure Message Communication *)

(* Triple unit consisting of real and ideal functionalities, and a
   simulator, for Secure Message Communication via encryption using a
   one-time pad agreed using a key exchange parameter to the real
   functionality. *)

uc_requires (*Forwarding*) KeyExchange.

ec_requires KeyExpText.

(**************************** Begin Unit Parameters ***************************)

(* group of keys *)

type key.

op (^^) : key -> key -> key.  (* binary operation *)

op kid : key.  (* identity *)

op kinv : key -> key.  (* inverse *)

axiom kmulA (x y z : key) : x ^^ y ^^ z = x ^^ (y ^^ z).

axiom kid_l (x : key) : kid ^^ x = x.

axiom kid_r (x : key) : x ^^ kid = x.

axiom kinv_l (x : key) : kinv x ^^ x = kid.

axiom kinv_r (x : key) : x ^^ kinv x = kid.

(* commutative semigroup of exponents *)

type exp.

op e : exp.  (* some exponent *)

op ( * ) : exp -> exp -> exp.  (* multiplication *)

axiom mulC (q r : exp) : q * r = r * q.

axiom mulA (q r s : exp) : q * r * s = q * (r * s).

op epdp_exp_univ : (exp, univ) epdp.  (* EPDP from exp to univ *)

axiom valid_epdp_exp_univ : valid_epdp epdp_exp_univ.

(* full (every element has non-zero weight), uniform (all elements
   with non-zero weight have same weight) and lossless (sum of all
   weights is 1%r) distribution over exp

   consequently exp has only finitely many elements *)

op [full uniform lossless] dexp : exp distr.

(* connection between key and exp, via generator key and
   exponentiation operation *)

op g : key.  (* generator *)

op (^) : key -> exp -> key.  (* exponentiation *)

axiom double_exp_gen (q1 q2 : exp) : (g ^ q1) ^ q2 = g ^ (q1 * q2).

(* the following axioms say that each key is uniquely generated from g
   by exponentiation *)

axiom gen_surj (x : key) : exists (q : exp), x = g ^ q.

axiom gen_inj (q r : exp) : g ^ q = g ^ r => q = r.

(* plain texts, with an EPDP to key *)

type text.

op epdp_text_key : (text, key) epdp.  (* EPDP from text to key *)

axiom valid_epdp_text_key : valid_epdp epdp_text_key.

(***************************** End Unit Parameters ****************************)

uc_clone Forwarding.

ec_clone import KeyExpText with
  type key         <- key,
  op (^^)          <- (^^),
  op kid           <- kid,
  op kinv          <- kinv,
  type exp         <- exp,
  op e             <- e,
  op ( * )         <- ( * ),
  op epdp_exp_univ <- epdp_exp_univ,
  op dexp          <- dexp,
  op g             <- g,
  op (^)           <- (^),
  type text        <- text,
  op epdp_text_key <- epdp_text_key.

ec_clone KeyExpText.

(* UC cloning must be done with "=" (not "<-" or "<=") *)

uc_clone KeyExchange with
  type key         = key,
  op (^^)          = (^^),
  op kid           = kid,
  op kinv          = kinv,
  type exp         = exp,
  op e             = e,
  op ( * )         = ( * ),
  op epdp_exp_univ = epdp_exp_univ,
  op dexp          = dexp,
  op g             = g,
  op (^)           = (^).

(* The composite direct interface has two components, corresponding
   to the two parties of the real functionality. *)

direct SMCPt1 {  (* Party 1 *)
  in pt1@smc_req(pt2 : port, t : text)  (* pt1 requests that text t
    be securely transmitted to pt2 *)
}

direct SMCPt2 {  (* Party 2 *)
  out smc_rsp(pt1 : port, t : text)@pt2  (* message sending t to pt2,
    along with the information that it was pt1 who initiated the
    communication *)
}

direct SMCDir {
  Pt1 : SMCPt1  (* Party 1 *)
  Pt2 : SMCPt2  (* Party 2 *)
}

(* The real functionality implements the composite direct interface
   SMCDir, and (in this case) no composite adversarial interface. It
   is parameterized by a key exchange functionality, KE, implementing
   the direct composite interface KeyEx.KEDir, which could be
   KeyEx.KEReal or KeyEx.KEIdeal. Note that KEDir must be qualified by
   KeyEx.

   The parties of SMCReal can send messages to, and receive messages
   from KE, just as they can with the forwarding subfunctionality
   Fwd. *)

functionality SMCReal(KE : KeyExchange.KEDir) implements SMCDir {
  subfun Fwd = Forwarding.Forw

  party Pt1 serves SMCDir.Pt1 {
    initial state WaitReq {
      match message with 
      | pt1@SMCDir.Pt1.smc_req(pt2, t) => {
          if (envport pt2) {
            send KE.Pt1.ke_req1(intport Pt2)
            and transition WaitKE2(pt1, pt2, t).
          }
          else { fail. }
        }
      | *                              => { fail. }
      end
    }

    state WaitKE2(pt1 : port, pt2 : port, t : text) {
      match message with 
      | KE.Pt1.ke_rsp2(k) => {
          send Fwd.D.fw_req
               (intport Pt2,
                epdp_port_port_key_univ.`enc
                (pt1, pt2, epdp_text_key.`enc t ^^ k))
          and transition Final.
        }
      | *                 => { fail. }
      end
    }

    state Final {
      match message with 
      | * => { fail. }
      end
    }
  }

  party Pt2 serves SMCDir.Pt2 {
    initial state WaitKE1 {
      match message with 
      | KE.Pt2.ke_rsp1(_, k) => {
          send KE.Pt2.ke_req2 and transition WaitFwd(k).
        }
      | *                     => { fail. }
      end
    }

    state WaitFwd(k : key) {
      var pt1, pt2 : port; var x : key;
      match message with 
      | Fwd.D.fw_rsp(_, u) => {
          match epdp_port_port_key_univ.`dec u with
          | Some tr => {
              (pt1, pt2, x) <- tr;
              match epdp_text_key.`dec (x ^^ kinv k) with
              | Some t => {
                  send SMCDir.Pt2.smc_rsp(pt1, t)@pt2
                  and transition Final.
                }
              | None   => { fail. }  (* cannot happen *)
              end
            }
          | None    => { fail. }  (* cannot happen *)
          end
        }
      | *                  => { fail. }
      end
    }

    state Final {
      match message with 
      | * => { fail. }
      end
    }
  }
}

(* The ideal functionality and simulator are set up to facilitate
   handling the one-time pad encryption using the Diffie-Hellman
   key using EasyCrypt's rnd tactic with an appropriate isomorphism *)

(* basic adversarial interface between ideal functionality and
   simulator *)

adversarial SMC2Sim {
  out sim_req(pt1 : port, pt2 : port)  (* initiate the simulation,
    telling the simulator the ports involved *)

  in  sim_rsp  (* give control back to the ideal functionality *)
}

functionality SMCIdeal implements SMCDir SMC2Sim {
  initial state WaitReq {
    match message with 
    | pt1@SMCDir.Pt1.smc_req(pt2, t) => {
        if (envport pt2) {
          send SMC2Sim.sim_req(pt1, pt2) and transition WaitSim(pt1, pt2, t).
        }
        else { fail. }
      }
    end
  }

  state WaitSim(pt1 : port, pt2 : port, t : text) {
    match message with 
    | SMC2Sim.sim_rsp => {
        send SMCDir.Pt2.smc_rsp(pt1, t)@pt2 and transition Final.
      }
    | *               => { fail. }
    end
  }

  state Final {
    match message with 
    | * => { fail. }
    end
  }
}

(* Because the real functionality SMCReal is parameterized by a key
   exchange functionality implementing the composite direct interface
   KeyEx.KEDir, when saying what SMCSim "simulates", we must indicate
   the ideal functionality that implements that composite direct
   interface. *)

simulator SMCSim uses SMC2Sim simulates SMCReal(KeyExchange.KEIdeal) {
  initial state WaitReq {
    match message with 
    | SMC2Sim.sim_req(pt1, pt2) => {
        (* simulator learns address of ideal functionality *)
        (* here we are pretending to be the instance of KeyEx.KEIdeal
           corresponding to parameter KE, sending its message to the
           simulator (which here will go the the adversary),
           initiating simulation of key exchange between the internal
           ports of the two parties of SMCReal *)
        send SMCReal.KE.KEI2S.ke_sim_req1
             (intport SMCReal.Pt1, intport SMCReal.Pt2)
        and transition WaitAdv1(pt1, pt2).
      }
    (* no messages from the adversary to the real functionality can be
       matched in the initial state; they automatically flow through
       the simulator to the ideal functionality, where they result in
       failure *)
    end
  }

  state WaitAdv1(pt1 : port, pt2 : port) {
    var q : exp;
    match message with 
    (* here we receive a message intended for the instance of
       KeyEx.KEIdeal corresponding to parameter KE of SMCReal *)
    | SMCReal.KE.KEI2S.ke_sim_rsp => {
        (* q must be sampled "early", so it can be matched with
           the sampling of q in KeyEx.KEIdeal

           pad_iso_l and pad_iso_r of KeysExpsText.ec are used with
           the rnd tactic to handle the one-time pad argument *)
        q <$ dexp;
        send SMCReal.KE.KEI2S.ke_sim_req2
        and transition WaitAdv2(pt1, pt2, q).
      }
    (* messages with addresses not >= address of ideal functionality
       are implicitly passed to environment *)
    | *                           => { fail. }
    end
  }

  state WaitAdv2(pt1 : port, pt2 : port, q : exp) {
    match message with 
    | SMCReal.KE.KEI2S.ke_sim_rsp => {
      (* in SMCReal(KeyEx.KEIdeal), the group element being forwarded
         is epdp_text_key.`enc t ^^ k, where t is the text being
         securely communicated, and k is the key agreed by
         Diffie-Hellman key exchange *)
        send SMCReal.Fwd.FwAdv.fw_obs
             (intport SMCReal.Pt1, intport SMCReal.Pt2,
              epdp_port_port_key_univ.`enc (pt1, pt2, g ^ q))
        and transition WaitAdv3.
      }
    | *                           => { fail. }
    end
  }

  state WaitAdv3 {
    match message with 
    | SMCReal.Fwd.FwAdv.fw_ok => {
        send SMC2Sim.sim_rsp and transition Final.
      }
    | *                       => { fail. }
    end
  }

  state Final {
    match message with
    | * => { fail. }
    end
  }
}
