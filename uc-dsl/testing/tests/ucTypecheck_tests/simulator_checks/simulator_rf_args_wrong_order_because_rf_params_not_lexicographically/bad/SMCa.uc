(* Secure Message Communication *)

(* Triple unit consisting of real and ideal functionalities, and a
   simulator, for Secure Message Communication via encryption using a
   one-time pad agreed using a key exchange parameter to the real
   functionality. *)

uc_requires Forwarding KeyExchange.

ec_requires +KeysExponentsAndPlaintexts.

uc_clone Forwarding.
uc_clone KeyExchange.

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
   the direct composite interface KeyExchange.KEDir, which could be
   KeyExchange.KEReal or KeyExchange.KEIdeal. Note that KEDir must be
   qualified by KeyExchange.

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

(* basic adversarial interface between ideal functionality and
   simulator *)

adversarial SMC2Sima {
  out sim_req(pt1 : port, pt2 : port)  (* initiate the simulation,
    telling the simulator the ports involved *)

  in  sim_rsp  (* give control back to the ideal functionality *)
}

functionality SMCIdeal implements SMCDir SMC2Sima {
  initial state WaitReq {
    match message with 
    | pt1@SMCDir.Pt1.smc_req(pt2, t) => {
        if (envport pt2) {
          send SMC2Sima.sim_req(pt1, pt2) and transition WaitSim(pt1, pt2, t).
        }
        else { fail. }
      }
    end
  }

  state WaitSim(pt1 : port, pt2 : port, t : text) {
    match message with 
    | SMC2Sima.sim_rsp => {
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
   KeyExchange.KEDir, when saying what SMCSim "simulates", we must
   indicate the ideal functionality that implements that composite
   direct interface. *)

simulator SMCSim uses SMC2Sima simulates SMCReal(KeyExchange.KEIdeal) {
  initial state WaitReq {
    match message with 
    | SMC2Sima.sim_req(pt1, pt2) => {
        (* simulator learns address of ideal functionality *)
        (* here we are pretending to be the instance of
           KeyExchange.KEIdeal corresponding to parameter KE, sending
           its message to the simulator (which here will go the the
           adversary), initiating simulation of key exchange between
           the internal ports of the two parties of SMCReal *)
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
       KeyExchange.KEIdeal corresponding to parameter KE of
       SMCReal *)
    | SMCReal.KE.KEI2S.ke_sim_rsp => {
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
        send SMCReal.Fwd.FwAdv.fw_obs
             (intport SMCReal.Pt1, intport SMCReal.Pt2,
              epdp_port_port_key_univ.`enc (pt1, pt2, g ^ q))
        and transition WaitAdv3(pt1, pt2, q).
      }
    | *                           => { fail. }
    end
  }

  state WaitAdv3(pt1 : port, pt2 : port, q : exp) {
    match message with 
    | SMCReal.Fwd.FwAdv.fw_ok => {
        send SMC2Sima.sim_rsp and transition Final.
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
