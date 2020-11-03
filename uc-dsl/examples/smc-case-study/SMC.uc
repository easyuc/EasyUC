(* Secure Message Communication *)

uc_requires Forwarding KeyExchange.

ec_requires KeysExponentsAndPlainTexts.

direct SMCPt1 {
  in pt1@smc_req(pt2 : port, t : text)
}

direct SMCPt2 {
  out smc_rsp(pt1 : port, t : text)@pt2
}

direct SMCDir {
  Pt1 : SMCPt1
  Pt2 : SMCPt2
}

functionality SMCReal(KE : KEDir) implements SMCDir {
  subfun Fwd = Forw

  party Pt1 serves SMCDir.Pt1 {
    initial state WaitReq {
      match message with 
      | pt1@SMCDir.Pt1.smc_req(pt2, t) => {
          if (envport pt1 /\ envport pt2) {
            send KE.Pt1.ke_req1(Pt2) and transition WaitKE2(pt1, pt2, t).
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
               (Pt2,
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
      | KE.Pt2.ke_rsp1 (_, k) => {
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

adversarial SMC2Sim {
  out sim_req(pt1 : port, pt2 : port)
  in  sim_rsp
}

functionality SMCIdeal implements SMCDir SMC2Sim {
  initial state WaitReq {
    match message with 
    | pt1@SMCDir.Pt1.smc_req(pt2, t) => {
        if (envport pt1 /\ envport pt2) {
          send SMC2Sim.sim_req(pt1, pt2) and transition WaitSim(pt1, pt2, t).
        }
        else { fail. }
      }
    | *                              => { fail. }
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

simulator SMCSim uses SMC2Sim simulates SMCReal(KEIdeal) {
  initial state WaitReq {
    match message with 
    | SMC2Sim.sim_req(pt1, pt2) => {
        (* simulator learns address of ideal functionality *)
        send SMCReal.KE.KEI2S.ke_sim_req1(SMCReal.Pt1, SMCReal.Pt2)
        and transition WaitAdv1(pt1, pt2).
      }
    end
  }

  state WaitAdv1(pt1 : port, pt2 : port) {
    var q : exp;
    match message with 
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
             (SMCReal.Pt1, SMCReal.Pt2,
              epdp_port_port_key_univ.`enc (pt1, pt2, g ^ q))
        and transition WaitAdv3(pt1, pt2, q).
      }
    | *                           => { fail. }
    end
  }

  state WaitAdv3(pt1 : port, pt2 : port, q : exp) {
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
