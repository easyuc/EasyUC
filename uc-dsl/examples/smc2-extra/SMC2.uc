uc_requires Forwarding SMC PrivateForwarding.

ec_requires +KeysExponentsAndPlaintexts.

direct SMC2Pt1 {
  in  pt1@smc_req(pt2 : port, t : text)
  out smc_rsp(t : text)@pt1
}

direct SMC2Pt2 {
  out smc_rsp(pt1 : port, t : text)@pt2
  in  pt2@smc_req(t : text)
}

direct SMC2Dir {
  Pt1 : SMC2Pt1
  Pt2 : SMC2Pt2
}

adversarial SMC2AdvPt3 {
  in pong
  out ping(u : univ)
}

adversarial SMC2Adv {
  Pt3 : SMC2AdvPt3
}

functionality SMC2Real(SMC1 : SMC.SMCDir, SMC2 : SMC.SMCDir)
    implements SMC2Dir SMC2Adv {
  subfun Fwd1 = Forwarding.Forw
  subfun Fwd2 = Forwarding.Forw
  subfun Fwd3 = PrivateForwarding.Forw
  subfun Fwd4 = PrivateForwarding.Forw

  party Pt1 serves SMC2Dir.Pt1 {
    initial state WaitReq {
      match message with 
      | pt1@SMC2Dir.Pt1.smc_req(pt2, t) => {
          if (envport pt2) {
            send Fwd3.D.fw_req
                 (intport Pt3, epdp_port_port_univ.`enc (pt1, pt2))
            and transition WaitFwd4(pt1, pt2, t).
          }
          else { fail. }
        }
      | *                               => { fail. }
      end
    }

    state WaitFwd4(pt1 : port, pt2 : port, t : text) {
      match message with 
      | Fwd4.D.fw_rsp(_, _) => {
          send Fwd1.D.fw_req
               (intport Pt2, epdp_port_port_univ.`enc (pt1, pt2))
          and transition WaitFwd2(pt1, pt2, t).
        }
      | *                               => { fail. }
      end
    }

    state WaitFwd2(pt1 : port, pt2 : port, t : text) {
      match message with
      | Fwd2.D.fw_rsp(_, _) => {
          send SMC1.Pt1.smc_req(intport Pt2, t)
          and transition WaitSMC2(pt1).
        }
      | *                   => { fail. }
      end         
    }

    state WaitSMC2(pt1 : port) {
      match message with 
      | SMC2.Pt2.smc_rsp(_, t) => {
          send SMC2Dir.Pt1.smc_rsp(t)@pt1
          and transition Final.
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

  party Pt2 serves SMC2Dir.Pt2 {
    initial state WaitFwd1 {
      var pt1, pt2 : port;
      match message with 
      | Fwd1.D.fw_rsp(_, u) => {
          (pt1, pt2) <- oget (epdp_port_port_univ.`dec u);
          send Fwd2.D.fw_req(intport Pt1, [])
          and transition WaitSMC1(pt1, pt2).
        }
      | *                   => { fail. }
      end
    }

    state WaitSMC1(pt1 : port, pt2 : port) {
      match message with
      | SMC1.Pt2.smc_rsp(_, t) => {
          send SMC2Dir.Pt2.smc_rsp(pt1, t)@pt2
          and transition WaitReq(pt2).
        }
      | *                      => { fail. }
      end
    }

    state WaitReq(pt2 : port) {
      match message with 
      | pt2'@SMC2Dir.Pt2.smc_req(t) => {
          if (pt2' = pt2) {
            send SMC2.Pt1.smc_req(intport Pt1, t)
            and transition Final.
          }
          else { fail. }
        }
      | *                           => { fail. }
      end
    }

    state Final {
      match message with 
      | * => { fail. }
      end
    }
  }

  party Pt3 serves SMC2Adv.Pt3 {
    initial state WaitFwd3 {
      var pt1, pt2 : port;
      match message with 
      | Fwd3.D.fw_rsp(_, u) => {
          send SMC2Adv.Pt3.ping(u) and transition WaitAdv.
        }
      | *                   => { fail. }
      end
    }

    state WaitAdv {
      match message with
      | SMC2Adv.Pt3.pong => {
          send Fwd4.D.fw_req(intport Pt1, []) and transition Final.
        }
      | *                => { fail. }
      end
    }

    state Final {
      match message with
      | * => { fail. }
      end
    }
  }
}

adversarial SMC2IF_to_Sim {
  out sim_req1(pt1 : port, pt2 : port)
  out sim_req2
  in  sim_rsp
}

functionality SMC2Ideal implements SMC2Dir SMC2IF_to_Sim {
  initial state WaitReq1 {
    match message with 
    | pt1@SMC2Dir.Pt1.smc_req(pt2, t) => {
        if (envport pt2) {
          send SMC2IF_to_Sim.sim_req1(pt1, pt2)
          and transition WaitSim1(pt1, pt2, t).
        }
        else { fail. }
      }
    | *                               => { fail. }
    end
  }

  state WaitSim1(pt1 : port, pt2 : port, t : text) {
    match message with
    | SMC2IF_to_Sim.sim_rsp => {
        send SMC2Dir.Pt2.smc_rsp(pt1, t)@pt2
        and transition WaitReq2(pt1, pt2).
      }
    | *                     => { fail. }
    end
  }        

  state WaitReq2(pt1 : port, pt2 : port) {
    match message with 
    | pt2'@SMC2Dir.Pt2.smc_req(t) => {
        if (pt2' = pt2) {
          send SMC2IF_to_Sim.sim_req2
          and transition WaitSim2(pt1, pt2, t).
        }
        else { fail. }
      }
    | *                           => { fail. }
    end
  }

  state WaitSim2(pt1 : port, pt2 : port, t : text) {
    match message with
    | SMC2IF_to_Sim.sim_rsp => {
        send SMC2Dir.Pt1.smc_rsp(t)@pt1
        and transition Final.
      }
    | *                     => { fail. }
    end
  }        

  state Final {
    match message with
    | * => { fail. }
    end
  }
}

simulator SMC2Sim uses SMC2IF_to_Sim
          simulates SMC2Real(SMC.SMCIdeal, SMC.SMCIdeal) {
  initial state WaitReq1 {
    var u : univ;
    match message with 
    | SMC2IF_to_Sim.sim_req1(pt1, pt2) => {
        u <- epdp_port_port_univ.`enc (pt1, pt2);
        send SMC2Real.SMC2Adv.Pt3.ping(u)
        and transition WaitAdv1(u).
      }
    | *                                => { fail. }
    end
  }

  state WaitAdv1(u : univ) {
    match message with 
    | SMC2Real.SMC2Adv.Pt3.pong => {
        send SMC2Real.Fwd1.FwAdv.fw_obs
             (intport SMC2Real.Pt1, intport SMC2Real.Pt2, u)
        and transition WaitAdv2.
      }
    | *                                => { fail. }
    end
  }

  state WaitAdv2 {
    match message with
    | SMC2Real.Fwd1.FwAdv.fw_ok => {
        send SMC2Real.Fwd2.FwAdv.fw_obs
             (intport SMC2Real.Pt2, intport SMC2Real.Pt1, [])
        and transition WaitAdv3.
      }
    | *                         => { fail. }        
    end
  }

  state WaitAdv3 {
    match message with
    | SMC2Real.Fwd2.FwAdv.fw_ok => {
        send SMC2Real.SMC1.SMC2Sim.sim_req
             (intport SMC2Real.Pt1, intport SMC2Real.Pt2)
        and transition WaitAdv4.
      }
    | *                         => { fail. }
    end
  }

  state WaitAdv4 {
    match message with
    | SMC2Real.SMC1.SMC2Sim.sim_rsp => {
        send SMC2IF_to_Sim.sim_rsp
        and transition WaitReq2.
      }
    | *                             => { fail. }
    end
  }

  state WaitReq2 {
    match message with 
    | SMC2IF_to_Sim.sim_req2 => {
        send SMC2Real.SMC2.SMC2Sim.sim_req
             (intport SMC2Real.Pt2, intport SMC2Real.Pt1)
        and transition WaitAdv5.
      }
    | *                      => { fail. }
    end
  }

  state WaitAdv5 {
    match message with
    | SMC2Real.SMC2.SMC2Sim.sim_rsp => {
        send SMC2IF_to_Sim.sim_rsp
        and transition Final.
      }
    | *                             => { fail. }
    end
  }

  state Final {
    match message with
    | * => { fail. }
    end
  }
}
