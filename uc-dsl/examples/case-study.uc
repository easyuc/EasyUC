(* SMC Case Study Expressed in UC DSL *)

(* require and import EasyCrypt theory defining exp, key, text *)

ec_requires KeysExponentsAndPlainTexts.

(* forwarding *)

direct fwDir {
  in pt1@fw_req(pt2 : port, u : univ)
  out fw_rsp(pt1 : port, u : univ)@pt2
}

direct FwDir {D : fwDir}

adversarial FwAdv {
  in fw_ok
  out fw_obs(pt1 : port, pt2 : port, u : univ)
}

functionality Forw implements FwDir FwAdv {
  initial state Init {
    match message with
    | pt1@fw_req(pt2, u) => {
        (* check that pt1 and pt2 don't point into forwarder or
           adversary *)
        if (envport(pt1) /\ envport(pt2)) {
          send fw_obs(pt1, pt2, u) and transition Wait(pt1, pt2, u).
        }
        else { fail. }
      }
    | othermsg => { fail. }
    end
  }

  state Wait(pt1 : port, pt2 : port, u : univ) {
    match message with
    | fw_ok => { send fw_rsp(pt1, u)@pt2 and transition Final. }
    | othermsg => { fail. }
    end
  } 

  state Final {
    match message with
    | othermsg => { fail. }
    end
  }
}

(* key exchange *)

direct KEDirPt1 {
  in pt1@ke_req1(pt2 : port)
  out ke_rsp2(k : key)@pt1
}

direct KEDirPt2 {
  in pt2@ke_req2
  out ke_rsp1(pt1 : port, k : key)@pt2
}

direct KEDir {
  Pt1 : KEDirPt1
  Pt2 : KEDirPt2
}

functionality KEReal implements KEDir {
  subfun Fw1 = Forw
  subfun Fw2 = Forw

  party Pt1 serves KEDir.Pt1 {
    initial state WaitReq1 {
      var q1 : exp;
      match message with
      | pt1@ke_req1(pt2) => {
          if (envport(pt1) /\ envport(pt2)) {
            q1 <$ dexp;
            send Fw1.D.fw_req(Pt2, encode (pt1, pt2, g ^ q1))
            and transition WaitFwd2(pt1, pt2, q1).
          }
          else { fail. }
        }
      | othermsg => { fail. }
      end
    }

    state WaitFwd2(pt1 : port, pt2 : port, q1 : exp) {
      match message with
      | Fw2.D.fw_rsp(_, u) => {
          decode u as key with
          | ok k2 => {
              send ke_rsp2(k2 ^ q1)@pt1 and transition Final.
            }
          | error => { fail. }
          end
        }
      | othermsg => { fail. }
      end
    }
  
    state Final {
      match message with
      | othermsg => { fail. }
      end
    }
  }

  party Pt2 serves KEDir.Pt2 {
    initial state WaitFwd1 {
      var q2 : exp;
      match message with
      | Fw1.D.fw_rsp(_, u) => {
          decode u as port * port * key with
          | ok (pt1, pt2, k1) => {
              q2 <$ dexp;
              send ke_rsp1(pt1, k1 ^ q2)@pt2
              and transition WaitReq2(pt1, pt2, q2).
            }
          | error => { fail. }  (* cannot happen *)
          end
        }
      | othermsg => { fail. }
      end
    }

    state WaitReq2(pt1 : port, pt2 : port, q2 : exp) {
      match message with
      | pt2'@ke_req2 => { 
          if (pt2' = pt2) {
            send Fw2.D.fw_req(Pt1, encode (g ^ q2)) and transition Final.
          }
          else { fail. }
        }
      | othermsg => { fail. }
      end
    }

    state Final {
      match message with
      | othermsg => { fail. }
      end
    }
  }
}

adversarial KEI2S {
  out ke_sim_req1(pt1 : port, pt2 : port)
  in ke_sim_rsp
  out ke_sim_req2
}

functionality KEIdeal implements KEDir KEI2S {
  initial state WaitReq1 {
    match message with
    | pt1@ke_req1(pt2) => {
        if (envport(pt1) /\ envport(pt2)) {
          send ke_sim_req1(pt1, pt2) and transition WaitSim1(pt1, pt2).
        }
        else { fail. }
      }
    | othermsg => { fail. }
    end
  }

  state WaitSim1(pt1 : port, pt2 : port) {
    var q : exp;
    match message with
    | ke_sim_rsp => {
        q <$ dexp;
        send ke_rsp1(pt1, g ^ q)@pt2 and transition WaitReq2(pt1, pt2, q).
      }
    | othermsg => { fail. }
    end
  }

  state WaitReq2(pt1 : port, pt2 : port, q : exp) {
    match message with
    | pt2'@ke_req2 => {
        if (pt2' = pt2) {
          send ke_sim_req2 and transition WaitSim2(pt1, pt2, q).
        }
        else { fail. }
      }
    | othermsg => { fail. }
    end
  }

  state WaitSim2(pt1 : port, pt2 : port, q : exp) {
    match message with
    | ke_sim_rsp => {
        send ke_rsp2(g ^ q)@pt1 and transition Final.
      }
    | othermsg => { fail. }
    end
  }

  state Final {
    match message with
    | othermsg => { fail. }
    end
  }
}

simulator KESim uses KEI2S simulates KEReal() {
  initial state WaitReq1 {
    var q1 : exp;
    match message with 
    | KEI2S.ke_sim_req1(pt1, pt2) => {
        (* simulator implicitly learns address of ideal functionality *)
        q1 <$ dexp;
        send KEReal.Fw1.FwAdv.fw_obs
             (KEReal.Pt1, KEReal.Pt2, encode (pt1, pt2, g ^ q1))
        and transition WaitAdv1(q1).
      }    
    | KEI2S.othermsg => { fail. }  (* catches ke_sim_req2 *)
    (* messages from adversary to real functionality will go to
       ideal functionality *)
    end
  }

  state WaitAdv1(q1 : exp) {
    var q2 : exp;
    match message with 
    | KEReal.Fw1.FwAdv.fw_ok => {
        q2 <$ dexp;
        send KEI2S.ke_sim_rsp and transition WaitReq2(q1, q2).
      }
    (* messages with addresses not >= address of ideal functionality
       are implicitly passed to environment *)
    | othermsg => { fail. }
    end
  }

  state WaitReq2(q1 : exp, q2 : exp) {
    match message with 
    | KEI2S.ke_sim_req2 => {
        send KEReal.Fw2.FwAdv.fw_obs(KEReal.Pt2, KEReal.Pt1, encode (g ^ q2))
        and transition WaitAdv2(q1, q2).
      }
    | othermsg => { fail. }
    end
  }

  state WaitAdv2(q1 : exp, q2 : exp) {
    match message with 
    | KEReal.Fw2.FwAdv.fw_ok => {
        send KEI2S.ke_sim_rsp and transition Final.
      }
    | othermsg => { fail. }
    end
   }

  state Final {
    match message with
    | othermsg => { fail. }
    end
  }
}

(* secure message communication *)

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
      | pt1@smc_req(pt2, t) => {
          if (envport(pt1) /\ envport(pt2)) {
            send KE.Pt1.ke_req1(Pt2) and transition WaitKE2(pt1, pt2, t).
          }
          else { fail. }
        }
      | othermsg => { fail. }
      end
    }

    state WaitKE2(pt1 : port, pt2 : port, t : text) {
      match message with 
      | KE.Pt1.ke_rsp2(k) => {
          send Fwd.D.fw_req(Pt2, encode (pt1, pt2, inj t ^^ k))
          and transition Final.
        }
      | othermsg => { fail. }
      end
    }

    state Final {
      match message with 
      | othermsg => { fail. }
      end
    }
  }

  party Pt2 serves SMCDir.Pt2 {
    initial state WaitKE1 {
      match message with 
      | KE.Pt2.ke_rsp1 (_, k) => {
          send KE.Pt2.ke_req2 and transition WaitFwd(k).
        }
      | othermsg => { fail. }
      end
    }

    state WaitFwd(k : key) {
      match message with 
      | Fwd.D.fw_rsp(_, u) => {
          decode u as port * port * key with
          | ok (pt1, pt2, x) => {
              send smc_rsp(pt1, projFudge(x ^^ kinv k))@pt2
              and transition Final.
            }
          | error => { fail. }
          end
        }
      | othermsg => { fail. }
      end
    }

    state Final {
      match message with 
      | othermsg => { fail. }
      end
    }
  }
}

adversarial SMC2Sim {
  out sim_req(pt1 : port, pt2 : port)
  in sim_rsp
}

functionality SMCIdeal implements SMCDir SMC2Sim {
  initial state WaitReq {
    match message with 
    | pt1@smc_req(pt2, t) => {
        if (envport(pt1) /\ envport(pt2)) {
          send sim_req(pt1, pt2) and transition WaitSim(pt1, pt2, t).
        }
        else { fail. }
      }
    | othermsg => { fail. }
    end
  }

  state WaitSim(pt1 : port, pt2 : port, t : text) {
    match message with 
    | sim_rsp => {
        send smc_rsp(pt1, t)@pt2 and transition Final.
      }
    | othermsg => { fail. }
    end
  }

  state Final {
    match message with 
    | othermsg => { fail. }
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
    | SMC2Sim.othermsg => { fail. }
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
    | othermsg => { fail. }
    end
  }

  state WaitAdv2(pt1 : port, pt2 : port, q : exp) {
    match message with 
    | SMCReal.KE.KEI2S.ke_sim_rsp => {
        send SMCReal.Fwd.FwAdv.fw_obs
             (SMCReal.Pt1, SMCReal.Pt2, encode (pt1, pt2,g ^ q))
        and transition WaitAdv3(pt1, pt2, q).
      }
    | othermsg => { fail. }
    end
  }

  state WaitAdv3(pt1 : port, pt2 : port, q : exp) {
    match message with 
    | SMCReal.Fwd.FwAdv.fw_ok => {
        send SMC2Sim.sim_rsp and transition Final.
      }
    | othermsg => { fail. }
    end
  }

  state Final {
    match message with
    | othermsg => { fail. }
    end
  }
}
