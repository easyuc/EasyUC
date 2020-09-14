(* Key Exchange *)

uc_requires Forwarding.

ec_requires KeysExponentsAndPlainTexts.

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
      | pt1@KEDir.Pt1.ke_req1(pt2) => {
          if (envport(pt1) /\ envport(pt2)) {
            q1 <$ dexp;
            send Fw1.D.fw_req(Pt2, encode (pt1, pt2, g ^ q1))
            and transition WaitFwd2(pt1, pt2, q1).
          }
          else { fail. }
        }
      | * => { fail. }
      end
    }

    state WaitFwd2(pt1 : port, pt2 : port, q1 : exp) {
      match message with
      | Fw2.D.fw_rsp(_, u) => {
          decode u as key with
          | ok k2 => {
              send KEDir.Pt1.ke_rsp2(k2 ^ q1)@pt1 and transition Final.
            }
          | error => { fail. }
          end
        }
      | * => { fail. }
      end
    }
  
    state Final {
      match message with
      | * => { fail. }
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
              send KEDir.Pt2.ke_rsp1(pt1, k1 ^ q2)@pt2
              and transition WaitReq2(pt1, pt2, q2).
            }
          | error => { fail. }  (* cannot happen *)
          end
        }
      | * => { fail. }
      end
    }

    state WaitReq2(pt1 : port, pt2 : port, q2 : exp) {
      match message with
      | pt2'@KEDir.Pt2.ke_req2 => { 
          if (pt2' = pt2) {
            send Fw2.D.fw_req(Pt1, encode (g ^ q2)) and transition Final.
          }
          else { fail. }
        }
      | * => { fail. }
      end
    }

    state Final {
      match message with
      | * => { fail. }
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
    | pt1@KEDir.Pt1.ke_req1(pt2) => {
        if (envport(pt1) /\ envport(pt2)) {
          send KEI2S.ke_sim_req1(pt1, pt2) and transition WaitSim1(pt1, pt2).
        }
        else { fail. }
      }
    | * => { fail. }
    end
  }

  state WaitSim1(pt1 : port, pt2 : port) {
    var q : exp;
    match message with
    | KEI2S.ke_sim_rsp => {
        q <$ dexp;
        send KEDir.Pt2.ke_rsp1(pt1, g ^ q)@pt2
        and transition WaitReq2(pt1, pt2, q).
      }
    | * => { fail. }
    end
  }

  state WaitReq2(pt1 : port, pt2 : port, q : exp) {
    match message with
    | pt2'@KEDir.Pt2.ke_req2 => {
        if (pt2' = pt2) {
          send KEI2S.ke_sim_req2 and transition WaitSim2(pt1, pt2, q).
        }
        else { fail. }
      }
    | * => { fail. }
    end
  }

  state WaitSim2(pt1 : port, pt2 : port, q : exp) {
    match message with
    | KEI2S.ke_sim_rsp => {
        send KEDir.Pt1.ke_rsp2(g ^ q)@pt1 and transition Final.
      }
    | * => { fail. }
    end
  }

  state Final {
    match message with
    | * => { fail. }
    end
  }
}

simulator KESim uses KEI2S simulates KEReal {
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
    | * => { fail. }  (* only catches KEI2S.ke_sim_req2 *)
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
    | * => { fail. }
    end
  }

  state WaitReq2(q1 : exp, q2 : exp) {
    match message with 
    | KEI2S.ke_sim_req2 => {
        send KEReal.Fw2.FwAdv.fw_obs(KEReal.Pt2, KEReal.Pt1, encode (g ^ q2))
        and transition WaitAdv2(q1, q2).
      }
    | * => { fail. }
    end
  }

  state WaitAdv2(q1 : exp, q2 : exp) {
    match message with 
    | KEReal.Fw2.FwAdv.fw_ok => {
        send KEI2S.ke_sim_rsp and transition Final.
      }
    | * => { fail. }
    end
   }

  state Final {
    match message with
    | * => { fail. }
    end
  }
}
