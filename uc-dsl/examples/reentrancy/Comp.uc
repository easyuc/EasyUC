(* triple unit implementing a *reentrant*, two-party real
   functionality for carrying out a joint computation, together with an
   ideal functionality and simulator

   see Comp.ec for supporting definitions

   the adverarial model for the real functionality is that the
   adversary just plays the role of the scheduler *)

uc_requires FwdSched.
ec_requires +CompDefs.

direct CompDir' {
  (* pt makes a request by supplying an input n, but not specifying
     the other port that will contribute an input *)

  in pt@req(n : int)

  (* the result for pt also includes who the other participating
     port was, pt' *)

  out rsp(pt' : port, m : int)@pt
}

direct CompDir {
  Pt1 : CompDir'
  Pt2 : CompDir'
}

(* the basic adversarial interface to a party of the real
   functionality lets the party suspend its computation, giving
   control to the adversary; at a later point, the adversary can
   resume the party's computation (but reentrancy or communication
   from subfunctionalities may mean the party's state has changed, and
   resumption will be from that new state)

   until a party is in its final state, in which all messages result
   in failure, resumption never fails, but may result in immediate
   suspension *)

adversarial CompAdv' {
  out suspend  (* give control to adversary *)
  in  resume   (* resume control *)
}

adversarial CompAdv {
  Pt1 : CompAdv'
  Pt2 : CompAdv'
}

(* the real functionality

   once the functionality is reentered, the adversary will
   have multiple choices for what to schedule next - either
   approving forwarding or resuming suspended parties *)

functionality CompReal implements CompDir CompAdv {
  subfun Fwd1 = FwdSched.FwdSched
  subfun Fwd2 = FwdSched.FwdSched

  party Pt1 serves CompDir.Pt1 CompAdv.Pt1 {
    initial state Init {
      var pt2 : port; var n2 : int;
      match message with
      | pt1@CompDir.Pt1.req(n1) => {
          send CompAdv.Pt1.suspend
          and transition PendingFwd1WaitAdvOrFwd2(pt1, n1).
        }
      | Fwd2.D.rsp(_, u)        => {
          (pt2, n2) <- oget (epdp_port_int_univ.`dec u);
          send CompAdv.Pt1.suspend
          and transition WaitAdvOrInput(pt2, n2).
        }            
      | *                       => { fail. }
      end
    }

    state PendingFwd1WaitAdvOrFwd2(pt1 : port, n1 : int) {
      var pt2 : port; var n2 : int;
      match message with
      | CompAdv.Pt1.resume => {
          send Fwd1.D.req(intport Pt2, epdp_port_int_univ.`enc (pt1, f n1))
          and transition WaitAdvOrFwd2(pt1, n1).
        }
      | Fwd2.D.rsp(_, u)   => {
          (pt2, n2) <- oget (epdp_port_int_univ.`dec u);
          send CompAdv.Pt1.suspend
          and transition PendingFwd1WaitAdv(pt1, pt2, n1, n2).
        }            
      | *                  => { fail. }
      end
    }

    state PendingFwd1WaitAdv(pt1 : port, pt2 : port, n1 : int, n2 : int) {
      match message with
      | CompAdv.Pt1.resume => {
          send Fwd1.D.req(intport Pt2, epdp_port_int_univ.`enc (pt1, f n1))
          and transition PendingOutputWaitAdv(pt1, pt2, n1, n2).
        }
      | *                  => { fail. }
      end
    }

    state WaitAdvOrFwd2(pt1 : port, n1 : int) {
      var pt2 : port; var n2 : int;
      match message with
      | CompAdv.Pt1.resume => {
          send CompAdv.Pt1.suspend
          and transition WaitAdvOrFwd2(pt1, n1).
        }
      | Fwd2.D.rsp(_, u)   => {
          (pt2, n2) <- oget (epdp_port_int_univ.`dec u);
          send CompDir.Pt1.rsp(pt2, h n1 n2)@pt1
          and transition Final.
      }            
      | *                  => { fail. }
      end
    }

    state WaitAdvOrInput(pt2 : port, n2 : int) {
      match message with
      | CompAdv.Pt1.resume      => {
          send CompAdv.Pt1.suspend
          and transition WaitAdvOrInput(pt2, n2).
        }
      | pt1@CompDir.Pt1.req(n1) => {
          send Fwd1.D.req(intport Pt2, epdp_port_int_univ.`enc (pt1, f n1))
          and transition PendingOutputWaitAdv(pt1, pt2, n1, n2).
        }
      | *                       => { fail. }
      end
    }

    state PendingOutputWaitAdv(pt1 : port, pt2 : port, n1 : int, n2 : int) {
      match message with
      | CompAdv.Pt1.resume => {
          send CompDir.Pt1.rsp(pt2, h n1 n2)@pt1
          and transition Final.
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

  party Pt2 serves CompDir.Pt2 CompAdv.Pt2 {
    initial state Init {
      var pt1 : port; var n1 : int;
      match message with
      | pt2@CompDir.Pt2.req(n2) => {
          send CompAdv.Pt2.suspend
          and transition PendingFwd2WaitAdvOrFwd1(pt2, n2).
        }
      | Fwd1.D.rsp(_, u)        => {
          (pt1, n1) <- oget (epdp_port_int_univ.`dec u);
          send CompAdv.Pt2.suspend
          and transition WaitAdvOrInput(pt1, n1).
        }            
      | *                       => { fail. }
      end
    }

    state PendingFwd2WaitAdvOrFwd1(pt2 : port, n2 : int) {
      var pt1 : port; var n1 : int;
      match message with
      | CompAdv.Pt2.resume => {
          send Fwd2.D.req(intport Pt1, epdp_port_int_univ.`enc (pt2, g n2))
          and transition WaitAdvOrFwd1(pt2, n2).
        }
      | Fwd1.D.rsp(_, u)   => {
          (pt1, n1) <- oget (epdp_port_int_univ.`dec u);
          send CompAdv.Pt2.suspend
          and transition PendingFwd2WaitAdv(pt1, pt2, n1, n2).
        }            
      | *                  => { fail. }
      end
    }

    state PendingFwd2WaitAdv(pt1 : port, pt2 : port, n1 : int, n2 : int) {
      match message with
      | CompAdv.Pt2.resume => {
          send Fwd2.D.req(intport Pt1, epdp_port_int_univ.`enc (pt2, g n2))
          and transition PendingOutputWaitAdv(pt1, pt2, n1, n2).
        }
      | *                  => { fail. }
      end
    }

    state WaitAdvOrFwd1(pt2 : port, n2 : int) {
      var pt1 : port; var n1 : int;
      match message with
      | CompAdv.Pt2.resume => {
          send CompAdv.Pt2.suspend
          and transition WaitAdvOrFwd1(pt2, n2).
        }
      | Fwd1.D.rsp(_, u)   => {
          (pt1, n1) <- oget (epdp_port_int_univ.`dec u);
          send CompDir.Pt2.rsp(pt1, h n2 n1)@pt2
          and transition Final.
      }            
      | *                  => { fail. }
      end
    }

    state WaitAdvOrInput(pt1 : port, n1 : int) {
      match message with
      | CompAdv.Pt2.resume       => {
          send CompAdv.Pt2.suspend
          and transition WaitAdvOrInput(pt1, n1).
        }
      | pt2@CompDir.Pt2.req(n2) => {
          send Fwd2.D.req(intport Pt1, epdp_port_int_univ.`enc (pt2, g n2))
          and transition PendingOutputWaitAdv(pt1, pt2, n1, n2).
        }
      | *                        => { fail. }
      end
    }

    state PendingOutputWaitAdv(pt1 : port, pt2 : port, n1 : int, n2 : int) {
      match message with
      | CompAdv.Pt2.resume => {
          send CompDir.Pt2.rsp(pt1, h n2 n1)@pt2
          and transition Final.
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

adversarial CompIdeal2Sim {
  (* party pty's input received (that input or the client
     port is not included in the message) *)

  out inp_received(pty : party_name)  

  (* party pty's output enabled *)

  in  out_enabled(pty : party_name)   
}

(* the ideal functionality *)

functionality CompIdeal implements CompDir CompIdeal2Sim {
  (* the initial input is received by either one of the parties,
     and the simulator is informed *)

  initial state Init {
    match message with
    | pt1@CompDir.Pt1.req(n1) => {
        send CompIdeal2Sim.inp_received(Pt1)
        and transition AccumOtherInput(Some (pt1, n1), None).
      }
    | pt2@CompDir.Pt2.req(n2) => {
        send CompIdeal2Sim.inp_received(Pt2)
        and transition AccumOtherInput(None, Some (pt2, n2)).
      }
    end
  }

  (* the other party receives its input, and the simulator is
     informed; out_enabled messages will result in failure *)

  state AccumOtherInput
        (inp1_opt : (port * int) option, inp2_opt : (port * int) option) {
    match message with
    | pt1@CompDir.Pt1.req(n1) => {
        if (inp1_opt = None) {
          send CompIdeal2Sim.inp_received(Pt1)
          and transition
            HandleOutputs((pt1, n1), oget inp2_opt, false, false).
        }
        else { fail. }
      }
    | pt2@CompDir.Pt2.req(n2) => {
        if (inp2_opt = None) {
          send CompIdeal2Sim.inp_received(Pt2)
          and transition
            HandleOutputs(oget inp1_opt, (pt2, n2), false, false).
        }
        else { fail. }
      }
    | * => { fail. }
    end
  } 

  (* respond to out_enabled messages for the two parties *)

  state HandleOutputs
        (inp1 : port * int, inp2 : port * int,
         out1_done : bool, out2_done : bool) {
    match message with
    | CompIdeal2Sim.out_enabled(pty) => {
        match pty with
        | Pt1 => {
            if (out1_done) { fail. }
            elif (out2_done) {
              send CompDir.Pt1.rsp
                   (fst inp2, h (snd inp1) (g (snd inp2)))@(fst inp1)
              and transition Final.
            }
            else {
              send CompDir.Pt1.rsp
                   (fst inp2, h (snd inp1) (g (snd inp2)))@(fst inp1)
              and transition HandleOutputs(inp1, inp2, true, false).
            }
          }
        | Pt2 => {
            if (out2_done) { fail. }
            elif (out1_done) {
              send CompDir.Pt2.rsp
                   (fst inp1, h (snd inp2) (f (snd inp1)))@(fst inp2)
              and transition Final.
            }
            else {
              send CompDir.Pt2.rsp
                   (fst inp1, h (snd inp2) (f (snd inp1)))@(fst inp2)
              and transition HandleOutputs(inp1, inp2, false, true).
            }
          }
        end
      }
    | *                              => { fail. }
    end
  }

  (* all messages result in failure *)

  state Final {
    match message with
    | * => { fail. }
    end
  }
}

(* the simulator

   has to keep track of the abstract states of the two parties and two
   forwarders - see Comp.ec for the types *)

simulator CompSim uses CompIdeal2Sim simulates CompReal {
  initial state Init {
    match message with
    | CompIdeal2Sim.inp_received(pty_name) => {
        match pty_name with
        | Pt1 => {
            send CompReal.CompAdv.Pt1.suspend
            and transition
              Main
              (SPS_PendingFwdWaitAdvOrOtherFwd, SPS_Init,
               SFS_Init, SFS_Init).
          }
        | Pt2 => {
            send CompReal.CompAdv.Pt2.suspend
            and transition
              Main
              (SPS_Init, SPS_PendingFwdWaitAdvOrOtherFwd,
               SFS_Init, SFS_Init).
          }
        end
      }
    end
  }

  state Main
        (pty1state : sim_party_state, pty2state : sim_party_state,
         fwd1state : sim_fwd_state, fwd2state : sim_fwd_state) {
    match message with
    | CompIdeal2Sim.inp_received(pty_name) => {
        match pty_name with
        | Pt1 => {
            if (pty1state = SPS_Init) {
              send CompReal.CompAdv.Pt1.suspend
              and transition
                Main
                (SPS_PendingFwdWaitAdvOrOtherFwd, pty2state,
                 fwd1state, fwd2state).
            }
            elif (pty1state = SPS_WaitAdvOrInput /\ fwd1state = SFS_Init) {
              send CompReal.Fwd2.FwdSchedAdv.req
              and transition
                Main
                (SPS_PendingOutputWaitAdv, pty2state,
                 SFS_WaitOK, fwd2state).
            }
            else { fail. }
        }
        | Pt2 => {
            if (pty2state = SPS_Init) {
              send CompReal.CompAdv.Pt2.suspend
              and transition
                Main
                (pty1state, SPS_PendingFwdWaitAdvOrOtherFwd,
                 fwd1state, fwd2state).
            }
            elif (pty2state = SPS_WaitAdvOrInput /\ fwd2state = SFS_Init) {
              send CompReal.Fwd2.FwdSchedAdv.req
              and transition
                Main
                (pty1state, SPS_PendingOutputWaitAdv,
                 fwd1state, SFS_WaitOK).
            }
            else { fail. }
          }
        end
      }
    | CompReal.CompAdv.Pt1.resume          => {
        if (pty1state = SPS_PendingFwdWaitAdvOrOtherFwd /\
            fwd1state = SFS_Init) {
          send CompReal.Fwd1.FwdSchedAdv.req
          and transition
            Main(SPS_WaitAdvOrOtherFwd, pty2state, SFS_WaitOK, fwd2state).
        }
        elif (pty1state = SPS_PendingFwdWaitAdv /\ fwd1state = SFS_Init) {
          send CompReal.Fwd1.FwdSchedAdv.req
          and transition
            Main
            (SPS_PendingOutputWaitAdv, pty2state,
             SFS_WaitOK, fwd2state).
        }
        elif (pty1state = SPS_WaitAdvOrOtherFwd \/
              pty1state = SPS_WaitAdvOrInput) {
          send CompReal.CompAdv.Pt1.suspend
          and transition Main(pty1state, pty2state, fwd1state, fwd2state).
        }
        elif (pty1state = SPS_PendingOutputWaitAdv) {
          send CompIdeal2Sim.out_enabled(Pt1)
          and transition Main(SPS_Final, pty2state, fwd1state, fwd2state).
        }
        else { fail. }
      }
    | CompReal.CompAdv.Pt2.resume          => {
        if (pty2state = SPS_PendingFwdWaitAdvOrOtherFwd /\
            fwd2state = SFS_Init) {
          send CompReal.Fwd2.FwdSchedAdv.req
          and transition
            Main(pty1state, SPS_WaitAdvOrOtherFwd, fwd1state, SFS_WaitOK).
        }
        elif (pty2state = SPS_PendingFwdWaitAdv /\ fwd2state = SFS_Init) {
          send CompReal.Fwd2.FwdSchedAdv.req
          and transition
            Main
            (pty1state, SPS_PendingOutputWaitAdv,
             fwd1state, SFS_WaitOK).
        }
        elif (pty2state = SPS_WaitAdvOrOtherFwd \/
              pty2state = SPS_WaitAdvOrInput) {
          send CompReal.CompAdv.Pt2.suspend
          and transition Main(pty1state, pty2state, fwd1state, fwd2state).
        }
        elif (pty2state = SPS_PendingOutputWaitAdv) {
          send CompIdeal2Sim.out_enabled(Pt2)
          and transition Main(pty1state, SPS_Final, fwd1state, fwd2state).
        }
        else { fail. }
      }
    | CompReal.Fwd1.FwdSchedAdv.ok         => {
        if (fwd1state = SFS_WaitOK /\ pty2state = SPS_Init) {
          send CompReal.CompAdv.Pt2.suspend
          and transition
            Main(pty1state, SPS_WaitAdvOrInput, SFS_Final, fwd2state).
        }
        elif (fwd1state = SFS_WaitOK /\
              pty2state = SPS_PendingFwdWaitAdvOrOtherFwd ) {
          send CompReal.CompAdv.Pt2.suspend
          and transition
            Main(pty1state, SPS_PendingFwdWaitAdv, SFS_Final, fwd2state).
        }
        elif (fwd1state = SFS_WaitOK /\ pty2state = SPS_WaitAdvOrOtherFwd) {
          send CompIdeal2Sim.out_enabled(Pt2)
          and transition Main(pty1state, SPS_Final, SFS_Final, fwd2state).
        }
        else { fail. }
      }
    | CompReal.Fwd2.FwdSchedAdv.ok         => {
        if (fwd2state = SFS_WaitOK /\ pty1state = SPS_Init) {
          send CompReal.CompAdv.Pt1.suspend
          and transition
            Main(SPS_WaitAdvOrInput, pty2state, fwd1state, SFS_Final).
        }
        elif (fwd2state = SFS_WaitOK /\
              pty1state = SPS_PendingFwdWaitAdvOrOtherFwd ) {
          send CompReal.CompAdv.Pt1.suspend
          and transition
            Main(SPS_PendingFwdWaitAdv, pty2state, fwd1state, SFS_Final).
        }
        elif (fwd2state = SFS_WaitOK /\ pty1state = SPS_WaitAdvOrOtherFwd) {
          send CompIdeal2Sim.out_enabled(Pt1)
          and transition Main(SPS_Final, pty2state, fwd1state, SFS_Final).
        }
        else { fail. }
      }
    end
  }
}
