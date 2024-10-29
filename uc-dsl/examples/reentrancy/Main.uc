(* simple one party main functionality that uses Comp *)

uc_requires Comp.
ec_requires +Comp.

direct Dir' {
  in pt@start
  out ok@pt
}

direct Dir {
  D : Dir'
}

adversarial Adv' {
  out suspend
  in resume
}

adversarial Adv {
  A : Adv'
}

functionality MainReal(Comp : Comp.CompDir) implements Dir Adv {
  party Pt serves Dir.D Adv.A {
    initial state Init {
      match message with
      | pt@Dir.D.start => {
          send Adv.A.suspend and transition First(pt).
        }
      | *              => { fail. }
      end
    }

    state First(pt : port) {
      match message with
      | Adv.A.resume => {
          send Comp.Pt1.req(5) and transition Second(pt).
        }
      | *            => { fail. }
      end
    }

    state Second(pt : port) {
      match message with
      | Adv.A.resume => {
          send Comp.Pt2.req(-10) and transition Third(pt, None, None).
        }
      | *            => { fail. }
      end
    }

    state Third(pt : port, out1opt : int option, out2opt : int option) {
      match message with
      | Comp.Pt1.rsp(_, n1) => {
          if (out1opt <> None) { fail. }
          elif (out2opt = None) {
            send Adv.A.suspend
            and transition Third(pt, Some n1, None).
          }
          elif (n1 + oget out2opt = 10) {
            send Dir.D.ok@pt and transition Final.
          }
          else { fail. }
        }
      | Comp.Pt2.rsp(_, n2) => {
          if (out2opt <> None) { fail. }
          elif (out1opt = None) {
            send Adv.A.suspend
            and transition Third(pt, None, Some n2).
          }
          elif (oget out1opt + n2 = 10) {
            send Dir.D.ok@pt and transition Final.
          }
          else { fail. }
        }
      | Adv.A.resume        => {
          send Adv.A.suspend
          and transition Third(pt, out1opt, out2opt).
        }
      | *                   => { fail. }
      end
    }

    state Final {
      match message with
        * => { fail. }
      end
    }
  }
}

adversarial MainIdeal2Sim {
  out start
  in don
}

functionality MainIdeal implements Dir MainIdeal2Sim {
  initial state Init {
    match message with
    | pt@Dir.D.start => {
        send MainIdeal2Sim.start and transition WaitSim(pt).
      }
    end
  }

  state WaitSim(pt : port) {
    match message with
    | MainIdeal2Sim.don => {
        send Dir.D.ok@pt and transition Final.
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

simulator MainSim
    uses MainIdeal2Sim simulates MainReal(Comp.CompIdeal) {
  initial state Init {
    match message with
    | MainIdeal2Sim.start => {
        send MainReal.Adv.A.suspend and transition First.
      }
    end
  }

  state First {
    match message with
    | MainReal.Adv.A.resume => {
        send MainReal.Comp.CompIdeal2Sim.inp_received(Pt1)
        and transition Second.
      }
    | *                     => { fail. }
    end
  }

  state Second {
    match message with
    | MainReal.Adv.A.resume => {
        send MainReal.Comp.CompIdeal2Sim.inp_received(Pt2)
        and transition Third.
      }
    | *                     => { fail. }
    end
  }

  state Third {
    match message with
    | MainReal.Comp.CompIdeal2Sim.out_enabled(_) => {
        send MainReal.Adv.A.suspend and transition Fourth.
      }
    | MainReal.Adv.A.resume                      => {
        send MainReal.Adv.A.suspend and transition Third.
      }
    | *                                          => { fail. }
    end
  }

  state Fourth {
    match message with
    | MainReal.Comp.CompIdeal2Sim.out_enabled(_) => {
        send MainIdeal2Sim.don and transition Final.
      }
    | MainReal.Adv.A.resume                      => {
        send MainReal.Adv.A.suspend and transition Fourth.
      }
    | *                                          => { fail. }
    end
  }

  state Final {
    match message with
    | * => { fail. }
    end
  }
}
