ec_requires +Guid.

direct Dir {
  in pt1@req(pt2 : port)
  out rsp@pt2
}

direct DIR {
  D : Dir
}

adversarial Adv {
  out req
  in rsp
}

adversarial ADV {
  D : Adv
}


functionality Real implements DIR ADV {
  party Pt serves DIR.D ADV.D {
    initial state Init {
      match message with
      | pt1@DIR.D.req(pt2) => {
          if (envport pt2) {
            send ADV.D.req
            and transition WaitAdv(pt2).
          }
          else { fail. }
        }
      end
    }
    state WaitAdv(pt2 : port) {
      match message with
      | ADV.D.rsp => {
          send DIR.D.rsp@pt2
          and transition Final.
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

adversarial Adv2Sim {
  out req
  in rsp
}

functionality Ideal implements DIR Adv2Sim {
  initial state Init {
    match message with
    | pt1@DIR.D.req(pt2) => {
        send Adv2Sim.req and transition Wait(pt2).
      }
    end
  }

  state Wait(pt2 : port) {
    match message with
    | Adv2Sim.rsp => {
        send DIR.D.rsp@pt2 and transition Final.
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

simulator Sim uses Adv2Sim simulates Real {
  initial state Init {
    match message with
    | Adv2Sim.req => {
        send Real.ADV.D.req and transition WaitAdv.
      }
    end
  }

  state WaitAdv {
    match message with
    | Real.ADV.D.rsp => {
        send Adv2Sim.rsp and transition Final.
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
