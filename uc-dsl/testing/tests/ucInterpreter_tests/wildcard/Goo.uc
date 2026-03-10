ec_requires +Foo.

direct D' {
  in pt@inp
  out outp@pt
}

direct D {
  D : D'
}

functionality RF implements D {
  party P serves D.D {
    initial state Init {
      match message with
      | pt@D.D.inp => {
          match A 3 true with
          | B => { fail. }
          | _ => {
              send D.D.outp@pt and transition Final.
            }
          end
        }
      end
    }
    state Final {
      match message with
      | * => { fail. }
      end
    }
  }
}

adversarial A {
  in rsp
  out req
}

functionality IF implements D A {
  initial state I {
    match message with
    | pt@D.D.inp => {
        send A.req and transition S(pt).
      }
    end
  }
  state S(pt : port) {
    match message with
    | A.rsp => {
        send D.D.outp@pt and transition Final.
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

simulator Sim uses A simulates RF {
  initial state I {
    match message with
    | A.req => { send A.rsp and transition Final. }
    end
  }
  state Final {
    match message with
    | * => { fail. }
    end
  }
}
