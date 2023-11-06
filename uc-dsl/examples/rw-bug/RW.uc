ec_requires +Rewriting.

direct Dir {
  in pt@req(xs : int list)
  out rsp(xs : int list)@pt
}

direct DIR {
  D : Dir
}

functionality Real implements DIR {
  party Pt serves DIR.D {
    initial state Init {
      match message with
      | pt@DIR.D.req(xs) => {
          send DIR.D.rsp
               (if 2 + size xs <= 0 then []
                else 1 ::
                     if 1 + size xs <= 0 then []
                     else 2 :: xs)@pt
          and transition Final.
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

adversarial Adv {
  out req
  in rsp
}

functionality Ideal implements DIR Adv {
  initial state Init {
    match message with
    | pt@DIR.D.req(xs) => {
        send Adv.req and transition Wait(pt, xs).
      }
    end
  }

  state Wait(pt : port, xs : int list) {
    match message with
    | Adv.rsp => {
        send DIR.D.rsp([1; 2] ++ xs)@pt and transition Final.
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

simulator Sim uses Adv simulates Real {
  initial state Init {
    match message with
    | Adv.req => {
        send Adv.rsp and transition Final.
      }
    end
  }

  state Final {
    match message with
    | * => { fail. }
    end
  }
}
