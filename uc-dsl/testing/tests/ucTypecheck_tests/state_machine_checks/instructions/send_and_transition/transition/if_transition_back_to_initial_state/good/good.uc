direct D' {
  in pt1@ping(pt2 : port)
  out pong(pt1 : port)@pt2
}

direct D {
  D' : D'
}

adversarial A {
  in ping
  out pong
}

functionality Foo implements D A {
  initial state Init {
    match message with
    | pt1@D.D'.ping(pt2) => {
        send A.pong and transition Final.
      }
    end
  }

  state Final {
    match message with
    | * => { fail. }
    end
  }
}


