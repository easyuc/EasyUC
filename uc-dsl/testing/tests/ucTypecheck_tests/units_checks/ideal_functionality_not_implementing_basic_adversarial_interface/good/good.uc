direct D' {
  in pt1@ping(pt2 : port)
  out pong(pt1 : port)@pt2
}

direct D {
  D' : D'
}

functionality Foo implements D {
  initial state Init {
    match message with
    | pt1@D.D'.ping(pt2) => {
        send D.D'.pong(pt1)@pt2 and transition Final.
      }
    end
  }

  state Final {
    match message with
    | * => { fail. }
    end
  }
}


