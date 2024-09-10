direct D' {
  in pt@foo(x : int)
  in pt@fool
  out goo@pt
}

direct D {
  D': D'
}

functionality Foo implements D {
  party P serves D.D' {
    initial state Init {
      match message with
      | pt@D.D'.foo(x) => {
          if (x = 0) { send D.D'.goo@pt and transition Other1. }
          else {
            send D.D'.goo@pt and transition Other2.
          }
        }
      | pt@D.D'.fool => {
          send D.D'.goo@pt and transition Other3.
        }
      end          
    }

    state Other1 {
      match message with
      | * => { fail. }
      end
    }

    state Other2 {
      match message with
      | * => { fail. }
      end
    }

    state Other3 {
      match message with
      | pt@D.D'.fool => { fail. }
      | *            => { fail. }
      end
    }

    state Other4 {
      match message with
      | * => { fail. }
      end
    }
  }
}



