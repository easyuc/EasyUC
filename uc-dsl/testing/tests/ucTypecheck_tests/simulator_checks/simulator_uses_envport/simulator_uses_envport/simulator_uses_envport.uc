direct D' {
  in  x@bla()
  out bli()@x
}

direct D {D:D'}

functionality R() implements D {

 party P serves D.D {

  initial state I {
  match message with * => {fail.} end
  }
 }
}

adversarial A {
  out start(pt : port)
  in stop
}

simulator S uses A simulates R() {
  initial state I {
    match message with
    | A.start(pt) => {
        if (envport pt) {
          send A.stop and transition F.
        }
        else {
          fail.
        }
      }
    end
  }

  state F {
    match message with
    | * => { fail. }
    end
  }
}
