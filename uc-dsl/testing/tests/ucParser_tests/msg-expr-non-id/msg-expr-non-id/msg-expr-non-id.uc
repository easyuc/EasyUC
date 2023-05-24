direct A' {
  in x@bla
  out bli@x
}

direct A {A:A'}

functionality F() implements A {
  party P serves A.A {
    initial state S {
      match message with
        pt@A.A.bla => {
          send A.A.bli@ if true then pt else pt and
          transition F.
        }
      end
    }

    state F {
      match message with
        * => { fail. }
      end
    }
  }
}
