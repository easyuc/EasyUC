direct X {
  in pt@msgin
  out msgout@pt
}

direct D {
  E : X
}

adversarial Y {
  in msgin
  out msgout
}

adversarial A {
  B : Y
}

functionality Ideal implements D A {
  party P serves D.E A.B {
    initial state Ini {
      match message with
        pt@D.E.msgin => {send A.B.msgout and transition Other.}
      end
    }

    state Other {
      match message with
        pt@D.E.msgin => {fail.}
      | A.B.msgin => {fail.}
      end
    }
  }
}
