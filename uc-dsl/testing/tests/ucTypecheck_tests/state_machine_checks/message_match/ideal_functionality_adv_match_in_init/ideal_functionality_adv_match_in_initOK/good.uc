direct X {
  in pt@msgin
  out msgout@pt
}

direct D {
  D : X
}

adversarial A {
  in msgin
  out msgout
}

functionality Ideal implements D A {
  initial state Ini {
    match message with
      pt@D.D.msgin => {fail.}
    end
  }
}
