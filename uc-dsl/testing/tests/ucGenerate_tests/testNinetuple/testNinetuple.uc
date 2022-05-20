direct D_basic {
  in pt@mesg(a : int*int*int*int*int*int*int*int*bool)

}

direct D_composite {
  I : D_basic
}

adversarial A_basic {
out msg0()
}

functionality IdealF implements D_composite A_basic {
  initial state Init {
    match message with
    | p@D_composite.I.mesg(a) => { fail. }
    end
  }
}
