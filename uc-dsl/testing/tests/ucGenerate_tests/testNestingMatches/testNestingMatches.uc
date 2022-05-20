direct D_basic {
  in pt@msg1()
  in pt@msg2()
}

direct D_composite {
  I : D_basic
}

adversarial A_basic {
out msg0()
}

functionality IdealF implements D_composite A_basic {
  initial state Init {  (* the functionality starts in this state *)
    match message with
    | p@D_composite.I.msg1() => { fail. }
    | p@D_composite.I.msg2() => { fail. }
    end
  }
}
