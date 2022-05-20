direct D_basic {
  in pt@msg1()
}

direct D_composite {
  I : D_basic
}

adversarial A_basic {
out msg0()
}

functionality IdealF implements D_composite A_basic {
  initial state Init {  (* the functionality starts in this state *)
    var i : int;
    match message with
    | p@D_composite.I.msg1() => { i<-0; fail. }
    end
  }
}
