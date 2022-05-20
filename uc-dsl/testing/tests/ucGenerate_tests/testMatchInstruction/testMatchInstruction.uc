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
  initial state Init {
    match message with
    | p@D_composite.I.msg1() => {
      match Logic.Some 1 with
      | None => { fail. }
      | Some _ => { fail. }
      end
    }
    end
  }
}
