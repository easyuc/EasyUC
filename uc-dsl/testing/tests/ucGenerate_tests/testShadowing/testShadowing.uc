direct D_basic {
  in pt@int_univ()
  in pt@option(m : int)
  in pt@port(p : port option)
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
    | p@D_composite.I.port(po) => {
      match Logic.Some 1 with
      | None => { fail. }
      | Some _ => { fail. }
      end
      }
    | p@D_composite.I.option(m) => {
      match Logic.Some 1 with
      | None => { fail. }
      | Some _ => { fail. }
      end
      }
    | p@D_composite.I.int_univ() => {
      match Logic.Some 1 with
      | None => { fail. }
      | Some _ => { fail. }
      end
      }
    end
  }
}
