direct D' {
  in x@foo
  out goo@y
}

direct D {
  D : D'
}

adversarial E {
  in who
}

functionality F implements D E {
  initial state A {
    var x : int;
    match message with
    | D.* => { fail. }
    end
  }
}
