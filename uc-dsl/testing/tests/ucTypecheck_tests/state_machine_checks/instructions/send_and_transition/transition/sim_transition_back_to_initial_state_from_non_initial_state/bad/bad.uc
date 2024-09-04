direct D' {
in  x@bla()
out bli()@x
}

direct D {D':D'}

adversarial A {
  in ping
  out pong
}

functionality F() implements D {

 party P serves D.D' {

  initial state I {
   match message with
    sender@D.D'.bla() => { fail. }
   end
  }
 }
}

simulator S uses A simulates F {
  initial state Init {
    match message with
    | A.pong => { send A.ping and transition Init. }
    end
  }
}
