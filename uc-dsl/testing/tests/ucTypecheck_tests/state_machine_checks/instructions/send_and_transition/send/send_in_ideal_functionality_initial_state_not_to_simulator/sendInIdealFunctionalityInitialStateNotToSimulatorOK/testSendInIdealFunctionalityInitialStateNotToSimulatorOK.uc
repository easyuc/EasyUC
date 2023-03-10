direct D' {
in  x@bla()
out bli()@x
}

direct D {D:D'}

adversarial A {
in  bla()
out bli()
}

functionality F() implements D A {
  initial state I {
   match message with
     x@D.D.bla => {send A.bli and transition J.}
   end
  }

  state J { match message with * => { fail. } end }
}
