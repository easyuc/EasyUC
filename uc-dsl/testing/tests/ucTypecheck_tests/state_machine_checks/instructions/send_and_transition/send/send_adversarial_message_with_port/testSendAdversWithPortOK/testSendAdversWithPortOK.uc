direct D' {
in  x@bla()
out bli()@x
}

direct D {D:D'}

adversarial A' {
in  bla()
out bli()
}

adversarial A {A:A'}

functionality F() implements D A {

 party P serves A.A D.D {

  initial state I {
   match message with
     x@D.D.bla  => {send A.A.bli() and transition J.}
   end
  }

  state J { match message with * => { fail. } end }
 }
}
