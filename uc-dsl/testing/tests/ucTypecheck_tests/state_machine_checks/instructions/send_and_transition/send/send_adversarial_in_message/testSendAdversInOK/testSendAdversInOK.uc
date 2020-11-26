direct D_ {
in  x@bla()
out bli()@x
}

direct D {D:D_}

adversarial A_ {
in  bla()
out bli()
}

adversarial A {A:A_}

functionality F() implements D A {

 party P serves A.A D.D {

  initial state I {
   match message with
     D.D.* => {send A.A.bli() and transition I.}
   | * => {fail.}
   end
  }
 }
}
