ec_requires KeysExponentsAndPlainTexts.

direct d {
in  x@bla()
out bli()@x
}

direct D {D:d}

adversarial a {
in  bla()
out bli()
}

adversarial A {A:a}

functionality F() implements D A {

 party P serves A.A D.D {

  initial state I {
   match message with
     D.D.*  => {send A.A.bli()@sender and transition I.}
   | * => {fail.}
   end
  }
 }
}
