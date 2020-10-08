ec_requires KeysExponentsAndPlainTexts.

direct a {
in  x@bla()
out bli()@x
}

direct A {A:a}

functionality F() implements A {

 party P serves A.A {
  initial state I {
   match message with
    sender@A.A.bla() => {send bli()@sender and transition I().}
   end
  }
 }
}
