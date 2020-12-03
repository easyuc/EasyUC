ec_requires KeysExponentsAndPlainTexts.

direct A_ {
in  x@bla()
out bli()@x
}

direct A {A:A_}

functionality F() implements A {

 party P serves A.A {

  initial state I {
   match message with
    sender@A.A.bla() => {send A.A.bli()@sender and transition II(e^g).}
   end
  }
 
  state II(k:key) {
   match message with
    * => {fail.}
   end
  }
 }
}
