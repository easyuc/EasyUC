ec_requires KeysExponentsAndPlainTexts.

direct A_ {
in  x@bla()
out bli()@x
}

direct A {A:A_}

functionality F() implements A {

 party P serves A.A {

  initial state I {
   var pp:port*port;
   match message with
    sender@A.A.bla() => {pp<-(sender,sender); fail.}
   end
  }
 }
}
