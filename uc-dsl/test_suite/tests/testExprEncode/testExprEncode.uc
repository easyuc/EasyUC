ec_requires KeysExponentsAndPlainTexts.

direct a {
in  x@bla()
out bli()@x
}

direct A {A:a}

functionality F() implements A {

 party P serves A.A {

  initial state I {
   var s:port;
   match message with
     sender@A.A.bla() => {s<-encode sender; fail.}
   end
  }
 }
}
