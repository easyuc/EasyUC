ec_requires KeysExponentsAndPlainTexts.

direct a {
in  x@bla()
out bli()@x
}

direct A {A:a}

functionality F() implements A {

 party P serves A.A {

  initial state I {
   var k:key;
   match message with
    * => {k<-hen e;fail.}
   end
  }

 }
}
