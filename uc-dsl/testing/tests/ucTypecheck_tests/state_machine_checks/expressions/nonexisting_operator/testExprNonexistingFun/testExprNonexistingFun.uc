ec_requires +KeysExponentsAndPlainTexts.

direct A' {
in  x@bla()
out bli()@x
}

direct A {A:A'}

functionality F() implements A {

 party P serves A.A {

  initial state I {
   var k:key;
   match message with
    y@A.A.bla => {k<-hen e;fail.}
   end
  }

 }
}
