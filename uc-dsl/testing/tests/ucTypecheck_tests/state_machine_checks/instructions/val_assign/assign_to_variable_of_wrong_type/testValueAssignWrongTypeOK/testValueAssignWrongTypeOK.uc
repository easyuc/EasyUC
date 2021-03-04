ec_requires +KeysExponentsAndPlainTexts.

direct A' {
in  x@bla()
out bli()@x
}

direct A {A:A'}

functionality F() implements A {

 party P serves A.A {

  initial state I {
   var x : key;
   match message with
    y@A.A.bla => { x<-g^e; fail. }
   end
  }
 }
}
