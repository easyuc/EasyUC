ec_requires KeysExponentsAndPlainTexts.

direct a {
in  x@bla(k:key)
out bli()@x
}

direct A {A:a}

functionality F() implements A {

 party P serves A.A {

  initial state I {
   var x : key;
   match message with
    sender@A.A.bla(k) => { x<-k; fail. }
   end
  }
 }
}
