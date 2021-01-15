ec_requires +KeysExponentsAndPlainTexts.

direct A_ {
in  x@bla(k:key)
out bli()@x
}

direct A {A:A_}

functionality F() implements A {

 party P serves A.A {

  initial state I {
   var x : key;
   match message with
    sender@A.A.bla(k) => { k<-g^e; fail. }
   end
  }
 }
}
