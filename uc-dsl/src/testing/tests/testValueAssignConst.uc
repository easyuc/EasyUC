requires KeysExponentsAndPlainTexts.

direct a {
in  x@bla(k:key)
out bli()@x
}

direct A {A:a}

functionality F() implements A {

 party P serves A {

  initial state I {
   var x : key;
   match message with
    bla(k) => { k<-g^e; fail. }
   |othermsg => {fail.}
   end
  }
 }
}
