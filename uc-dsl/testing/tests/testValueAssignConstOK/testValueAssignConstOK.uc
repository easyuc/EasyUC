ec_requires KeysExponentsAndPlainTexts.

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
    bla(k) => { x<-k; fail. }
   |othermsg => {fail.}
   end
  }
 }
}
