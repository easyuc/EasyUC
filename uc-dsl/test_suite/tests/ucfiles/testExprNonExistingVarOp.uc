requires KeysExponentsAndPlainTexts.

direct a {
in  x@bla()
out bli()@x
}

direct A {A:a}

functionality F() implements A {

 party P serves A {

  initial state I {
   match message with
    sender@othermsg => {send bli()@sender and transition II(k.k).}
   end
  }
 
  state II(k:key) {
   match message with
    othermsg => {fail.}
   end
  }
 }
}
