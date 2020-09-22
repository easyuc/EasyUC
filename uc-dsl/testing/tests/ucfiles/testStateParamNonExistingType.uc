requires KeysExponentsAndPlainTexts.

direct a {
in x@bla()
}

direct A {A:a}

functionality F() implements A {

 party P serves A {

  initial state I {
   match message with
    othermsg => {fail.}
   end
  }
 
  state II(k:kye) {
   match message with
    othermsg => {fail.}
   end
  }
 }
}
