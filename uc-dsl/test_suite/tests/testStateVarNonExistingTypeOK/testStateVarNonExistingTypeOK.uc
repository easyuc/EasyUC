requires KeysExponentsAndPlainTexts.

direct a {
in  x@bla()
out bli()@x
}

direct A {A:a}

functionality F() implements A {

 party P serves A {

  initial state I {
   var a b : univ;
   match message with
    othermsg => {fail.}
   end
  }
 }
}
