requires KeysExponentsAndPlainTexts.

direct a {
in  x@bla()
out bli()@x
}

direct A {A:a}

functionality F() implements A {

 party P serves A {

  initial state I {
   var s:univ;
   match message with
    sender@othermsg => {s<-encode sender; fail.}
   end
  }
 }
}
