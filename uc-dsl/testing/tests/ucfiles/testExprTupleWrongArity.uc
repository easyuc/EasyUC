requires KeysExponentsAndPlainTexts.

direct a {
in  x@bla()
out bli()@x
}

direct A {A:a}

functionality F() implements A {

 party P serves A {

  initial state I {
   var pp:port*port;
   match message with
    sender@othermsg => {pp<-sender; fail.}
   end
  }
 }
}
