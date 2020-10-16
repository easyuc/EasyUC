ec_requires KeysExponentsAndPlainTexts.

direct a {
in  x@bla()
out bli()@x
}

direct A {A:a}

functionality F() implements A {

 party P serves A.A {

  initial state I {
   var x : exp;
   match message with
    * => {x <$ e; fail.}
   end
  }
 }
}
