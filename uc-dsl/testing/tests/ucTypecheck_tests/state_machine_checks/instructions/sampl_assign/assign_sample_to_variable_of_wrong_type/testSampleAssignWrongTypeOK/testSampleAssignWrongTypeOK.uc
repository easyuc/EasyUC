ec_requires +KeysExponentsAndPlainTexts.

direct A' {
in  x@bla()
out bli()@x
}

direct A {A:A'}

functionality F() implements A {

 party P serves A.A {

  initial state I {
   var x : exp;
   match message with
    x@A.A.bla => {x <$ dexp; fail.}
   end
  }
 }
}
