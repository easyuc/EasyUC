ec_requires +KeysExponentsAndPlainTexts.

direct D_ {
in  x@bla()
out bli()@x
}

direct D {D:D_}

functionality F implements D {

 party P serves D.D {

  initial state I {
   var x : exp;
   match message with
    * => {x <$ dexp; fail.}
   end
  }
 }
}
