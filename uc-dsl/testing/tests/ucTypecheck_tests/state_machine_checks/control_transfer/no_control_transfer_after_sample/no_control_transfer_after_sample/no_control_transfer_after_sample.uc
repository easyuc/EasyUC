ec_requires +KeysExponentsAndPlainTexts.

direct D' {
in  x@bla()
out bli()@x
}

direct D {D:D'}

functionality F implements D {

 party P serves D.D {

  initial state I {
   var x : exp;
   match message with
    y@D.D.bla => {x <$ dexp; }
   end
  }
 }
}
