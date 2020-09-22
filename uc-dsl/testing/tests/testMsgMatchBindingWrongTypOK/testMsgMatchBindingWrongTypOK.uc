ec_requires KeysExponentsAndPlainTexts.

direct d {
in x@k(k1 : key)
out bli()@x
}

direct D {D:d}

adversarial a {
in  bla()
out bli()
}

adversarial A {A:a}



functionality S() implements D A {

 party P serves D.D A.A {
  initial state Is 
  {
   match message with
     p@D.D.k(e) => {fail.}
   | *  => {fail.}
   end
  }
 }
}

