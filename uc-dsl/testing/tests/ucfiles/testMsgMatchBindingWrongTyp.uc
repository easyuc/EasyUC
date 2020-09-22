requires KeysExponentsAndPlainTexts.

direct d {
in x@k(k:key)
out bli()@x
}

direct D {D:d}

adversarial a {
in  bla()
out bli()
}

adversarial A {A:a}



functionality S() implements D A {

 party P serves D,A {
  initial state Is 
  {
   match message with
     D.k(e:exp) => {fail.}
   | othermsg => {fail.}
   end
  }
 }
}

