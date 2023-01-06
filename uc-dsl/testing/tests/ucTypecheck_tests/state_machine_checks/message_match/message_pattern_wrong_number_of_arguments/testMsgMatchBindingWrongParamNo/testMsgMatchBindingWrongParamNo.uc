direct D' {
in x@bla()
out bli()@x
}

direct D {D:D'}

adversarial A' {
in  bla()
out bli()
}

adversarial A {A:A'}

functionality S() implements D A {

 party P serves D.D A.A {
  initial state Is 
  {
   match message with
   | x@D.D.bla => {fail.}
   end
  }

  state Other
  {
   match message with
     A.A.bla(_) => {fail.}
   | *  => {fail.}
   end
  }
 }
}

