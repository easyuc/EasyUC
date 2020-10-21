direct d {
in x@bla()
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
     p@A.A.bla => {fail.}
   | * => {fail.}
   end
  }
 }
}

