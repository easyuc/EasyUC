direct D_ {
in x@bla()
out bli()@x
}

direct D {D:D_}

adversarial A_ {
in  bla()
out bli()
}

adversarial A {A:A_}



functionality S() implements D A {

 party P serves D.D A.A {
  initial state Is 
  {
   match message with
     A.A.bla() => {fail.}
   | * => {fail.}
   end
  }
 }
}

