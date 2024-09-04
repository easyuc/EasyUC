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
     p@D.D.bla => {send A.A.bli and transition Other.}
   end
  }
  state Other
  {
   match message with
     p@A.A.bla => {fail.}
   | * => {fail.}
   end
  }
 }
}

