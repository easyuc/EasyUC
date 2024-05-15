direct D' {
in x'@bla(x : int)
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
   var x : int;
   match message with
     y@D.D.bla(_) => {fail.}
   end
  }
 }
}

