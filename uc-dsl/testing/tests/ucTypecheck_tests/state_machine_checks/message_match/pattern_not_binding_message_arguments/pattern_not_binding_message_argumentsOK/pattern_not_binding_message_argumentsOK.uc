direct D' {
in x@bla(b:bool)
out bli()@x
}

direct D {D:D'}

functionality S() implements D {

 party P serves D.D {
  initial state Is 
  {
   match message with
     x@D.D.bla(b) => {fail.}
   end
  }
 }
}

