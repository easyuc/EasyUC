direct d {
in x@bla()
out bli()@x
}

direct D {D:d}

functionality S() implements D {

 party P serves D.D {
  initial state Is 
  {
   match message with
     D.D.bla() => {fail.}
   end
  }
 }
}

