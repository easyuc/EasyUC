direct D_ {
in x@bla()
out bli()@x
}

direct D {D:D_}

functionality S() implements D {

 party P serves D.D {
  initial state Is 
  {
   match message with
     x@D.D.bla() => {fail.}
   end
  }
 }
}

