direct D' {
in x@bla()
out bli()@x
}

direct D {D:D'}

direct I {
in  x@bla()
out bli()@x
}

functionality S() implements D I {

  initial state Is 
  {
   match message with
     othermsg => {fail.}
   end
  }
 
}

