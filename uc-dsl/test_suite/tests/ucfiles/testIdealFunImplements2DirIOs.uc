direct d {
in x@bla()
out bli()@x
}

direct D {d:d}

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

