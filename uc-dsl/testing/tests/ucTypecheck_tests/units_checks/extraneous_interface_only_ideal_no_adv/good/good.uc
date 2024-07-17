direct D' {
in x@bla()
out bli()@x
}

direct D {D:D'}

functionality S() implements D {

  initial state Is 
  {
   match message with
     * => {fail.}
   end
  }
 
}

