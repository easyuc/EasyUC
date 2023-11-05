direct D' {
in x@bla()
out bli()@x
}

direct D {D:D'}

adversarial I {
in  bla()
out bli()
}

functionality S() implements D {

  initial state Is 
  {
   match message with
     * => {fail.}
   end
  }
 
}

