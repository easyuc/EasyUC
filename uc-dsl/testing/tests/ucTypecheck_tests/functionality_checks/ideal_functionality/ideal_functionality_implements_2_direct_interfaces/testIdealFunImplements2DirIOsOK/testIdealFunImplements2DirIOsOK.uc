direct d {
in x@bla()
out bli()@x
}

direct D {d:d}

adversarial I {
in  bla()
out bli()
}

functionality S() implements D I {

  initial state Is 
  {
   match message with
     * => {fail.}
   end
  }
 
}

