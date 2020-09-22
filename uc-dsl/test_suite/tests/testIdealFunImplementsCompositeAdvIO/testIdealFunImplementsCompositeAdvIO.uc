direct d {
in  x@bla()
out bli()@x
}

direct D {d:d}

adversarial I {
in  bla()
out bli()
}

adversarial A {
i1 : I
i2 : I
}

functionality S() implements D A {

  initial state Is 
  {
   match message with
     * => {fail.}
   end
  }
 
}

