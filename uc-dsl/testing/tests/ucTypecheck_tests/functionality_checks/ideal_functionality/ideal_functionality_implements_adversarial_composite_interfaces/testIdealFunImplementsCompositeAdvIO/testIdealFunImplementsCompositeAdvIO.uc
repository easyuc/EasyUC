direct D' {
in  x@bla()
out bli()@x
}

direct D {D:D'}

adversarial I {
in  bla()
out bli()
}

adversarial A {
I1 : I
I2 : I
}

functionality S() implements D A {

  initial state Is 
  {
   match message with
     * => {fail.}
   end
  }
 
}

