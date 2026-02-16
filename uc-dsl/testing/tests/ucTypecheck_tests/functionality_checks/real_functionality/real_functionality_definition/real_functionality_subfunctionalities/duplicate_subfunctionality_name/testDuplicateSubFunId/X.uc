direct D' {
in x@bla()
}

direct D {D:D'}

adversarial A {
in bla()
}

functionality Q implements D A {

  initial state Is 
  {
   match message with
    * => {fail.}
   end
  }
}
