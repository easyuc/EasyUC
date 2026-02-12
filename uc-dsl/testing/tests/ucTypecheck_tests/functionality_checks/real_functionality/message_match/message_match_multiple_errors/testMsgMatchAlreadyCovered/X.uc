direct D' {
in x@bla()
out bli()@x
}

direct D {D:D'}

adversarial A' {
in  bla()
out bli()
}

functionality F implements D A' {
  initial state Is 
  {
   match message with
    * => {fail.}
   end
  }
}

