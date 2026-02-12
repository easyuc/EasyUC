direct D' {
in x@bla()
in x@blb()
out bli()@x
out blj()@x
}

direct D {D:D'}

adversarial A' {
in  bla()
in  blb()
out bli()
}

functionality F() implements D A'{

  initial state Is 
  {
   match message with
    *  => {fail.}
   end
  }
}
