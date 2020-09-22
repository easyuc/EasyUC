direct d {
in x@bla()
out bli()@x
}

direct D {D:d}

adversarial I {
in  bla()
out bli()
}

functionality S() implements D I {

  initial state Is 
  {
   match message with
   | D.D.* => {fail.}
   | I.* => {fail.}
   end
  }
 
}

