direct d {
in x@bla()
out bli()@x
}

direct D {D:d}

adversarial I {
in  bla()
in  blb()
out bli()
}

functionality S() implements D I {

  initial state Is 
  {
   match message with
     p@D.D.bla => {fail.}
   | I.bla => {fail.}
   | *  => {fail.}
   end
  }
 
}

