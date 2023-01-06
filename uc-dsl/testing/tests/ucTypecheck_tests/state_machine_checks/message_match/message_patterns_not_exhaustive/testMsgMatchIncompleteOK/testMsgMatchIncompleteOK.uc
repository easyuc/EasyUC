direct D' {
in x@bla()
out bli()@x
}

direct D {D:D'}

adversarial I {
in  bla()
in  blb()
out bli()
}

functionality S() implements D I {

  initial state Ini
  {
    match message with
    | x@D.D.bla => {fail.}
    end
  }

  state Other
  {
   match message with
    p@D.D.bla => {fail.}
   | I.bla => {fail.}
   | * => {fail.}
   end
  }
 
}
