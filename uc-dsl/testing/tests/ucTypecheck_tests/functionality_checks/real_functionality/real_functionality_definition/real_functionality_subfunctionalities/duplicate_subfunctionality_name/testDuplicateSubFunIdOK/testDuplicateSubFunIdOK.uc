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

functionality R() implements D {

subfun SF1=Q
subfun SF2=Q

 party P serves D.D {
  initial state Isus 
  {
   match message with
    * => {fail.}
   end
  }
 }

}
