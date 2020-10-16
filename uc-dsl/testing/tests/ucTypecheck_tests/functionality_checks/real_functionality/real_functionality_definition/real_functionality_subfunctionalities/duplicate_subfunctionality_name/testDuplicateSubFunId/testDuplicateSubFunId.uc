direct d {
in x@bla()
}

direct D {D:d}

adversarial a {
in bla()
}

functionality Q implements D a {

  initial state Is 
  {
   match message with
    * => {fail.}
   end
  }
 
}

functionality R() implements D {

subfun SF=Q
subfun SF=Q

 party P serves D.D {
  initial state Isus 
  {
   match message with
    * => {fail.}
   end
  }
 }

}
