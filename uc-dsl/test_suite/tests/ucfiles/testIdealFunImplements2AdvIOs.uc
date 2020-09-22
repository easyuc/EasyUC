adversarial D {
in  bla()
out bli()
}

adversarial I {
in  bla()
out bli()
}

functionality S() implements D I {

  initial state Is 
  {
   match message with
     othermsg => {fail.}
   end
  }
 
}

