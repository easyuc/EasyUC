direct D_ {
in x@bla()
out bli()@x
}

direct D {D:D_}

adversarial I {
in  bla()
out bli()
}

adversarial J {
in  bla()
out bli()
}

functionality IF() implements D I {

  initial state Is 
  {
   match message with
     * => {fail.}
   end
  }
 
}

functionality RF() implements D {

 party P serves D.D {

  initial state Is {
  match message with * => {fail.} end
  }
 }
}

simulator S uses J simulates RF() {

  initial state Is {
  match message with J.* => {fail.} end
  }

}

