direct D' {
  in x@bla()
  out bli()@x
}

direct D {D1:D' D2:D'}

adversarial I {
  in  bla()
  out bli()
}

adversarial I' {
  in  bla()
  out bli()
}

adversarial A {D1:I D2:I'}

functionality IF() implements D I {
  initial state Is 
  {
   match message with
     * => {fail.}
   end
  }
}

functionality RF() implements D A {
 party P1 serves D.D1 A.D2 {
  initial state Is {
    match message with * => {fail.} end
  }
 }
 party P2 serves D.D2 A.D1 {
  initial state Is {
    match message with * => {fail.} end
  }
 }
}

simulator S uses I simulates RF() {
  initial state Is {
    match message with I.* => {fail.} end
  }
}

