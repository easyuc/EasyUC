direct D' {
in  x@bla
out bli(k:int, a:bool)@x
}

direct D {D:D'}

functionality F() implements D {

 party P serves D.D {

  initial state I {
   match message with
     x@D.D.bla => {send D.D.bli(3, false)@x and transition J.}
   end
  }

  state J { match message with * => { fail. } end }
 }
}
