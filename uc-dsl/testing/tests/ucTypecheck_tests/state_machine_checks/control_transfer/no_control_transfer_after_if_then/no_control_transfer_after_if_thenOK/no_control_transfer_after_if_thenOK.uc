direct D' {
in  x@bla()
out bli()@x
}

direct D {D:D'}

functionality F implements D {

 party P serves D.D {

  initial state I {
   match message with
     y@D.D.bla => {
            if (true) {fail.}
            else {fail.}
     }
   end
  }
 }
}
