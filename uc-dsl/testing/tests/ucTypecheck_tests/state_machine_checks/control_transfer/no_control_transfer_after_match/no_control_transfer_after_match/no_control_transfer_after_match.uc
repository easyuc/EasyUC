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
           match Some 0 with 
           | Some i => {}
           | None   => {}
           end
    }
   end
  }
 }
}
