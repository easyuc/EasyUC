direct D' {
  in  x@bla()
  out bli()@x
}

direct D {D:D'}

functionality F implements D {

 party P serves D.D {

  initial state I {
   var a : int; var b : bool;
   match message with
     x@D.D.bla => {
		match [] with 
		| []      => { fail. }
		| x :: xs => {
                    if (true) {
                      b <- x; fail.
                    }
                    else {
                      b <- x; fail.
                    }
                  }
		end
     }
   end
  }
 }
}
