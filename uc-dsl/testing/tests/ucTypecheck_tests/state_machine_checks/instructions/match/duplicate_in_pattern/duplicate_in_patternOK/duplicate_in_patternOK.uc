ec_requires +IntPair.

direct D' {
in  x@bla()
out bli()@x
}

direct D {D:D'}

functionality F implements D {

 party P serves D.D {

  initial state I {
   match message with
     x@D.D.bla => {
		match IntPair 0 0 with 
		| IntPair i j => { if (i < j) { fail. } else { fail.} }
		end
     }
   end
  }
 }
}
