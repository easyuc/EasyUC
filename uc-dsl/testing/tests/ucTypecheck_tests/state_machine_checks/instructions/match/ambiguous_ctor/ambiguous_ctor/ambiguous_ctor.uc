ec_requires +Ambi1 +Ambi2.

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
		match Ambi1.Ambi with 
		| Ambi => {fail.} 
		end
     }
   end
  }
 }
}
