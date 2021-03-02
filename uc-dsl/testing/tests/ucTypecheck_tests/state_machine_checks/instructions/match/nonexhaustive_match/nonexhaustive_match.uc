ec_requires +OneTwo.

direct D' {
in  x@bla()
out bli()@x
}

direct D {D:D'}

functionality F implements D {

 party P serves D.D {

  initial state I {
   match message with
     * => {
		match One with 
		| One => {fail.} 
		end
     }
   end
  }
 }
}
