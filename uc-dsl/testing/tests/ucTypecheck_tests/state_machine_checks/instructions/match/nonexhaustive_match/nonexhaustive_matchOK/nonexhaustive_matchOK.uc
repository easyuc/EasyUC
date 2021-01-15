ec_requires +OneTwo.

direct D_ {
in  x@bla()
out bli()@x
}

direct D {D:D_}

functionality F implements D {

 party P serves D.D {

  initial state I {
   match message with
     * => {
		match One with 
		| One => {fail.} 
		| Two => {fail.} 
		end
     }
   end
  }
 }
}
