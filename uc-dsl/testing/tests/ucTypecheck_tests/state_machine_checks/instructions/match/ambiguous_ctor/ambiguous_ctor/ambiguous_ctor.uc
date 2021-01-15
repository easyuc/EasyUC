ec_requires +Ambi1 +Ambi2.

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
		match Ambi1.Ambi with 
		| Ambi => {fail.} 
		end
     }
   end
  }
 }
}
