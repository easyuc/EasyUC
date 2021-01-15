ec_requires +IntPair.

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
		match IntPair 0 0 with 
		| IntPair i j => {fail.}
		end
     }
   end
  }
 }
}
