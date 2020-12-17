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
		match Some 0 with 
		| Sime i => {fail.}
		| None   => {fail.} 
		end
     }
   end
  }
 }
}
