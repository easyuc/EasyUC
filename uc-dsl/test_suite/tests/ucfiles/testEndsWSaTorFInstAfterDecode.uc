direct d {
in  x@bla(u:univ)
out bli()@x
}

direct D {D:d}
functionality F(G:D) implements D {

 party P serves D {

  initial state I {
   match message with
     bla(u) => {
		decode u as int with
                  ok x =>{fail.}
		| error=>{fail.}
		end
		fail.
	      }
   | othermsg => {fail.}
   end
  }
 }
}
