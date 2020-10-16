direct d {
in  x@bla(u:univ)
out bli()@x
}

direct D {D:d}
functionality F(G:D) implements D {

 party P serves D.D {

  initial state I {
   match message with
     pt@D.D.bla(u) => {
		decode u as int with
                  ok x =>{fail.}
		| error=>{fail.}
		end
	      }
   | * => {fail.}
   end
  }
 }
}
