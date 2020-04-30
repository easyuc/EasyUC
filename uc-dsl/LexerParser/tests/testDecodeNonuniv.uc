requires KeysExponentsAndPlainTexts.

direct a {
in  x@bla(k:key)
out bli()@x
}

direct A {A:a}

functionality F() implements A {

 party P serves A {

  initial state I {
   match message with
    bla(k) => {	decode k as key with
		  ok x =>{fail.}
		| error=>{fail.}
		end
	      }
   |othermsg => {fail.}
   end
  }
 }
}
