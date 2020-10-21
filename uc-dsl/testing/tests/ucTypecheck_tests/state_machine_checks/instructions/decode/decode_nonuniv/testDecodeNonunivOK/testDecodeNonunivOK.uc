ec_requires KeysExponentsAndPlainTexts.

direct a {
in  x@bla(u:univ)
out bli()@x
}

direct A {a:a}

functionality F() implements A {

 party P serves A.a {

  initial state I {
   match message with
    pt@A.a.bla(k) => { 
                decode k as key with
                  ok x =>{fail.}
                | error=>{fail.}
                end
              }
   end
  }
 }
}
