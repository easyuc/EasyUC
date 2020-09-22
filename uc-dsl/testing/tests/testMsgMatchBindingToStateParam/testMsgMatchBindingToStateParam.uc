direct d {
in x@bla(u:univ)
out bli()@x
}

direct D {D:d}

adversarial a {
in  bla()
out bli()
}

adversarial A {A:a}



functionality S() implements D A {

 party P serves D.D A.A {
  initial state Is 
  {
   match message with
    * => {fail.}
   end
  }

  state S(p:port)
  {
   match message with
     p@D.D.bla(p)  => {fail.}
   | * => {fail.}
   end
  }

 }
}

