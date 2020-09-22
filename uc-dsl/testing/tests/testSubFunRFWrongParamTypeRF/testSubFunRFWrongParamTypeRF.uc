direct a {
in x@bla()
}

direct A {a:a}

direct d {
in x@bli()
}

direct D {d:d}


functionality E() implements A {

 party P serves a {
  initial state Isus 
  {
   match message with
    othermsg => {fail.}
   end
  }
 }
}

functionality S(X:D) implements A {
 party P serves a {
  initial state Isus 
  {
   match message with
    othermsg => {fail.}
   end
  }
 }

}

functionality R() implements A {

 subfun Q=E()
 subfun SF=S(Q)

 party P serves a {
  initial state Isus 
  {
   match message with
    othermsg => {fail.}
   end
  }
 }

}
