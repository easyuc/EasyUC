direct a {
in x@bla()
}

direct A {a:a}

direct d {
in x@bli()
}

direct D {d:d}

functionality S(X:D) implements A  {
 party P serves a {
  initial state Isus 
  {
   match message with
    othermsg => {fail.}
   end
  }
 }
}

functionality R(Q:A) implements A  {

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
