direct D_ {
in x@bla()
out bli()@x
}

direct D {D:D_}

functionality F(P:D) implements D {

party Y serves D.D {
  initial state Is 
  {
   match message with
     P.D.bla => {fail.}
   | * => {fail.}
   end
  }
}
 
}

