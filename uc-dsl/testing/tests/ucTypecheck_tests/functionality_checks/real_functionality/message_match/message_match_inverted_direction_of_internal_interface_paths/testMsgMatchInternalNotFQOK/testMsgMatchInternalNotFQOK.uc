uc_requires X.
uc_clone X.

direct D' {
in x@bla()
out bli()@x
}

direct D {D:D'}

functionality F(P:X.D) implements D {

party Y serves D.D {
  initial state Is 
  {
   match message with
     P.D.bli => {fail.}
   | * => {fail.}
   end
  }
}
 
}

