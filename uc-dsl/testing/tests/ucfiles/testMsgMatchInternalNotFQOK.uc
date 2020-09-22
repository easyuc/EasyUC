direct d {
in x@bla()
out bli()@x
}

direct D {D:d}

functionality F(P:D) implements D {

party Y serves D {
  initial state Is 
  {
   match message with
     P.D.bli => {fail.}
   | othermsg => {fail.}
   end
  }
}
 
}

