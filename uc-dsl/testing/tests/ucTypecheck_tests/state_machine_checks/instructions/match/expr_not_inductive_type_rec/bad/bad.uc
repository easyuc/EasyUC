ec_requires +Foo.

direct D' {
  in  x@bla()
  out bli()@x
}

direct D {D:D'}

functionality F implements D {

 party P serves D.D {

  initial state I {
   match message with
     x@D.D.bla => {
       match t_val with 
       | A => { fail. }
       end
     }
   end
  }
 }
}
