direct X { in pt@hi out bye@pt }
direct XX {X : X}

adversarial Y { in bye out hi }

functionality SF implements XX Y {
  initial state IS {
    match message with
      pt@XX.X.hi => { send Y.hi and transition NS(pt). }
    end
  }

  state NS(pt : port) {
    match message with
      Y.bye => { send XX.X.bye@pt and transition NS(pt). }
    | *     => { fail. }
    end
  }
}

adversarial B {
in bla()
}

adversarial A {
Subio:B
}

direct E{
in x@bla()
}

direct D {
Subio:E
Subio3:E
}

functionality S() implements D A {
 subfun SF = SF

 party P1 serves D.Subio {
  initial state Is 
  {
   match message with
    * => {fail.}
   end
  }
 }

 party P2 serves A.Subio {
  initial state Is 
  {
   match message with
     SF.X.bye => { fail. }
   end
  }
 }

 party P3 serves D.Subio3 {
  initial state Is 
  {
   match message with
    * => {fail.}
   end
  }
 }

}
