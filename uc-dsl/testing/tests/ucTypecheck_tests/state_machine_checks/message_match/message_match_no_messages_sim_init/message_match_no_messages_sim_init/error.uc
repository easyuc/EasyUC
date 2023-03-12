adversarial A1 {
  out foo
}

adversarial A {
  A1 : A1
}

direct E{
in x@bla()
}

direct D {
Subio:E
Subio3:E
}

functionality RF() implements D A {
  party P1 serves D.Subio A.A1 {
    initial state IS {
      match message with
        * => { fail. }
      end
    }
  }

  party P2 serves D.Subio3 {
    initial state IS {
      match message with
        * => { fail. }
      end
    }
  }
}

adversarial I2Sim {
  in foo
}

simulator Sim uses I2Sim simulates RF {
  initial state IS {
    match message with
      * => { fail. }
    end
  }
}
