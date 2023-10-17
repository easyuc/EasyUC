direct DirBas {
  in pt@req
  out rsp@pt
}

direct Dir {
  Pt1 : DirBas
  Pt2 : DirBas
}

adversarial AdvBas {
  in pong
  out ping
}

adversarial Adv {
  Pt1 : AdvBas
}

functionality Real implements Dir Adv {
  party Pt1 serves Dir.Pt1 Adv.Pt1 {
    initial state Init {
      match message with
      | pt@Dir.Pt1.req => {
          send Adv.Pt1.ping and transition Final.
        }
      end
    }

    state Final {
      match message with
      | * => { fail. }
      end
    }
  }

  party Pt2 serves Dir.Pt2 {
    initial state Init {
      match message with
      | pt@Dir.Pt2.req => {
          send Dir.Pt2.rsp@pt and transition Final.
        }
      end
    }

    state Final {
      match message with
      | * => { fail. }
      end
    }
  }
}
 
      

