(* Composition Theorem Definitions and Proofs *)

require import UCCore UCListAux.

abstract theory CompRF.

(* begin theory parameters *)

op rf_info : rf_info.

axiom rf_info_valid : rf_info_valid rf_info.

op change_pari : int.  (* parameter being changed from real to ideal *)

axiom change_pari_valid : 1 <= change_pari <= rf_info.`rfi_num_params.

(* end theory parameters *)

module MakeRFComp (Rest : FUNC, Par : FUNC) : FUNC = {
  var self : addr

  proc init(_self : addr) : unit = {
    self <- _self;
    Rest.init(_self);
    Par.init(_self ++ [change_pari]);
  }

  (* the same as after_core from MakeRF: *)

  proc after_core_or_par(r : msg option, orig_dest_addr)
         : msg option * msg * bool = {
    var m : msg <- witness; var pari : int;
    var not_done <- true;
    if (r = None) {
      not_done <- false;
    }
    else {
      m <- oget r;  (* next iteration, if any, will use m *)
      if (m.`3.`1 <> orig_dest_addr) {
        not_done <- false; r <- None;
      }
      elif (m.`1 = Dir) {
        if (m.`3.`1 = self) {
          if (envport self m.`2) {
            not_done <- false;
          }
          elif (! (addr_eq_param rf_info self m.`2.`1 \/
                   addr_eq_subfun rf_info self m.`2.`1)) {
            not_done <- false; r <- None;
          }
        }
        elif (addr_eq_param rf_info self m.`3.`1 \/
              addr_eq_subfun rf_info self m.`3.`1) {
          if (m.`2.`1 <> self) {
            not_done <- false; r <- None;
          }
        }
        else {  (* should not happen *)
          not_done <- false; r <- None;
        }
      }
      else {  (* m.`1 = Adv *)
        not_done <- false;
        if (m.`2.`1 <> adv) {
          r <- None;
        }
        elif (m.`3.`1 = self \/
              addr_eq_subfun rf_info self m.`3.`1) {
          if (! rf_info.`rfi_adv_pi_begin + 1 <= m.`2.`2 <=
                rf_info.`rfi_adv_pi_main_end) {
            r <- None;
          }
        }
        elif (addr_ge_param rf_info self m.`3.`1) {
          pari <- head_of_drop_size_first 0 self m.`3.`1;
          if (! (nth1_adv_pi_begin_params rf_info pari < m.`2.`2 <=
                 nth1_adv_pi_end_params rf_info pari)) {
            r <- None;
          }
        }
        else {  (* should not happen *)
          r <- None;
        }
      }
    }          
    return (r, m, not_done);
  }

  proc loop(m : msg) : msg option = {
    var r : msg option <- None;
    var not_done : bool <- true;
    while (not_done) {
      if (self ++ [change_pari] <= m.`2.`1) {
        r <@ Par.invoke(m);
      }
      else {
        r <@ Rest.invoke(m);
      }
      (r, m, not_done) <@ after_core_or_par(r, m.`2.`1);
    }
    return r;
  }

  proc invoke(m : msg) : msg option = {
    var r : msg option <- None;
    (* we can assume m.`3.`1 is not >= self *)
    if ((m.`1 = Dir /\ m.`2.`1 = self) \/
        (m.`1 = Adv /\
         (m.`2.`1 = self \/
          addr_ge_param rf_info self m.`2.`1 \/
          addr_eq_subfun rf_info self m.`2.`1))) {
      r <@ loop(m);
    }
    return r;
  }
}.

end CompRF.
