(* UcState module *)

(* Global State of UC DSL tool *)

open Batteries

let include_dirs_ref : string list ref = ref []

let get_include_dirs () = ! include_dirs_ref

let set_include_dirs x = include_dirs_ref := x

let add_highest_include_dirs x =
  let dirs = List.remove (!include_dirs_ref) x in
  include_dirs_ref := x :: dirs

let add_lowest_include_dirs x =
  let dirs = List.remove (!include_dirs_ref) x in
  include_dirs_ref := dirs @ [x]

let raw_messages : bool ref = ref false

let set_raw_messages () = raw_messages := true

let unset_raw_messages () = raw_messages := true

let get_raw_messages () = ! raw_messages

let pg_mode : bool ref = ref false

let set_pg_mode () = pg_mode := true

let unset_pg_mode () = pg_mode := false

let get_pg_mode () = ! pg_mode

let pg_start_pos : int ref = ref 0

let set_pg_start_pos p  = pg_start_pos := p

let get_pg_start_pos () = ! pg_start_pos

let batch_mode : bool ref = ref false

let set_batch_mode () = batch_mode := true

let get_batch_mode () = ! batch_mode

let debugging : bool ref = ref false

let set_debugging () = debugging := true

let unset_debugging () = debugging := false

let get_debugging () = ! debugging

let run_print_pos : bool ref = ref false

let set_run_print_pos () = run_print_pos := true

let unset_run_print_pos () = run_print_pos := false

let get_run_print_pos () = ! run_print_pos

let units : bool ref = ref false

let set_units () = units := true

let get_units () = ! units
