(* UcState module *)

(* Global state of UC DSL tool *)

let include_dirs_ref : string list ref = ref []

let get_include_dirs() = ! include_dirs_ref

let set_include_dirs x = include_dirs_ref := x

let raw_messages : bool ref = ref false

let set_raw_messages () = raw_messages := true

let get_raw_messages () = ! raw_messages
