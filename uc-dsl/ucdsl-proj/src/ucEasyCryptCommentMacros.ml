(* UCEasyCryptCommentMacros module *)

open Batteries
open BatIO

exception ECComMacs_NonterminatedComment of int
exception ECComMacs_UnmatchedClose       of int
exception ECComMacs_ScanError            of int

exception ECComMacs_Error of string

let input_char_opt (inp : input) : char option =
  try Some (input_char inp) with
  | End_of_file -> None

let input_char_eof_error (lnum : int) (inp : input) : char =
  match input_char_opt inp with
  | None   -> raise (ECComMacs_ScanError lnum)
  | Some c -> c

let scan_ident_opt (inp : input) (lnum : int) (c : char)
      : int * string option * char option =
  let rec scan_init lnum c =
    if c = '\n'
      then match input_char_opt inp with
           | None   -> (lnum + 1, None, None)
           | Some c -> scan_init (lnum + 1) c
    else if Char.is_whitespace c
      then match input_char_opt inp with
           | None   -> (lnum, None, None)
           | Some c -> scan_init lnum c
    else if Char.is_letter c
      then match input_char_opt inp with
           | None   -> (lnum, Some (String.of_char c), None)
           | Some d -> scan_rest lnum [c] d
    else (lnum, None, Some c)
  and scan_rest lnum cs c =
    if Char.is_letter c || Char.is_digit c
    then match input_char_opt inp with
         | None   -> (lnum, Some (String.of_list (cs @ [c])), None)
         | Some d -> scan_rest lnum (cs @ [c]) d
    else (lnum, Some (String.of_list cs), Some c) in
  scan_init lnum c

let scan_idents (inp : input) (lnum : int) (c : char)
      : int * string list * char option =
  let rec scan_first_opt lnum c =
    match scan_ident_opt inp lnum c with
    | (lnum, None,    cOpt)   -> (lnum, [], cOpt)
    | (lnum, Some id, None)   -> (lnum, [id], None)
    | (lnum, Some id, Some c) -> scan_comma_or_done lnum [id] c
  and scan_next lnum ids c =
    match scan_ident_opt inp lnum c with
    | (lnum, Some id, None)   -> (lnum, ids @ [id], None)
    | (lnum, Some id, Some c) -> scan_comma_or_done lnum (ids @ [id]) c
    | _                       -> raise (ECComMacs_ScanError lnum)
  and scan_comma_or_done lnum ids c =
    if c = '\n'
      then match input_char_opt inp with
           | None   -> (lnum + 1, ids, None)
           | Some c -> scan_comma_or_done (lnum + 1) ids c
    else if Char.is_whitespace c
      then match input_char_opt inp with
           | None   -> (lnum, ids, None)
           | Some c -> scan_comma_or_done lnum ids c
    else if c = ','
      then scan_next lnum ids (input_char_eof_error lnum inp)
    else (lnum, ids, Some c) in
  scan_first_opt lnum c

let scan_name_and_params (inp : input) (lnum : int) (c : char)
      : int * string * string list * char option =
  let rec scan_open_par lnum name c =
    if c = '\n'
      then scan_open_par (lnum + 1) name (input_char_eof_error lnum inp)
    else if Char.is_whitespace c
      then scan_open_par lnum name (input_char_eof_error lnum inp)
    else if c = '('
      then match scan_idents inp lnum (input_char_eof_error lnum inp) with
           | (lnum, pars, Some c) -> scan_close_par lnum name pars c
           | (lnum, _,    None)   -> raise (ECComMacs_ScanError lnum)
    else raise (ECComMacs_ScanError lnum)
  and scan_close_par lnum name params c =
    if c = '\n'
      then scan_close_par (lnum + 1) name params (input_char_eof_error lnum inp)
    else if Char.is_whitespace c
      then scan_close_par lnum name params (input_char_eof_error lnum inp)
    else if c = ')'
      then (lnum, name, params, input_char_opt inp)
    else raise (ECComMacs_ScanError lnum) in
  match scan_ident_opt inp lnum c with
  | (lnum, Some name, Some c) -> scan_open_par lnum name c
  | (lnum, _,         _)      -> raise (ECComMacs_ScanError lnum)

type macro = {
  name   : string;
  params : string list;
  body   : string
}

type macros = macro list

let macro_empty_body (name : string) (params : string list) : macro =
  {name = name; params = params; body = ""}

let trim_macro_body (mac : macro) : macro =
  {mac with body = String.trim mac.body}

let add_char_to_macro_body (mac : macro) (c : char) : macro =
  {mac with body = mac.body ^ String.of_char c}

let add_string_to_macro_body (mac : macro) (s : string) : macro =
  {mac with body = mac.body ^ s}

let add_char_to_opt_macro_body (mac_opt : macro option) (c : char)
      : macro option =
  match mac_opt with
  | None     -> None
  | Some mac -> Some {mac with body = mac.body ^ String.of_char c}

let add_string_to_opt_macro_body (mac_opt : macro option) (s : string)
      : macro option =
  match mac_opt with
  | None     -> None
  | Some mac -> Some {mac with body = mac.body ^ s}

(* lnum >= 1, nest >= 0, if mac_opt <> None, then nest > 0 *)

let rec scan_init (inp : input) (lnum : int) (nest : int)
    (macs : macro list) (mac_opt : macro option) (c : char) : macro list =
  if c = '\n'
    then match input_char_opt inp with
         | None   ->
             if nest = 0
             then macs
             else raise (ECComMacs_NonterminatedComment (lnum + 1))
         | Some c ->
             scan_init inp (lnum + 1) nest macs
             (add_char_to_opt_macro_body mac_opt '\n') c
  else if c = '('
    then match input_char_opt inp with
         | None   ->
             if nest = 0
             then macs
             else raise (ECComMacs_NonterminatedComment lnum)
         | Some c ->
             scan_from_open inp lnum nest macs
             (add_char_to_opt_macro_body mac_opt '(') c
  else if c = '*'
    then match input_char_opt inp with
         | None   ->
             if nest = 0
             then macs
             else raise (ECComMacs_NonterminatedComment lnum)
         | Some c -> scan_from_star inp lnum nest macs mac_opt c
  else match input_char_opt inp with
       | None   ->
           if nest = 0
           then macs
           else raise (ECComMacs_NonterminatedComment lnum)
       | Some d ->
           scan_init inp lnum nest macs
           (add_char_to_opt_macro_body mac_opt c) d
and scan_from_open (inp : input) (lnum : int) (nest : int)
    (macs : macro list) (mac_opt : macro option) (c : char) : macro list =
  if c = '\n'
    then match input_char_opt inp with
         | None   ->
             if nest = 0
             then macs
             else raise (ECComMacs_NonterminatedComment (lnum + 1))
         | Some c ->
             scan_init inp (lnum + 1) nest macs
             (add_char_to_opt_macro_body mac_opt '\n') c
  else if c = '*'
    then match input_char_opt inp with
         | None   -> raise (ECComMacs_NonterminatedComment lnum)
         | Some c ->
             scan_from_open_star inp lnum (nest + 1) macs
             (add_char_to_opt_macro_body mac_opt '*') c
  else if c = '('
    then match input_char_opt inp with
         | None   ->
             if nest = 0
             then macs
             else raise (ECComMacs_NonterminatedComment lnum)
         | Some c ->
             scan_from_open inp lnum nest macs
             (add_char_to_opt_macro_body mac_opt '(') c
  else match input_char_opt inp with
       | None   ->
           if nest = 0
           then macs
           else raise (ECComMacs_NonterminatedComment lnum)
       | Some d ->
           scan_init inp lnum nest macs
           (add_char_to_opt_macro_body mac_opt c) d
and scan_from_open_star (inp : input) (lnum : int) (nest : int)
    (macs : macro list) (mac_opt : macro option) (c : char) : macro list =
  if c = '\n'
    then match input_char_opt inp with
         | None   -> raise (ECComMacs_NonterminatedComment (lnum + 1))
         | Some c ->
             scan_init inp (lnum + 1) nest macs
             (add_char_to_opt_macro_body mac_opt '\n') c
  else if c = '!'
    then if nest = 1
         then match input_char_opt inp with
              | None   -> raise (ECComMacs_NonterminatedComment lnum)
              | Some c ->
                  match scan_name_and_params inp lnum c with
                  | (lnum, name, params, Some c) ->
                      scan_init inp lnum nest macs
                      (Some (macro_empty_body name params)) c
                  | (lnum, _,    _,      None)   ->
                      raise (ECComMacs_NonterminatedComment lnum)
         else match input_char_opt inp with  (* nest >= 2 *)
              | None   -> raise (ECComMacs_NonterminatedComment lnum)
              | Some c ->
                  scan_init inp lnum nest macs
                  (add_string_to_opt_macro_body mac_opt "!") c
  else match input_char_opt inp with
       | None   -> macs
       | Some d ->
           scan_init inp lnum nest macs
           (add_char_to_opt_macro_body mac_opt c) d
and scan_from_star (inp : input) (lnum : int) (nest : int)
    (macs : macro list) (mac_opt : macro option) (c : char) : macro list =
  if c = '\n'
    then match input_char_opt inp with
         | None   ->
             if nest = 0
             then macs
             else raise (ECComMacs_NonterminatedComment (lnum + 1))
         | Some c ->
             scan_init inp (lnum + 1) nest macs
             (add_string_to_opt_macro_body mac_opt "*\n") c
  else if c = ')'
    then if nest = 1 && Option.is_some mac_opt
           then match input_char_opt inp with
                | None   -> (macs @ [trim_macro_body (Option.get mac_opt)])
                | Some c ->
                    scan_init inp lnum 0
                    (macs @ [trim_macro_body (Option.get mac_opt)])
                    None c
         else if nest >= 1
           then match input_char_opt inp with
                | None   ->
                    if nest = 1
                    then macs
                    else raise (ECComMacs_NonterminatedComment lnum)
                | Some c ->
                    scan_init inp lnum (nest - 1) macs
                    (add_string_to_opt_macro_body mac_opt "*)") c
         else raise (ECComMacs_UnmatchedClose lnum)
  else match input_char_opt inp with
       | None   ->
           if nest = 0
           then macs
           else raise (ECComMacs_NonterminatedComment lnum)
       | Some d ->
           scan_init inp lnum nest macs
           (add_string_to_opt_macro_body mac_opt ("*" ^ String.of_char c)) d

let scan_file (filename : string) : macro list =
  let inp = File.open_in filename in
  match input_char_opt inp with
  | None   -> []
  | Some c -> scan_init inp 1 0 [] None c

let rec has_dups (xs : string list) : bool =
  match xs with
  | []      -> false
  | x :: xs -> List.mem x xs || has_dups xs

let rec find_dup (xs : string list) : string option =
  match xs with
  | []      -> None
  | x :: xs -> if List.mem x xs then Some x else find_dup xs

let check_macro (mac : macro) : unit =
  if has_dups mac.params
  then let msg =
         Printf.sprintf "comment macro %s has duplicate parameter name"
         mac.name in
       raise (ECComMacs_Error msg)

let check_macros (macs : macro list) : unit =
  let names = List.map (fun macro -> macro.name) macs in
  let () =
    match find_dup names with
    | None      -> ()
    | Some name ->
        let msg =
          Printf.sprintf "multiple comment macros have the same name: %s"
          name in
        raise (ECComMacs_Error msg) in
  List.iter check_macro macs

let scan_and_check_file (filename : string) : macro list =
  let macros = scan_file filename in
  check_macros macros; macros

let has_name (macs : macro list) (name : string) : bool =
  List.exists (fun mac -> mac.name = name) macs

let make_var (var : string) : string = "<<" ^ var ^ ">>"

let apply_macro (macs : macro list) (name : string) (args : string list)
      : string =
  match List.find_opt (fun mac -> mac.name = name) macs with
  | None     ->
      raise (ECComMacs_Error (Printf.sprintf "undefined macro: %s" name))
  | Some mac ->
    if List.length args <> List.length mac.params
    then let msg =
           Printf.sprintf "wrong number of arguments for comment macro: %s"
           mac.name in
         raise (ECComMacs_Error msg)
    else let subs = List.combine mac.params args in
         List.fold_left
         (fun body (param, arg) ->
            String.nreplace ~str:body ~sub:(make_var param) ~by:arg)
         (mac.body) subs

(* start for testing *)

let print_macro (mac : macro) : unit =
  Printf.printf "name: %s; params: %s\n\nbody:\n---\n%s\n---\n\n"
  mac.name (String.concat ", " mac.params) mac.body

let print_macros (macs : macro list) : unit =
  List.iter print_macro macs

let test_scan_and_check (filename : string) : unit =
  try print_macros (scan_and_check_file filename) with
  | ECComMacs_ScanError lnum            ->
      (Printf.printf "error scanning file at line %d\n" lnum; exit 1)
  | ECComMacs_NonterminatedComment lnum ->
      (Printf.printf "nonterminated comment at line %d\n" lnum; exit 1)
  | ECComMacs_UnmatchedClose lnum       ->
      (Printf.printf "unmatched close comment at line %d\n" lnum; exit 1)
  | ECComMacs_Error s                   ->
      (Printf.printf "error: %s\n" s; exit 1)
  | Sys_error _                         ->
      (Printf.printf "unable to open file: %s\n" filename)

let test_subst (filename : string) (name : string)
    (args : string list) : unit =
  try let macs = scan_and_check_file filename in
      Printf.printf "args: %s\nresult:\n---\n%s\n---\n"
      (String.concat ", " args)
      (apply_macro macs name args) with
  | ECComMacs_ScanError lnum            ->
      (Printf.printf "error scanning file at line %d\n" lnum; exit 1)
  | ECComMacs_NonterminatedComment lnum ->
      (Printf.printf "nonterminated comment at line %d\n" lnum; exit 1)
  | ECComMacs_UnmatchedClose lnum       ->
      (Printf.printf "unmatched close comment at line %d\n" lnum; exit 1)
  | ECComMacs_Error s                   ->
      (Printf.printf "error: %s\n" s; exit 1)
  | Sys_error _                         ->
      (Printf.printf "unable to open file: %s\n" filename)

(* end for testing *)
