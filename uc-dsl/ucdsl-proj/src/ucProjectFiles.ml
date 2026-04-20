(* UcProjectFiles module *)

open Batteries
open BatIO

open UcMessage

exception ScanError of int

type binding =
  | BString of string * string
  | BInt    of string * int
  | BBool   of string * bool

(* letters and digits, beginning with a letter *)

let is_ident (s : string) : bool =
  match String.to_list s with
  | []      -> false
  | c :: cs ->
      Char.is_letter c &&
      List.for_all
      (fun d -> Char.is_letter d || Char.is_digit d)
      cs

let is_numeral (s : string) : bool =
  try ignore (String.to_int s); true with
  | _ -> false

let is_bool_string (s : string) : bool =
  List.mem s ["true"; "false"]

let bool_string_to_bool (s : string) : bool =
  match s with
  | "true"  -> true
  | "false" -> false
  | _       -> failure "cannot happen"

let valid_field_char (c : char) : bool =
  Char.is_letter c || Char.is_digit c || c = '_' || c = '.' ||
  c = '-' || c = '/' || c = '#'

let input_char_opt (inp : input) : char option =
  try Some (input_char inp) with
  | End_of_file -> None

let rec scan_ignore_to_eol_or_eof (inp : input) (lnum : int) (c : char)
        : (int * char option) =
    if c = '\n'
    then (lnum + 1, input_char_opt inp)
    else match input_char_opt inp with
         | None   -> (lnum, None)
         | Some c -> scan_ignore_to_eol_or_eof inp lnum c

let scan_field_opt (inp : input) (lnum : int) (c : char)
      : int * string option * char option =
  let rec scan_rest lnum cs c =
    if valid_field_char c
    then match input_char_opt inp with
         | None   -> (lnum, Some (String.of_list (cs @ [c])), None)
         | Some d -> scan_rest lnum (cs @ [c]) d
    else (lnum, Some (String.of_list cs), Some c) in
  let rec scan_init lnum c =
    if c = '\n' then
      match input_char_opt inp with
      | None   -> (lnum + 1, None, None)
      | Some c -> scan_init (lnum + 1) c
    else if Char.is_whitespace c
      then match input_char_opt inp with
           | None   -> (lnum, None, None)
           | Some c -> scan_init lnum c
    else if c = '#'  (* comment to eol/eof *)
      then match input_char_opt inp with
           | None   -> (lnum, None, None)
           | Some c ->
               match scan_ignore_to_eol_or_eof inp lnum c with
               | (lnum, None)   -> (lnum, None, None)
               | (lnum, Some c) -> scan_init lnum c
    else if valid_field_char c
      then match input_char_opt inp with
           | None   -> (lnum, Some (String.of_char c), None)
           | Some d -> scan_rest lnum [c] d
    else (lnum, None, Some c) in
  scan_init lnum c

let scan_field_same_line (inp : input) (lnum : int) (c : char)
      : int * string * char option =
  let rec scan_rest cs c =
    if valid_field_char c
    then match input_char_opt inp with
         | None   -> (lnum, String.of_list (cs @ [c]), None)
         | Some d -> scan_rest (cs @ [c]) d
    else (lnum, String.of_list cs, Some c) in
  let rec scan_init c =
    if c = '\n' then raise (ScanError lnum)
    else if Char.is_whitespace c
      then match input_char_opt inp with
           | None   -> raise (ScanError lnum)
           | Some c -> scan_init c
    else if valid_field_char c
      then match input_char_opt inp with
           | None   -> (lnum, String.of_char c, None)
           | Some d -> scan_rest [c] d
    else raise (ScanError lnum) in
  scan_init c

let scan_equals_same_line_look_ahead (inp : input) (lnum : int) (c : char)
      : int * char =
  let rec scan c =
    if c = '\n'
      then raise (ScanError lnum)
    else if Char.is_whitespace c
      then match input_char_opt inp with
           | None   -> raise (ScanError lnum)
           | Some c -> scan c
    else if c = '='
      then match input_char_opt inp with
           | None   -> raise (ScanError lnum)
           | Some d -> (lnum, d)
    else raise (ScanError lnum) in
  scan c

let scan_binding_opt (file : string) (inp : input) (lnum : int) (c : char)
      : int * binding option * char option =
  match scan_field_opt inp lnum c with
  | (lnum, Some x, Some c) ->
      (let (lnum, c) = scan_equals_same_line_look_ahead inp lnum c in
       let (lnum, y, c_opt) = scan_field_same_line inp lnum c in
       if (not (is_ident x))
         then non_loc_error_message
              (fun ppf ->
                 Format.fprintf ppf
                 ("@[on@ line@ %d@ of@ file@ %s@, bad@ " ^^
                  "identifier:@ %s@]")
                 lnum file x)
       else if is_numeral y
         then (lnum, Some (BInt (x, String.to_int y)), c_opt)
       else if is_bool_string y
         then (lnum, Some (BBool (x, bool_string_to_bool y)), c_opt)
       else (lnum, Some (BString (x, y)), c_opt))
  | (lnum, Some _, None)   -> raise (ScanError lnum)
  | (lnum, None, c_opt)    -> (lnum, None, c_opt)

let scan_bindings (file : string) (inp : input) (lnum : int) (c : char)
      : binding list =
  let rec scan lnum bndgs c =
    match scan_binding_opt file inp lnum c with
    | (_,    Some bnd, None)   -> bndgs @ [bnd]
    | (lnum, Some bnd, Some c) -> scan lnum (bndgs @ [bnd]) c
    | (_,    None,     None )  -> bndgs
    | (lnum, None,     Some _) -> raise (ScanError lnum) in
  scan lnum [] c

(* (project) file will be fully qualified *)

let check_binding (file : string) (prefix : string)
    (bnd : binding) : binding =
  match bnd with
  | BString ("include", dir)    ->
     let dir =
       let dir = UcUtils.trim_trailing_slashes dir in
       if Filename.is_relative dir
       then if prefix = "."
               then dir
            else if dir = "."
               then prefix
            else Filename.concat prefix dir
       else dir in
     if (not (Sys.file_exists dir) || not (Sys.is_directory dir))
     then non_loc_error_message
          (fun ppf ->
             Format.fprintf ppf
             "@[invalid@ directory@ in@ project@ file@ %s:@ %s@]"
             file dir);
     BString ("include", dir)
  | BBool ("units",   _)        -> bnd
  | BInt ("margin",  margin)    ->
      if margin < 3      
      then non_loc_error_message
           (fun ppf ->
              Format.fprintf ppf
              "@[invalid@ margin@ in@ project@ file@ %s@: %n@]"
              file margin);
      bnd
  | BString (x,         y)      ->
      non_loc_error_message
      (fun ppf ->
         Format.fprintf ppf
         "@[bad@ binding@ in@ file@ %s:@ @[%s@ =@ %s@]@]"
         file x y)
  | BInt    (x,         n)      ->
      non_loc_error_message
      (fun ppf ->
         Format.fprintf ppf
         "@[bad@ binding@ in@ file@ %s:@ @[%s@ =@ %d@]@]"
         file x n)
  | BBool   (x,         b)      ->
      non_loc_error_message
      (fun ppf ->
         Format.fprintf ppf
         "@[bad@ binding@ in@ file@ %s:@ @[%s@ =@ %b@]@]"
         file x b)

type project_params =
  {pp_includes : string list;
   pp_units    : bool option;
   pp_margin   : int option}

let pr_init : project_params =
  {pp_includes = [];
   pp_units    = None;
   pp_margin   = None}

(* later bindings in the project file take precedence over earlier
   ones

   in the project result, we order include directories from
   highest to lowest precedence, and we discard duplicates *)

let resolve (bndgs : binding list) : project_params =
  let rec res pr bndgs =
    match bndgs with
    | []                              -> pr
    | BString ("include", y) :: bndgs ->
        let incs = pr.pp_includes
        in res {pr with pp_includes = y :: List.remove incs y} bndgs
    | BBool ("units",     b) :: bndgs ->
        res {pr with pp_units = Some b} bndgs
    | BInt ("margin",     n) :: bndgs ->
        res {pr with pp_margin = Some n} bndgs
    | _                               -> failure "cannot happen" in
  res pr_init bndgs

let process_project_file (file : string) (prefix : string)
     : project_params =
  let inp =
    try open_in file with
    | Sys_error _ ->
        non_loc_error_message
        (fun ppf ->
           Format.fprintf ppf
           "@[unable@ to@ open@ file:@ %s@]" file) in
  match input_char_opt inp with
  | None   -> pr_init
  | Some c ->
      let bndgs =
        try scan_bindings file inp 1 c with
        | ScanError lnum ->
            non_loc_error_message
            (fun ppf ->
               Format.fprintf ppf
               "@[scanning@ error@ on@ line@ %d@ of@ file:@ %s@]"
               lnum file) in
      let bndgs = List.map (check_binding file prefix) bndgs in
      resolve bndgs

let project_name = "ucdsl.project"

type relat =
  | Extension    of string
  | NotExtension of string

let str_of_relat (rel : relat) : string =
  match rel with
  | Extension s    -> s
  | NotExtension s -> s

let find_and_process_project_file (file_opt : string option)
      : project_params =
  let rec find (path : string) (rel : relat) : (string * string) option =
    let projfile = Filename.concat path project_name in
    if Sys.file_exists projfile
      then Some (projfile, str_of_relat rel)
    else if Filename.dirname path = path
      then None
    else find (Filename.dirname path)
         (match rel with
          | Extension ext       ->
              if ext = "."
              then NotExtension ".."
              else Extension (Filename.dirname ext)
          | NotExtension dotdot ->
              NotExtension
              (if dotdot = "" then ".." else dotdot ^ "/..")) in
  let cwd = Unix.getcwd () in
  let root =
    match file_opt with
    | None      -> cwd
    | Some file -> Unix.realpath (Filename.dirname file) in
  let relat =
    if String.starts_with root cwd
    then let ext = String.lchop ~n:(String.length cwd + 1) root in
         Extension (if ext = "" then "." else ext)
    else NotExtension "" in
  match find root relat with
  | None                -> pr_init
  | Some (file, prefix) ->
      try process_project_file file prefix with
      | _ -> exit 1
