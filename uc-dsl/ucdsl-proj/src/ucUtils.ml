(* UcUtils module *)

(* UC DSL Utilities *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2020-2021 - Boston University
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

open Batteries
open EcLocation

let rec find_dup ?(cmp = Stdlib.compare) (xs : 'a list ) =
  match xs with
  | []      -> None
  | x :: xs ->
      if BatList.mem_cmp cmp x xs then Some x else find_dup ~cmp xs

let has_dup ?(cmp = Stdlib.compare) (xs : 'a list) =
  Option.is_some (find_dup ~cmp xs)

let index_of_ex x xs =
  match List.index_of x xs with
  | None   -> raise Not_found
  | Some i -> i

let filename_of_loc l = l.loc_fname

let begin_of_file_pos (file : string) : Lexing.position =
  {pos_fname = file; pos_lnum = 0; pos_bol = 0; pos_cnum = 0}

let begin_of_file_loc (file : string) : EcLocation.t =
  let pos = begin_of_file_pos file in
  EcLocation.make pos pos

let mergelocs (l : 'a located list) : EcLocation.t = mergeall (List.map loc l)

let dummyloc (o : 'a) : 'a located = mk_loc _dummy o

let string_of_id_path (iop : string list) : string =
  List.fold_left (fun p i -> if p <> "" then p ^ "." ^ i else i) "" iop

let format_strings
    (ppf : Format.formatter) (sepc : char) (xs : string list) : unit =
  let rec fs (ppf : Format.formatter) (xs : string list) : unit =
    match xs with
    | []      -> ()
    | [x]     -> Format.fprintf ppf "%s" x
    | x :: xs -> Format.fprintf ppf "%s%c@ %a" x sepc fs xs in
  Format.fprintf ppf "@[<hv>%a@]" fs xs

let format_strings_comma
    (ppf : Format.formatter) (xs : string list) : unit =
  format_strings ppf ',' xs

let format_id_paths_comma
    (ppf : Format.formatter) (iops : string list list) : unit =
  format_strings ppf ',' (List.map string_of_id_path iops)

let sl1_starts_with_sl2 (sl1 : string list) (sl2 : string list) : bool =
  List.for_all 
  identity
  (List.mapi
   (fun i s2 -> 
      match (List.nth_opt sl1 i) with 
      | Some s1 -> s1=s2
      | None    -> false)
   sl2)

let capitalized_root_of_filename_with_extension file =
  String.capitalize (Filename.chop_extension (Filename.basename file))

let find_file root ext prelude_dir include_dirs =
  let full     = root ^ ext in
  let full_cap = String.capitalize full in
  let prelude_full = prelude_dir ^ "/" ^ full in
  let prelude_full_cap = prelude_dir ^ "/" ^ full_cap in
  if Sys.file_exists prelude_full
    then Some prelude_full
  else if Sys.file_exists prelude_full_cap
    then Some prelude_full_cap
  else if Sys.file_exists full
    then Some full
  else if Sys.file_exists full_cap
    then Some full_cap
  else List.fold_left
       (fun opt_res dir ->
          match opt_res with
          | None   ->
              let qualified     = dir ^ "/" ^ full in
              let qualified_cap = dir ^ "/" ^ full_cap in
              if Sys.file_exists qualified
                then Some qualified
              else if Sys.file_exists qualified_cap
                then Some qualified_cap
              else None
          | Some _ -> opt_res)
       None include_dirs
