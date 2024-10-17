(* UcUtils module *)

(* UC DSL Utilities *)

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

let rec sl1_starts_with_sl2 (sl1 : string list) (sl2 : string list) : bool =
  match sl1, sl2 with
  | _,           []          -> true
  | [],           _          -> false
  | (s1 :: sl1), (s2 :: sl2) -> s1 = s2 && sl1_starts_with_sl2 sl1 sl2

let capitalized_root_of_filename_with_extension file =
  String.capitalize_ascii (Filename.chop_extension (Filename.basename file))

(* the next three functions are adapted from code in
   ECsrc/ecLoader.ml *)

let try_stat name =
  try Some (Unix.lstat name) with  (* does not follow symbolic links *)
  | Unix.Unix_error _ -> None

(* dev and ino will be the device and inode produced by Unix.lstat
   of Filename.concat dir name *)

let check_case dir name (dev, ino) =
  let name = String.uncapitalize_ascii name in
  let check1 tname =
      match name = String.uncapitalize_ascii tname with
      | false -> None
      | true  -> begin
          try
            let stat = Filename.concat dir tname in
            let stat = Unix.lstat stat in
            if stat.Unix.st_dev = dev && stat.Unix.st_ino = ino
            then Some tname
            else None
          with Unix.Unix_error _ -> None
        end in
  List.find_map_opt check1 (EcUtils.Os.listdir dir)

(* full will be capitalized *)

let normalize_case_of_full_in_dir dir full =
  let stat =
    let lfull = String.uncapitalize_ascii full in
    EcUtils.List.fpick
    (List.map
     (fun name ->
        let fullname = Filename.concat dir name in
        fun () ->
          try_stat fullname |> EcUtils.omap (fun stat -> (stat, name)))
     [lfull; full])
  in match stat with
     | None              -> None
     | Some (stat, name) ->
         let stat = (stat.Unix.st_dev, stat.Unix.st_ino) in
         check_case dir name stat

let find_uc_root root prelude_dir include_dirs =
  let full = root ^ ".uc" in
  match normalize_case_of_full_in_dir prelude_dir full with
  | Some res -> Some (Filename.concat prelude_dir res)
  | None     ->
      match normalize_case_of_full_in_dir "." full with
      | Some res -> Some res
      | None     ->
          List.fold_left
          (fun opt_res dir ->
             match opt_res with
             | Some _ -> opt_res
             | None   ->
                 match normalize_case_of_full_in_dir dir full with
                 | None     -> None
                 | Some res -> Some (Filename.concat dir res))
          None include_dirs
