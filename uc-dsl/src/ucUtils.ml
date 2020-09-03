(* UcUtils module *)

(* UC DSL Utilities *)

open Batteries
open UcSpec
open UcTypedSpec
open EcLocation

let index_of_ex x xs =
  match List.index_of x xs with
  | None   -> raise Not_found
  | Some i -> i

let indexed_map_to_list (mapind : ('o * int) IdMap.t) : 'o list =
  let l = IdMap.fold (fun _ v l -> v :: l ) mapind [] in
  let lord = List.sort (fun a1 a2 -> snd a1 - snd a2) l in
  List.map (fun a -> fst a) lord

let filter_map (fm : 'a -> 'b option) (m : 'a IdMap.t) : 'b IdMap.t =
  let flt =
    IdMap.filter
    (fun _ def ->
       match fm def with
       | Some _ -> true
       | None   -> false)
    m in
  IdMap.map
  (fun def ->
     match fm def with
     | Some x -> x
     | None -> raise (Failure "!impossible!"))
  flt

let unlocm (lm : 'a located IdMap.t) : 'a IdMap.t =
  IdMap.map (fun al -> unloc al) lm

let mergelocs (l : 'a located list) : EcLocation.t = mergeall(List.map loc l)

let dummyloc (o : 'a) : 'a located = mk_loc _dummy o

let dummylocl (l : 'a list) : 'a located list = List.map (fun i -> dummyloc i) l

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

let qid1_starts_with_qid2 (q1 : qid) (q2 : qid) : bool =
  List.for_all
  identity
  (List.mapi
   (fun i id2 -> 
      match List.nth_opt q1 i with
      | Some id1 -> unloc id1 = unloc id2
      | None     -> false)
   q2)

let sl1_starts_with_sl2 (sl1 : string list) (sl2 : string list) : bool =
  List.for_all 
  identity
  (List.mapi
   (fun i s2 -> 
      match (List.nth_opt sl1 i) with 
      | Some s1 -> s1=s2
      | None    -> false)
   sl2)
