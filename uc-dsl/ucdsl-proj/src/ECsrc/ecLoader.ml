(* -------------------------------------------------------------------- *)
open EcUtils

(* -------------------------------------------------------------------- *)
type idx_t     = int * int
type namespace = [ `System | `Named of string ]

type ecloader = {
  mutable ecl_idirs : ((namespace option * string) * idx_t) list;
}

(* -------------------------------------------------------------------- *)
type kind = [`Ec | `EcA]

exception BadExtension of string

let getkind ext =
  let ext =
    if   String.starts_with ext "."
    then String.chop ~l:1 ~r:0 ext
    else ext
  in

  match ext with
  | "ec"  -> `Ec
  | "eca" -> `EcA
  | _     -> raise (BadExtension ("." ^ ext))

(* -------------------------------------------------------------------- *)
let create () = { ecl_idirs = []; }

(* -------------------------------------------------------------------- *)
let aslist (ld : ecloader) =
  ld.ecl_idirs

(* -------------------------------------------------------------------- *)
let dup (ld : ecloader) = { ecl_idirs = ld.ecl_idirs; }

(* -------------------------------------------------------------------- *)
let forsys (ld : ecloader) =
  { ecl_idirs =
      List.filter
        (fun ((b, _), _) -> b = Some `System)
        ld.ecl_idirs; }

(* -------------------------------------------------------------------- *)
let rec addidir ?namespace ?(recursive = false) (idir : string) (ecl : ecloader) =
  if recursive then begin
    let isdir filename =
      let filename = Filename.concat idir filename in
      try Sys.is_directory filename with Sys_error _ -> false
    in

    let dirs = (try EcUtils.Os.listdir idir with Unix.Unix_error _ | Sys_error _ -> []) in
    let dirs = List.sort compare (List.filter isdir dirs) in

      List.iter (fun filename ->
        if not (String.starts_with filename ".") then
          let filename = Filename.concat idir filename in
            addidir ?namespace ~recursive filename ecl)
        dirs
  end;

  match (try Some (Unix.stat idir) with Unix.Unix_error _ -> None) with
  | None    -> ()
  | Some st -> begin
      let idx = (st.Unix.st_dev, st.Unix.st_ino) in
      let idirs = List.filter (fun ((nm, _), _) -> nm = namespace) ecl.ecl_idirs in

      match Sys.os_type with
      | "Win32" ->
          let test ((_, name), _) = name = idir in
          if not (List.exists test idirs) then
            ecl.ecl_idirs <- ((namespace, idir), idx) :: ecl.ecl_idirs

      | _ ->
          if not (List.exists ((=) idx |- snd) idirs) then
            ecl.ecl_idirs <- ((namespace, idir), idx) :: ecl.ecl_idirs
  end

(* -------------------------------------------------------------------- *)
let try_stat name =
  try  Some (Unix.lstat name)
  with Unix.Unix_error _ -> None

(* -------------------------------------------------------------------- *)
let norm_name (mode : [`Lower | `Upper]) name =
  String.init
    (String.length name)
    (function
     | 0 when mode = `Lower -> Char.lowercase_ascii name.[0]
     | 0 when mode = `Upper -> Char.uppercase_ascii name.[0]
     | i -> name.[i])

(* -------------------------------------------------------------------- *)
let check_case idir name (dev, ino) =
  let name = norm_name `Lower name in

  let check1 tname =
      match name = norm_name `Lower tname with
      | false -> None
      | true  -> begin
          try
            let stat = Filename.concat idir tname in
            let stat = Unix.lstat stat in

            if stat.Unix.st_dev = dev && stat.Unix.st_ino = ino then
              Some tname
            else None
          with Unix.Unix_error _ -> None
      end
  in
    try  List.find_map_opt check1 (EcUtils.Os.listdir idir)
    with Unix.Unix_error _ -> None

(* -------------------------------------------------------------------- *)
let locate ?(namespaces = [None]) (name : string) (ecl : ecloader) =
  if not (EcRegexp.match_ (`S "^[a-zA-Z0-9_]+$") name) then
    None
  else
    let locate kind ((inamespace, idir), _) =
      let name =
        match kind with
        | `Ec  -> Printf.sprintf "%s.ec"  name
        | `EcA -> Printf.sprintf "%s.eca" name
      in

      let nmok =
        let for1 namespace =
          match namespace, inamespace with
          | Some nm, Some inm -> nm = inm
          | None   , (None | Some `System) -> true
          | _      , _                     -> false
        in List.exists for1 namespaces in

      if not nmok then None else

      let stat =
        let oname = norm_name `Upper name in
        let iname = norm_name `Lower name in
          List.fpick
            (List.map
               (fun name ->
                 let fullname = Filename.concat idir name in
                   fun () -> try_stat fullname |> omap (fun s -> (s, name)))
               [iname; oname])
      in
        match stat with
        | None -> None
        | Some (stat, name) ->
          let stat = (stat.Unix.st_dev, stat.Unix.st_ino) in
            check_case idir name stat
            |> Option.map (fun name -> (inamespace, Filename.concat idir name, kind))
    in

    match
      List.rev_pmap
        (fun kind -> List.opick (locate kind) ecl.ecl_idirs)
        [`Ec; `EcA]
    with
    | [x] -> Some x
    | _   -> None
