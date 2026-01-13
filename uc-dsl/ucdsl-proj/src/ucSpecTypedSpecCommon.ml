(* UcSpecTypedSpecCommon module *)

(* Common definitions used by UcSpec (specification parse trees) and
   UcTypedSpec (typed specifications) *)

open EcLocation
open EcSymbols
open EcUtils

type psymbol = symbol located

(* message direction *)

type msg_dir =
  | In   (* input message *)
  | Out  (* output message *)

let invert_dir (dir : msg_dir) = 
  match dir with In -> Out | Out -> In
  
(* message patterns and message paths

   the type variable 'a will be instantiated with either
   symbol (UcSpec) or EcIdent.t * EcTypes.ty (UcTypedSpec) *)

type 'a pat =                    (* for matching values *)
  | PatId       of 'a located    (* identifier to bind to *)
  | PatWildcard of EcLocation.t  (* wildcard *)

let match_pat (pat : 'a pat) (y : 'b) : ('a * 'b) option =
  match pat with
  | PatId x       -> Some (unloc x, y)
  | PatWildcard _ -> None

let pat_id_data (pat : 'a pat) : 'a option =
  match pat with
  | PatId x       -> Some (unloc x)
  | PatWildcard _ -> None

(* if pats is None, then ys must be empty; if pats is Some pats',
   then pats' and ys must have the same length *)

let match_pats (pats : 'a pat list option) (ys : 'b list) : ('a * 'b) list =
  match pats with
  | None      -> []
  | Some pats ->
      List.filter_map (fun x -> x) (List.map2 match_pat pats ys)

let get_loc_pat (pat : 'a pat) : EcLocation.t = 
  match pat with
  | PatWildcard l -> l
  | PatId id      -> loc id

let get_loc_pat_list (tm : 'a pat list) : EcLocation.t =
  mergeall (List.map (fun mi -> get_loc_pat mi) tm)

type msg_or_star =
  | MsgOrStarMsg of symbol  (* message name *)
  | MsgOrStarStar           (* wildcard *)

type msg_path_pat_u =
  {inter_id_path : symbol list;  (* inter id path *)
   msg_or_star   : msg_or_star}  (* message name or wildcard *)

type msg_path_pat = msg_path_pat_u located

let msg_path_pat_ends_star (mpp : msg_path_pat) : bool =
  match (unloc mpp).msg_or_star with
  | MsgOrStarMsg  _ -> false
  | MsgOrStarStar   -> true

type 'a msg_pat_body =  (* body of a msg_pat *)
  {msg_path_pat : msg_path_pat;
   pat_args : 'a pat list option}

type 'a msg_pat =
  {port_id      : 'a located option;   (* source port of message is bound
                                          to this identifier *)
   msg_path_pat : msg_path_pat;        (* message path pattern *)
   pat_args     : 'a pat list option}  (* optional list of value patterns,
                                          one for each message argument *)

let match_port_id (pid : 'a located option) (y : 'b) : ('a * 'b) option =
  match pid with
  | None     -> None
  | Some pid -> Some (unloc pid, y)

let match_msg_pat (mp : 'a msg_pat) (port : 'b) (args : 'b list)
      : ('a * 'b) list =
  (match match_port_id mp.port_id port with
   | None   -> []
   | Some p -> [p]) @
  match_pats mp.pat_args args

type msg_path_u =
  {inter_id_path : symbol list;  (* inter id path *)
   msg : symbol}                 (* message name *)

let msg_path_u_to_qsymbol (mpu : msg_path_u) : qsymbol =
  (mpu.inter_id_path, mpu.msg)

type msg_path = msg_path_u located  (* message path *)

(* for assignment instructions: *)

type lhs =  (* left-hand sides *)
  | LHSSimp  of psymbol       (* assign to variable *)
  | LHSTuple of psymbol list  (* assign to tuple of variables *)
