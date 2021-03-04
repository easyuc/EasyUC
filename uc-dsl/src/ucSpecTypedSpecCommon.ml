(* UcSpecTypedSpecCommon module *)

(* Common definitions used by UcSpec (specification parse trees) and
   UcTypedSpec (typed specifications) *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2020-2021 - Boston University
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

open EcLocation
open EcSymbols

type psymbol = symbol located

(* message direction *)

type msg_dir =
  | In   (* input message *)
  | Out  (* output message *)

let invert_dir (dir : msg_dir) = 
  match dir with In -> Out | Out -> In
  
(* message patterns and message paths *)

type pat =                       (* for matching values *)
  | PatId       of psymbol       (* identifier to bind to *)
  | PatWildcard of EcLocation.t  (* wildcard *)

let get_loc_pat (pat : pat) : EcLocation.t = 
  match pat with
  | PatWildcard l -> l
  | PatId id      -> loc id

let get_loc_pat_list (tm : pat list) : EcLocation.t =
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

type msg_pat_body =  (* body of a msg_pat *)
  {msg_path_pat : msg_path_pat;
   pat_args : pat list option}

type msg_pat =
  {port_id      : psymbol option;   (* source port of message is bound
                                       to this identifier *)
   msg_path_pat : msg_path_pat;     (* message path pattern *)
   pat_args     : pat list option}  (* optional list of value patterns,
                                       one for each message argument *)

type msg_path_u =
  {inter_id_path : symbol list;  (* inter id path *)
   msg : symbol}                 (* message name *)

type msg_path = msg_path_u located  (* message path *)

(* left-hand sides of assignment *)

type lhs =  (* left-hand sides *)
  | LHSSimp  of psymbol       (* assign to variable *)
  | LHSTuple of psymbol list  (* assign to tuple of variables *)
