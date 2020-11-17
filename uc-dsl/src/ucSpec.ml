(* UcSpec module *)

(* Specification Parse Trees *)

open EcLocation
open EcSymbols
open EcParsetree
open UcMessage

let parse_error = error_message

let type_error = error_message

type msg_dir =
  | In
  | Out

let invert_dir (dir : msg_dir) = 
  match dir with In -> Out | Out -> In

type type_binding = {id : psymbol; ty : pty}

type message_body =
  {id : psymbol; params : type_binding list}

type message_def =
  {dir : msg_dir; id : psymbol; params : type_binding list;
   port : psymbol option}

type comp_item = {sub_id : psymbol; inter_id : psymbol}

type inter =
  | Basic     of message_def list
  | Composite of comp_item list

type named_inter = {id : psymbol; inter : inter}

type inter_def =
  | DirectInter      of named_inter
  | AdversarialInter of named_inter

type fun_param = {id : psymbol; id_dir : psymbol}

type sub_fun_decl = {id : psymbol; fun_id : psymbol}

type msg_or_star =
  | MsgOrStarMsg of symbol
  | MsgOrStarStar

type msg_path_pat_u = {inter_id_path : symbol list; msg_or_star : msg_or_star}

type msg_path_pat = msg_path_pat_u located

let msg_path_pat_ends_star mpp =
  match (unloc mpp).msg_or_star with
  | MsgOrStarMsg  _ -> false
  | MsgOrStarStar   -> true

type pat =
  | PatId       of psymbol
  | PatWildcard of EcLocation.t

let get_loc_pat (pat : pat) : EcLocation.t = 
  match pat with
  | PatWildcard l -> l
  | PatId id      -> loc id

let get_loc_pat_list (tm : pat list) : EcLocation.t =
  mergeall (List.map (fun mi -> get_loc_pat mi) tm)

type msg_pat =
  {port_id : psymbol option; msg_path_pat : msg_path_pat;
   pat_args : pat list option}

type msg_pat_body =
  {msg_path_pat : msg_path_pat; pat_args : pat list option}

type msg_path_u = {inter_id_path : symbol list; msg : symbol}

type msg_path = msg_path_u located

type msg_expr =
  {path : msg_path; args : pexpr list located; port_id : psymbol option}

type state_expr = {id : psymbol; args : pexpr list located}

type send_and_transition = {msg_expr : msg_expr; state_expr : state_expr}

type lhs =
  | LHSSimp  of psymbol
  | LHSTuple of psymbol list

type instruction_u =
  | Assign of lhs * pexpr
  | Sample of lhs * pexpr
  | ITE of pexpr * instruction list located *  (* if-then-else *)
           instruction list located option
  | Match of pexpr * (ppattern * instruction list located) list
  | SendAndTransition of send_and_transition
  | Fail

and instruction = instruction_u located

type msg_match_clause = {msg_pat : msg_pat; code : instruction list located}

type state_code = {vars : type_binding list; mmclauses : msg_match_clause list}

type state =
  {id : psymbol; params : type_binding list located; code : state_code}
                
type state_def =
  | InitialState of state
  | FollowingState of state 

type party_def =
  {id : psymbol; serves : pqsymbol list; states : state_def list}

type fun_body_real =
  {sub_fun_decls : sub_fun_decl list; party_defs : party_def list}

type fun_body =
  | FunBodyReal  of fun_body_real
  | FunBodyIdeal of state_def list

let is_real_fun_body fb =
  match fb with
  | FunBodyReal _  -> true
  | FunBodyIdeal _ -> false

type fun_def =
  {id : psymbol; params : fun_param list; id_dir : psymbol;
   id_adv : psymbol option; fun_body : fun_body}

type sim_def =
  {id : psymbol; uses : psymbol; sims : psymbol;
   sims_arg_ids : psymbol list located; states : state_def list }

type def =
  | InterDef of inter_def
  | FunDef   of fun_def
  | SimDef   of sim_def

type externals = {uc_requires : psymbol list; ec_requires : psymbol list}

type spec = {externals : externals; definitions : def list}
