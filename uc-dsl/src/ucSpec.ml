(* UcSpec module *)

(* Specification Parse Trees *)

open EcLocation
open UcMessage

let parse_error = error_message

let type_error = error_message

type string_l = string located

type id = string_l

type msg_dir =
  | In
  | Out

let invert_dir (dir : msg_dir) = 
  match dir with In -> Out | Out -> In

type ty =
  | NamedTy of id
  | TupleTy of ty list

type type_binding = {id : id; ty : ty}

type message_body =
  {id : id; params : type_binding list}

type message_def =
  {dir : msg_dir; id : id; params : type_binding list; port : id option}

type comp_item = {sub_id : id; inter_id : id}

type inter =
  | Basic     of message_def list
  | Composite of comp_item list

type named_inter = {id : id; inter : inter}

type inter_def =
  | DirectInter      of named_inter
  | AdversarialInter of named_inter

type fun_param = {id : id; id_dir : id}

type sub_fun_decl = {id : id; fun_id : id}

type msg_or_star =
  | MsgOrStarMsg  of id
  | MsgOrStarStar of EcLocation.t

type qid = id list

type msg_path_pat = {inter_id_path : qid; msg_or_star : msg_or_star}

let msg_path_pat_ends_star mpp =
  match mpp.msg_or_star with
  | MsgOrStarMsg  _ -> false
  | MsgOrStarStar _ -> true

type pat =
  | PatId       of id
  | PatWildcard of EcLocation.t

type msg_pat =
  {port_id : id option; msg_path_pat : msg_path_pat; pat_args : pat list option}

type msg_pat_body =
  {msg_path_pat : msg_path_pat; pat_args : pat list option}

type expression =
  | Id    of qid
  | Tuple of expression_l list
  | App   of id * expression_l list
  | Enc   of expression_l

and expression_l = expression located

type msg_path = {inter_id_path : qid; msg : id}

type msg_expr =
  {path : msg_path; args : expression_l list located; port_id : id option}

type state_expr = {id : id; args : expression_l list located}

type send_and_transition = {msg_expr : msg_expr; state_expr : state_expr}

type instruction =
  | Assign of id * expression_l
  | Sample of id * expression_l
  | ITE of expression_l * instruction_l list located *
           instruction_l list located option
  | Decode of
      expression_l * ty * pat list * instruction_l list located *
      instruction_l list located
  | SendAndTransition of send_and_transition
  | Fail

and instruction_l = instruction located

type msg_match_clause = {msg_pat : msg_pat; code : instruction_l list located}

type state_code = {vars : type_binding list; mmclauses : msg_match_clause list}

type state = {id : id; params : type_binding list located; code : state_code}
                
type state_def =
  | InitialState of state
  | FollowingState of state 

type party_def =
  {id : id; serves : qid list; states : state_def list}

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
  {id : id; params : fun_param list; id_dir : id; id_adv : id option;
   fun_body : fun_body}

type sim_def =
  {id : id; uses : id; sims : id; sims_arg_ids : id list located;
   states : state_def list }

type def =
  | InterDef of inter_def
  | FunDef   of fun_def
  | SimDef   of sim_def

type externals = {ec_requires : id list; uc_requires : id list}

type spec = {externals : externals; definitions : def list}
