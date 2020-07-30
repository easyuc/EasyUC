(* UcSpec module *)

(* Specification Parse Trees *)

open EcLocation

exception LexerError of EcLocation.t * string

exception ParseError of EcLocation.t * string

exception TypeError of EcLocation.t * string

let parse_error loc msg =
  raise (ParseError (loc, msg))

let type_error loc msg =
  raise (TypeError (loc, msg))

type string_l = string located

type id = string_l

type msg_dir =
  | In
  | Out

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

type msg_path_item =
  | MsgPathId       of id
  | MsgPathOtherMsg of EcLocation.t

type qid = id list

type msg_path = {inter_id_path: qid; msg_or_other : msg_path_item}

type pat =
  | PatId of id
  | PatIdType of type_binding
  (*| Tuple of match_item list located*)
  | PatWildcard of EcLocation.t

type msg_pat =
  {port_id : id option; path : msg_path; pat_args : pat list option}

type msg_pat_body =
  {path : msg_path; pat_args : pat list option}

type expression =
  | Id    of qid
  | Tuple of expression_l list
  | App   of id * expression_l list
  | Enc   of expression_l

and expression_l = expression located

type msg_instance =
  {path : msg_path; args : expression_l list; port_id : id option}

type state_instance = {id : id; args : expression_l list}

type send_and_transition = {msg : msg_instance; state : state_instance}

type instruction =
  | Assign of id * expression_l
  | Sample of id * expression_l
  | ITE of expression_l * instruction_l list * instruction_l list option
  | Decode of
      expression_l * ty * pat list * instruction_l list *
      instruction_l list
  | SendAndTransition of send_and_transition
  | Fail

and instruction_l = instruction located

type msg_match_clause = {msg_pat : msg_pat; code : instruction_l list}

type state_code = {vars : type_binding list; mmclauses : msg_match_clause list}

type state = {id : id; params : type_binding list; code : state_code}
                
type state_def =
  | InitialState of state
  | FollowingState of state 

type party_def =
  {id : id; serves : qid list; states : state_def list}

type sub_item =
  | SubFunDecl of sub_fun_decl
  | PartyDef   of party_def

type fun_body =
  | FunBodyReal  of sub_item list
  | FunBodyIdeal of state_def list

let is_real_fun_body fb =
  match fb with
  | FunBodyReal _  -> true
  | FunBodyIdeal _ -> false

type fun_def =
  {id : id; params : fun_param list; id_dir : id; id_adv : id option;
   fun_body : fun_body}

type sim_def =
  {id : id; uses : id; sims : id; sims_arg_ids : id list;
   states : state_def list }

type def =
  | InterDef of inter_def
  | FunDef   of fun_def
  | SimDef   of sim_def

type externals = {ec_requirements : id list; dl_imports : id list}

type spec = {externals : externals; definitions : def list}
