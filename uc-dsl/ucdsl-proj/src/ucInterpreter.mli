(* UnInterpreter module interface *)

open EcSymbols
open EcEnv

open UcSpecTypedSpecCommon
open UcSpec
open UcTypedSpec

exception ConfigError

type config

val create_config : symbol -> maps_tyd -> env -> fun_expr -> config

val is_gen_config           : config -> bool
val is_real_config          : config -> bool
val is_ideal_config         : config -> bool
val is_real_running_config  : config -> bool
val is_ideal_running_config : config -> bool

val env_of_config : config -> env

val update_prover_infos_config :
  config -> EcParsetree.pprover_infos -> config

val add_var_to_config : config -> psymbol -> pty -> config

val add_hyp_to_config : config -> psymbol -> pexpr -> config

val real_of_gen_config : config -> maps_tyd -> config

val ideal_of_gen_config : config -> maps_tyd -> config

val loc_of_running_config_next_instr : config -> EcLocation.t

(* sending messages and stepping configurations *)

(* exceptions for when EasyCrypt's proof engine can't solve a needed
   goal, and consequently configuration is not changed *)

exception BlockedIf                    (* step blocked on boolean expression
                                          of if-then-else *)
exception BlockedMatch                 (* step blocked on datatype value
                                          being matched *)
exception BlockedPortOrAddrComparison  (* step blocked at comparison of
                                          port or address *)

type effect =
  | EffectStep                         (* step succeeded, and new configuration
                                          is running *)
  | EffectRand of EcIdent.t            (* step added ident representing
                                          random choice to global context,
                                          and new configuration is running *)
  | EffectMsgOut of sent_msg_expr_tyd  (* a message was output, and new
                                          configuration is not running *)
  | EffectFailOut                      (* fail was output, and new
                                          configuration is not running *)

val send_message_to_real_or_ideal_config :
      config -> sent_msg_expr_tyd -> config * effect

val step_running_real_or_ideal_config :
      config -> config * effect
