(* UnInterpreter module interface *)

open EcSymbols
open EcEnv

open UcSpecTypedSpecCommon
open UcSpec
open UcTypedSpec

exception ConfigError

type config

val pp_config : Format.formatter -> config -> unit

(* pretty print a sent message expression using the environment
   of a configuration (which is not exported from this module) *)

val pp_sent_msg_expr_tyd_in_config :
  Format.formatter -> config -> sent_msg_expr_tyd -> unit

val create_gen_config : symbol -> maps_tyd -> env -> fun_expr -> config

val is_gen_config           : config -> bool
val is_real_config          : config -> bool
val is_ideal_config         : config -> bool
val is_real_running_config  : config -> bool
val is_ideal_running_config : config -> bool
val is_real_sending_config  : config -> bool
val is_ideal_sending_config : config -> bool

type control =  (* does environment or adversary have control? *)
  | CtrlEnv
  | CtrlAdv

val control_of_real_or_ideal_config : config -> control

val loc_of_running_config_next_instr : config -> EcLocation.t option

val update_prover_infos_config :
  config -> EcParsetree.pprover_infos -> config

val add_var_to_config : config -> psymbol -> pty -> config

val add_hyp_to_config : config -> psymbol -> pexpr -> config

val real_of_gen_config  : config -> config
val ideal_of_gen_config : config -> config

(* sending messages and stepping configurations *)

type effect =
  | EffectOK                           (* step succeeded (not random
                                          assignment), and new configuration
                                          is running or sending *)
  | EffectRand of EcIdent.t            (* step added ident representing
                                          random choice to global context,
                                          and new configuration is
                                          running *)
  | EffectMsgOut of sent_msg_expr_tyd  (* a message was output, and new
                                          configuration is real or ideal *)
  | EffectFailOut                      (* fail was output, and new
                                          configuration is real or ideal *)
  | EffectBlockedIf                    (* configuration is running *)
  | EffectBlockedMatch                 (* configuration is running *)
  | EffectBlockedPortOrAddrCompare     (* configuration is running or sending *)

val send_message_to_real_or_ideal_config :
      config -> sent_msg_expr -> config

val step_running_or_sending_real_or_ideal_config :
      config -> config * effect
