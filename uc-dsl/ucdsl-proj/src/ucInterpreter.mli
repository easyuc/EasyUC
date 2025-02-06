(* UnInterpreter module interface *)

open EcSymbols
open EcParsetree
open EcEnv

open UcSpecTypedSpecCommon
open UcSpec
open UcTypedSpec

exception ConfigError

type config

val pp_config : Format.formatter -> config -> unit

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

(* typecheck and then pretty print to a string a sent message
   expression - all using the environment of a configuration *)

val typecheck_and_pp_sent_msg_expr : config -> sent_msg_expr -> string

val update_prover_infos_config :
      config -> EcParsetree.pprover_infos -> config

val modify_rewriting_dbs_config : config -> mod_dbs -> config
val pp_rewriting_dbs_config  : Format.formatter -> config -> unit

val add_var_to_config             : config -> psymbol -> pty -> config
val add_var_to_config_make_unique : config -> psymbol -> pty -> config * symbol

val add_hyp_to_config             : config -> psymbol -> pformula -> config
val add_hyp_to_config_make_unique :
      config -> psymbol -> pformula -> config * symbol

val real_of_gen_config  : config -> config
val ideal_of_gen_config : config -> config

(* sending messages and stepping configurations *)

val send_message_to_real_or_ideal_config : config -> sent_msg_expr -> config

type effect =
  | EffectOK                          (* step succeeded (not random
                                         assignment), and new configuration
                                         is running or sending *)
  | EffectRand of symbol              (* step added ident representing
                                         random choice to global context,
                                         and new configuration is running *)
  | EffectMsgOut of string * control  (* a message was output, and new
                                         configuration is real or ideal;
                                         control says who has control *)
  | EffectFailOut                     (* fail was output, and new
                                         configuration is real or ideal *)

val pp_effect : Format.formatter -> effect -> unit  (* for debugging *)

(* exceptions that can be raised by
   step_running_or_sending_real_or_ideal_config *)

(* step failed, because couldn't evaluate the boolean expression of
   an if-then-else to true or false *)

exception StepBlockedIf

(* step failed, because couldn't expose the constructor of an
   expression being matched *)

exception StepBlockedMatch

(* step failed, because address and/or port comparisons couldn't be
   decided *)

exception StepBlockedPortOrAddrCompare

(* if the pprover_infos option is None, it means to use the prover_infos
   of the configuration for SMT calls

   if it's Some ppi, it means to update the prover_infos of the
   configuration with ppi (this can issue an error message, and use
   that for SMT calls; but the returned configuration's prover_infos
   is *not* updated with ppi

   if mod_pdbs is None, it means to use the rewriting
   databases of the configuration for simplification

   if it's Some (rm_pdbs, add_pdbs), it means to update the rewriting
   databases of the configuration by first removing rm_pdbs and then
   adding add_pdbs (this can issue an error message), and use that for
   simplification; but the returned configuration's rewriting
   databases are *not* updated *)

val step_running_or_sending_real_or_ideal_config :
      config ->
      EcParsetree.pprover_infos option ->
      mod_dbs option ->
      config * effect
