(* UcTypesExprsErrorMessages module interface *)

(* adapted from ecUserMessages.mli of EasyCrypt distribution *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* --------------------------------------------------------------------
 * Copyright (c) - 2020 - Boston University
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

open EcEnv
open UcTypecheckTypesExprs

val pp_tyerror         : env -> Format.formatter -> tyerror -> unit
val pp_cnv_failure     : env -> Format.formatter -> tymod_cnv_failure -> unit
val pp_mismatch_funsig : env -> Format.formatter -> mismatch_funsig -> unit
val pp_modappl_error   : env -> Format.formatter -> modapp_error -> unit
