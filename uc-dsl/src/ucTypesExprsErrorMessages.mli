(* UcTypesExprsErrorMessages module interface *)

(* Formatting error messages issued when translating types and
   expressions *)

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
open UcTransTypesExprs

val pp_tyerror : env -> Format.formatter -> tyerror -> unit
