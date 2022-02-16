open EcLocation
open EcSymbols
open EcBigInt

(* symbols *)

type psymbol = symbol located

let qsymb_of_symb (x : symbol) : qsymbol = ([], x)

type pqsymbol  = qsymbol located
type osymbol_r = psymbol option
type osymbol   = osymbol_r located
type pmsymbol  = (psymbol * ((pmsymbol located) list) option) list

(* types *)

type pty_r =
  | PTunivar
  | PTtuple  of pty list
  | PTnamed  of pqsymbol
  | PTvar    of psymbol
  | PTapp    of pqsymbol * pty list
  | PTfun    of pty * pty
  | PTglob   of pmsymbol located
and pty = pty_r located

(* type variable instantiations *)

type ptyannot_r =
  | TVIunamed of pty list
  | TVInamed  of (psymbol * pty) list

and ptyannot  = ptyannot_r  located

(* expressions *)

type plpattern_r =
  | LPSymbol of psymbol
  | LPTuple  of osymbol list
  | LPRecord of (pqsymbol * psymbol) list

and plpattern = plpattern_r located

type ppattern =
| PPApp of (pqsymbol * ptyannot option) * osymbol list

type ptybinding  = osymbol list * pty
and  ptybindings = ptybinding list

and pexpr_r =
  | PEcast   of pexpr * pty                       (* type cast          *)
  | PEint    of zint                              (* int. literal       *)
  | PEdecimal of (zint * (int * zint))             (* dec. literal       *)
  | PEident  of pqsymbol * ptyannot option        (* symbol             *)
  | PEapp    of pexpr * pexpr list                (* op. application    *)
  | PElet    of plpattern * pexpr_wty * pexpr     (* let binding        *)
  | PEtuple  of pexpr list                        (* tuple constructor  *)
  | PEif     of pexpr * pexpr * pexpr             (* _ ? _ : _          *)
  | PEmatch  of pexpr * (ppattern * pexpr) list   (* match              *)
  | PEforall of ptybindings * pexpr               (* forall quant.      *)
  | PEexists of ptybindings * pexpr               (* exists quant.      *)
  | PElambda of ptybindings * pexpr               (* lambda abstraction *)
  | PErecord of pexpr option * pexpr rfield list  (* record             *)
  | PEproj   of pexpr * pqsymbol                  (* projection         *)
  | PEproji  of pexpr * int                       (* tuple projection   *)
  | PEscope  of pqsymbol * pexpr                  (* scope selection    *)

and pexpr = pexpr_r located
and pexpr_wty = pexpr * pty option

and 'a rfield = {
  rf_name  : pqsymbol;
  rf_tvi   : ptyannot option;
  rf_value : 'a;
}

