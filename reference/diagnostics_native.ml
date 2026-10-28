(* The diagnostics of both algorithms, native, as theories/Diagnostics.v:
   the stages of a registration log, the errors of classification, of
   case trees and calls, and of registration, and the answers of a
   registration.  They lie below both algorithms, on the kernel alone, so
   that the native algorithm 2 (Recursion_native) depends on algorithm 1
   (Elim_native) and not the converse, and the registration monad
   (Registration_native) depends on neither. *)

open Pts_native

type site = SField of int | SResult

type decl_error =
  | EOpenParams | EOpenIndices | ESelfReference
  | EOpenCtor of string | EDuplicateCtor of string
  | ENegative of string * int * term       (* constructor, field, its type *)
  | ENonStrict of string * int * term
  | ENested of string * int * term
  | ENotFamily of string * term
  | EArity of string * site * term
  | ENonUniform of string * site * term
  | EInIndices of string * site * term

type stage =
  | AtIndType of string
  | AtCtorType of string * string
  | AtField of string * string * int
  | AtElimType of string * int
  | AtRuleLhs of string * int * string
  | AtRuleRhs of string * int * string
  | AtDefType of string
  | AtDefBody of string
  | AtMotive of string * string           (* f, the variable split: the sort of the motive *)
  | AtEquation of string * int            (* f, the leaf: its defining equation *)

type case_error =
  | CDuplicateArg of string
  | CNoStruct of string
  | CUnbound of string
  | CNotFamily of string * term
  | CIndices of string * term
  | CGeneralize of string * string
  | CParams of string * string
  | CBranches of string
  | CFields of string * int
  | CFieldName of string * string
  | CRoot of string
  | CUnsplit of string
  | CMotiveSort of string * sort
  | CCallArity of term
  | CNotStructural of term
  | CNotImmediate of term
  | CIndexChanged of string * term
  | CConstantChanged of string * term

type reg_error =
  | RClassify of decl_error
  | RTaken of gref
  | RUndeclared of string
  | RLevel of string * int * sort * int    (* constructor, field, its sort, the level of D *)
  | RNotAType of stage * term
  | RRejected of stage * error
  | ROpen
  | RCase of case_error
  | REquation of string * int * term * term   (* f, the leaf, the two sides *)

type failure = Refuse of reg_error | NoFuelAt of stage * term

type registration =
  | Registered of signature
  | Refused of reg_error
  | OutOfFuelAt of stage * term

type log = (stage * event list) list
