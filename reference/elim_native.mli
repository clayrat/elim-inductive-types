(* Interface of the native algorithm 1, on top of the kernel's native
   reference: the classification of raw declarations, the eliminators and
   ι-rules generated from a description, and staged registration.  The
   steps of a registration share a log; [run] starts one and returns its
   log with the answer. *)

open Pts_native

(** {1 Classification} *)

type raw_ctor = { rc_name : string; rc_type : term }   (* in the context of the parameters *)

type raw_decl = {
  rd_name : string;
  rd_params : term list;
  rd_indices : term list;
  rd_level : int;
  rd_ctors : raw_ctor list;
}

type site = Diagnostics_native.site = SField of int | SResult

type decl_error = Diagnostics_native.decl_error =
  | EOpenParams | EOpenIndices | ESelfReference
  | EOpenCtor of string | EDuplicateCtor of string
  | ENegative of string * int * term       (* constructor, field, its type *)
  | ENonStrict of string * int * term
  | ENested of string * int * term
  | ENotFamily of string * term
  | EArity of string * site * term
  | ENonUniform of string * site * term
  | EInIndices of string * site * term

(* [classify_decl_with true] is the demonstration mode: a field outside the
   grammar is kept as non-recursive instead of refused. *)
val classify_decl_with : bool -> raw_decl -> (ind_desc, decl_error) result
val classify_decl : raw_decl -> (ind_desc, decl_error) result

(** {1 Generation} *)

val motive_type : ind_desc -> int -> term
val method_type : ind_desc -> ctor_desc -> term     (* in the context of the parameters and P *)
val elim_type : ind_desc -> int -> term

type iota_rule = {
  rule_ctor : string;
  rule_ctx : ctx;          (* the fields, the methods, the motive, the parameters *)
  rule_lhs : term;
  rule_rhs : term;
  rule_type : term;
}

val iota_rules : ind_desc -> int -> iota_rule list

(** {1 Registration} *)

(* The stages and answers are shared with algorithm 2 (Diagnostics_native),
   whose stages and errors they include. *)
type stage = Diagnostics_native.stage =
  | AtIndType of string
  | AtCtorType of string * string
  | AtField of string * string * int
  | AtElimType of string * int
  | AtRuleLhs of string * int * string
  | AtRuleRhs of string * int * string
  | AtDefType of string
  | AtDefBody of string
  | AtMotive of string * string
  | AtEquation of string * int

type reg_error = Diagnostics_native.reg_error =
  | RClassify of decl_error
  | RTaken of gref
  | RUndeclared of string
  | RLevel of string * int * sort * int    (* constructor, field, its sort, the level of D *)
  | RNotAType of stage * term
  | RRejected of stage * error
  | ROpen
  | RCase of Diagnostics_native.case_error
  | REquation of string * int * term * term

type failure = Diagnostics_native.failure = Refuse of reg_error | NoFuelAt of stage * term

type registration = Diagnostics_native.registration =
  | Registered of signature
  | Refused of reg_error
  | OutOfFuelAt of stage * term

type log = (stage * event list) list

(* The specification, the fuel of every checker run and the log of a
   registration. *)
type registrar

val run : spec -> int -> (registrar -> (signature, failure) result) -> log * registration
val run_steps : spec -> int -> (registrar -> ('a, failure) result) -> log * ('a, failure) result

val declare_with : registrar -> bool -> signature -> raw_decl -> int list -> (signature, failure) result
val declare : registrar -> signature -> raw_decl -> int list -> (signature, failure) result
val declare_elim : registrar -> signature -> string -> int -> (signature, failure) result
val ensure_elim : registrar -> signature -> string -> int -> (signature, failure) result
val check_rule : registrar -> signature -> string -> int -> iota_rule -> (unit, failure) result
val define : registrar -> signature -> string -> term -> term -> (signature, failure) result

val unit_name : int -> string
val unit_at : int -> term
val tt_at : int -> term
val ensure_unit : registrar -> signature -> int -> (signature, failure) result

(** {1 For algorithm 2} *)

val refuse : reg_error -> ('a, failure) result
val emit : registrar -> stage -> event list -> unit       (* a stage without a checker run *)
val fuel_of : registrar -> int
(* [sort_of r sg st gamma a]: the sort [a] has in [gamma], its checker run
   logged at [st]. *)
val sort_of : registrar -> signature -> stage -> ctx -> term -> (sort, failure) result

val declare_checked : spec -> int -> signature -> raw_decl -> int list -> log * registration
val declare_bypassing : spec -> int -> signature -> raw_decl -> int list -> log * registration
val define_checked : spec -> int -> signature -> string -> term -> term -> log * registration
