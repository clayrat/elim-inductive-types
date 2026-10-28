(** Interface of the native algorithm 1, on top of the kernel's native
    reference and the registration monad: the classification of raw
    declarations, the eliminators and ι-rules generated from a
    description, and staged registration. *)

open Pts_native

(** The registration monad and the diagnostics of both algorithms,
    re-exported as Elim/Declare.v exports Registration.v. *)
include module type of struct include Registration_native end

(** {1 Classification} *)

type raw_ctor = {
  rc_name : string;
  rc_type : term;          (** in the context of the parameters *)
}

type raw_decl = {
  rd_name : string;
  rd_params : term list;
  rd_indices : term list;
  rd_level : int;
  rd_ctors : raw_ctor list;
}

(** Whether classification checks strict positivity, or bypasses it:
    [Bypass] is the demonstration mode, where a field outside the grammar
    is kept as non-recursive instead of refused. *)
type positivity = Checked | Bypass

val classify_decl_with : positivity -> raw_decl -> (ind_desc, decl_error) result

val classify_decl : raw_decl -> (ind_desc, decl_error) result

(** {1 Generation} *)

val motive_type : ind_desc -> int -> term

(** In the context of the parameters and P. *)
val method_type : ind_desc -> ctor_desc -> term

val elim_type : ind_desc -> int -> term

type iota_rule = {
  rule_ctor : string;
  rule_ctx : ctx;          (** the fields, the methods, the motive, the parameters *)
  rule_lhs : term;
  rule_rhs : term;
  rule_type : term;
}

val iota_rules : ind_desc -> int -> iota_rule list

(** {1 Registration} *)

val declare_with : registrar -> positivity -> signature -> raw_decl -> int list -> (signature, failure) result

val declare : registrar -> signature -> raw_decl -> int list -> (signature, failure) result
val declare_elim : registrar -> signature -> string -> int -> (signature, failure) result
val ensure_elim : registrar -> signature -> string -> int -> (signature, failure) result
val check_rule : registrar -> signature -> string -> int -> iota_rule -> (unit, failure) result

val unit_name : int -> string
val unit_at : int -> term
val tt_at : int -> term
val ensure_unit : registrar -> signature -> int -> (signature, failure) result

(** {1 Entry points} *)

val declare_checked : spec -> int -> signature -> raw_decl -> int list -> log * registration
val declare_bypassing : spec -> int -> signature -> raw_decl -> int list -> log * registration
