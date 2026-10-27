(* Interface of the native algorithm 2, on top of the native algorithm 1:
   the history of results, the elaboration of case trees, and the
   compiler of structural recursion.  Registrations share the log of a
   registrar of Elim_native. *)

open Pts_native
open Diagnostics_native

(** {1 The history} *)

val below_name : string -> int -> string
val build_name : string -> int -> string
val recbelow_name : string -> int -> string
val history_level : ind_desc -> int -> int

val below_type : ind_desc -> int -> term
val below_body : ind_desc -> int -> term
val build_type : ind_desc -> int -> term
val build_body : ind_desc -> int -> term
val recbelow_type : ind_desc -> int -> term
val recbelow_body : ind_desc -> int -> term

(* [Below_D], [build_D] and [recBelow_D] for motives in [Type_j], with
   [Unit_ℓ], [elim_D[ℓ+1]] and [elim_D[ℓ]]; unless [recBelow_D] is there. *)
val ensure_below : Elim_native.registrar -> signature -> string -> int -> (signature, failure) result

(** {1 Case trees} *)

type mark = Constant | Varying
type strategy = Direct | History

(* A leaf is a named right side, a split names its variable and, for
   every constructor, the names of its fields and the subtree. *)
type case_tree = Leaf of Looping.named | Split of string * (string * string list * case_tree) list

type fun_decl = {
  fn_name : string;
  fn_args : (string * Looping.named * mark) list;   (* outermost first *)
  fn_result : Looping.named;
  fn_struct : string;
  fn_strategy : strategy;
  fn_tree : case_tree;
}

type path = (int * int) list
type tag = User of string * path option | Anon | Aux of int
type binder = { b_tag : tag; b_type : term }
type scope = binder list                    (* innermost first *)

type generalized = {
  gn_seeds : int list;
  gn_tail : int list;
  gn_seed_types : term list;
  gn_tail_types : term list;
  gn_goal : term;
}

type prim = PVoid | PUnit | PBool

type split_var = {
  sv_name : string;
  sv_level : int;
  sv_path : path option;
  sv_desc : ind_desc;
  sv_prim : prim option;
  sv_params : term list;
  sv_indices : int list;
}

type split_info = { si_var : split_var; si_gen : generalized }

type elab =
  | ELeaf of scope * term * term list * term       (* scope, goal, values of the arguments, right side *)
  | ESplit of scope * term * split_info * (int * elab) list

val resolve_in : scope -> Looping.named -> (term, case_error) result
val generalize : scope -> term -> int list -> int list -> (generalized, case_error) result
val motive : generalized -> term
val prepare_split : signature -> scope -> term -> string -> int list -> (split_info, case_error) result

(* [elaborate_with sg extra hyp_tag g goal env t]: the root split with
   [extra] in its tail and its hypotheses tagged by [hyp_tag]. *)
val elaborate_with :
  signature -> int list -> (int -> tag) -> scope -> term -> term list -> case_tree -> (elab, case_error) result
val elaborate : signature -> scope -> term -> term list -> case_tree -> (elab, case_error) result
val start : fun_decl -> (scope * term * term list, case_error) result
val varying : fun_decl -> int list

(** {1 The compiler} *)

val access : term -> path -> term list -> term
val equations : string -> elab -> (term * term) list

(* The signature with the history and instances, the type, the body, and
   what [out] reads off the elaborated tree. *)
val compile_with :
  Elim_native.registrar -> (elab -> 'a) -> signature -> fun_decl -> (signature * term * term * 'a, failure) result
val compile_term :
  Elim_native.registrar -> signature -> fun_decl -> (signature * term * term * (term * term) list, failure) result
val compile : Elim_native.registrar -> signature -> fun_decl -> (signature, failure) result

val compile_checked : spec -> int -> signature -> fun_decl -> log * registration
val compile_all : spec -> int -> signature -> fun_decl list -> log * registration
