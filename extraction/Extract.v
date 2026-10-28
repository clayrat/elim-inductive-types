(** * Extraction driver

    Exports the kernel's checker and evaluator, algorithm 1 (the
    classification of declarations, the generator of eliminators and the
    registration of declarations, instances and δ-constants), algorithm 2
    (the history, the compiler of case trees and the names of the scopes
    of its equations), the declarations of the lecture (Data/) and its
    programs (Programs/) into generated/deptypes.ml.  The extract keeps
    the kernel's module name, so the kernel's printer (extraction/pretty.ml
    of the submodule, which make copies next to it) compiles against it
    unchanged; [observe] is extracted only for the observations it prints.
    As in the kernel, natural numbers are OCaml ints, booleans OCaml bools
    and names OCaml strings. *)

From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlNativeString.
From DepTypes.PTS Require Import Syntax Named Spec Signature Eval Check.
From DepTypes.Configs Require Import Finite Predicative.
From DepTypes.SystemU Require Import Encodings.
From DepTypes.MLTT Require Import Constants Families.
From IndTypes.Elim Require Import Decl Generate Declare.
From IndTypes.Data Require Import Nat Lists Tree W Primitives Positivity.
From IndTypes.Recursion Require Import Below CaseTree Compile.
From IndTypes.Programs Require Import Direct Half Append Rejected Copy.

Extraction Language OCaml.
Set Extraction Output Directory "generated".

(** Arithmetic on de Bruijn indices and levels, natively. *)
Extract Inlined Constant Init.Nat.add => "(+)".
Extract Inlined Constant Init.Nat.max => "max".
Extract Inlined Constant Init.Nat.eqb => "(=)".
Extract Inlined Constant Init.Nat.ltb => "(<)".
Extract Inlined Constant PeanoNat.Nat.add => "(+)".
Extract Inlined Constant PeanoNat.Nat.max => "max".
Extract Inlined Constant PeanoNat.Nat.eqb => "(=)".
Extract Inlined Constant PeanoNat.Nat.ltb => "(<)".

Extraction "deptypes.ml"
  term_eqb sort_eqb gref_eqb rename lift subst subst1 arrow times free_in map_sorts lookup
  apps spine_head spine_args pis lams vars
  sig_empty sig_add sig_type sig_delta ind_type ctor_type field_type elim_arity elim_view full_elim iota
  resolve resolve_ctx
  lambda_star system_u system_u_minus predicative pure_predicative u_to_univ
  classify normalize_trace normalize whnf convert
  infer check run_infer run_check
  observe
  classify_decl classify_decl_with
  motive_type method_type elim_type iota_rules
  declare declare_with declare_elim ensure_elim check_rule define declare_checked declare_bypassing define_checked run_registration
  registered refusal ensure_unit unit_at tt_at unit_name
  nat_desc elim_nat_ty double_body vec_desc w_desc
  raw_nat sg_nat0 raw_list list_desc raw_vec raw_tree tree_desc raw_w ind_w_run ind_false_run
  raw_void raw_unit raw_bool void_desc unit_desc bool_desc to_prim void_schema unit_schema bool_schema
  raw_negative raw_negative_bool raw_non_strict void_diagonal bool_diagonal sg_void sg_bool
  ensure_below below_name build_name recbelow_name
  generalize
  compile_checked compile_all named_equations
  prog_fuel num plus_fn pow_fn f_fn direct_run sg_direct
  half_fn even_fn half_run even_run sg_half sg_even unit_history_run
  append_fn plus2_fn sumv_fn sg_vec append_run sg_append
  pred_fn g_fn ack_fn len_fn sg_list iter_fn ack_ho_fn sg_ack
  copy_fn copy_run sg_copy.
