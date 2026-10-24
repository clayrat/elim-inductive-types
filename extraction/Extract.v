(** * Extraction driver

    Exports the kernel's checker and evaluator and, as they appear, the
    generator of eliminators, the compiler of structural recursion and
    the lecture examples into generated/deptypes.ml.  The extract keeps
    the kernel's module name, so the kernel's printer (extraction/pretty.ml
    of the submodule, which make copies next to it) compiles against it
    unchanged; [observe] is extracted only for the observations it prints.
    As in the kernel, natural numbers are OCaml ints, booleans OCaml bools
    and names OCaml strings. *)

From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlNativeString.
From DepTypes.PTS Require Import Syntax Named Spec Signature Eval Check.
From DepTypes.Configs Require Import Finite Predicative.
From DepTypes.SystemU Require Import Encodings.

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
  observe.
