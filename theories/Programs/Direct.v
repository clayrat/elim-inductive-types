(** * The direct translation: [+], [pow], [f]

    Every recursive call on an immediate subterm becomes the induction
    hypothesis, which mechanizes the terms written by hand for ℕ:
    - addition, by recursion on the first argument;
    - [pow], with the motive [λ_. Type₀ : ℕ → Type₁]: large elimination;
    - [f], with the motive [λn. Πb:ℕ. ℕ^n]: the result type changes with
      n, which Church's iterator could not do, and the argument b that
      changes in the recursive call sits in the motive under Π.

    Each is compiled by [compile_checked] with the strategy [Direct], and
    its body is the term written by hand: the recursive call is the
    hypothesis of [succ].  [pow] needs [elimNat[1]], registered on the
    way; the defining equations hold by conversion. *)

From Stdlib Require Import String List Bool.
Import ListNotations.
From DepTypes.Common Require Import Result Traced.
From DepTypes.PTS Require Import Syntax Named Signature Eval Check.
From DepTypes.Configs Require Import Predicative.
From DepTypes.SystemU Require Import Looping.
From DepTypes.MLTT Require Import Constants.
From IndTypes.Elim Require Import Declare.
From IndTypes.Data Require Import Nat.
From IndTypes.Recursion Require Import CaseTree Compile.
Open Scope string_scope.
Open Scope nterm_scope.

Definition prog_fuel : nat := 1000.

Definition num (n : nat) : nterm := Nat.iter n succ zero.

(** Two named terms convert, their names free. *)
Definition converts (sg : signature) (names : list string) (t u : nterm) : bool :=
  match convert sg prog_fuel (build names t) (build names u) with ConvEqual _ => true | _ => false end.

Definition sg_of (r : list (stage * list event) * registration) : signature :=
  match registered r with Some sg => sg | None => ∅ end.

Definition plus : nterm := NConst (Def "plus").
Definition pow : nterm := NConst (Def "pow").
Definition f : nterm := NConst (Def "f").

(** [plus zero m = m], [plus (succ k) m = succ (plus k m)]. *)
Definition plus_fn : fun_decl := {|
  fn_name := "plus"; fn_args := [("n", Nat, Constant); ("m", Nat, Constant)]; fn_result := Nat;
  fn_struct := "n"; fn_strategy := Direct;
  fn_tree := Split "n" [("zero", [], Leaf "m"); ("succ", ["k"], Leaf (succ (plus "k" "m")))] |}.

(** [pow n = ℕ^n]: [pow zero = Unit], [pow (succ k) = ℕ × pow k]. *)
Definition pow_fn : fun_decl := {|
  fn_name := "pow"; fn_args := [("n", Nat, Constant)]; fn_result := Type@ 0;
  fn_struct := "n"; fn_strategy := Direct;
  fn_tree := Split "n" [("zero", [], Leaf NUnit); ("succ", ["k"], Leaf (Nat ⨯ pow "k"))] |}.

(** [f n b = ⟨b, b + 1, …⟩ : ℕ^n]: [f zero b = tt],
    [f (succ k) b = ⟨b, f k (succ b)⟩]. *)
Definition f_fn : fun_decl := {|
  fn_name := "f"; fn_args := [("n", Nat, Constant); ("b", Nat, Varying)]; fn_result := pow "n";
  fn_struct := "n"; fn_strategy := Direct;
  fn_tree := Split "n" [("zero", [], Leaf NTt); ("succ", ["k"], Leaf ⟨ "b", f "k" (succ "b") ⟩)] |}.

Definition direct_run : list (stage * list event) * registration :=
  compile_all predicative prog_fuel sg_nat0 [plus_fn; pow_fn; f_fn].

Definition sg_direct : signature := sg_of direct_run.

(** The motive of each recursion, [elimNat[1]] for [pow], each body and
    every equation. *)
Example direct_stages :
  map fst (fst direct_run) =
  [AtMotive "plus" "n"; AtDefType "plus"; AtDefBody "plus"; AtEquation "plus" 0; AtEquation "plus" 1;
   AtMotive "pow" "n"; AtElimType "Nat" 1; AtRuleLhs "Nat" 1 "zero"; AtRuleRhs "Nat" 1 "zero";
   AtRuleLhs "Nat" 1 "succ"; AtRuleRhs "Nat" 1 "succ"; AtDefType "pow"; AtDefBody "pow";
   AtEquation "pow" 0; AtEquation "pow" 1;
   AtMotive "f" "n"; AtDefType "f"; AtDefBody "f"; AtEquation "f" 0; AtEquation "f" 1].
Proof. vm_compute. reflexivity. Qed.

(** The bodies: the motive [λ_. ℕ] with [m] outside it, the motive
    [λ_. Type₀] of large elimination, and the motive [λn. Πb:ℕ. ℕ^n] with
    the varying [b] under Π, the hypothesis applied to [succ b]. *)
Example direct_bodies :
  option_map snd (sig_def sg_direct "plus") =
    Some (build [] (λ "n", λ "m", NConst (Elim "Nat" 0) (λ "_", Nat) "m" (λ "k", λ "ih", succ "ih") "n")) /\
  option_map snd (sig_def sg_direct "pow") =
    Some (build [] (λ "n", NConst (Elim "Nat" 1) (λ "_", Type@ 0) NUnit (λ "k", λ "ih", Nat ⨯ "ih") "n")) /\
  option_map snd (sig_def sg_direct "f") =
    Some (build [] (λ "n", λ "b", NConst (Elim "Nat" 0) (λ "n", Π "b" : Nat, pow "n") (λ "b", NTt)
                     (λ "k", λ "ih", λ "b", ⟨ "b", "ih" (succ "b") ⟩) "n" "b")).
Proof. repeat split; vm_compute; reflexivity. Qed.

Example direct_computes :
  normalize sg_direct prog_fuel (build [] (plus (num 2) (num 3))) = NormalForm (build [] (num 5)) /\
  normalize sg_direct prog_fuel (build [] (f (num 2) (num 5))) =
    NormalForm (build [] ⟨ num 5, ⟨ num 6, NTt ⟩ ⟩).
Proof. split; vm_compute; reflexivity. Qed.

(** The equations by conversion, the pattern variables free. *)
Example direct_equations :
  converts sg_direct ["m"; "k"] (plus (succ "k") "m") (succ (plus "k" "m")) &&
  converts sg_direct ["k"] (pow (succ "k")) (Nat ⨯ pow "k") &&
  converts sg_direct ["b"; "k"] (f (succ "k") "b") ⟨ "b", f "k" (succ "b") ⟩ = true.
Proof. vm_compute. reflexivity. Qed.
