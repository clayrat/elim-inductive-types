(** * Recursion two steps back: [half] and [isEven]

      half 0       = 0
      half 1       = 0
      half (n + 2) = succ (half n)

    In the branch [half (succ (succ n))] the history has the type
    [P (succ n) × (P n × Below P n)], and [half n] becomes [table.2.1].

    [isEven] is the same recursion returning a type: the motive
    [λ_. Type₀ : ℕ → Type₁], so j = ℓ = 1, the empty history is
    [Unit_1], [Below] goes through [elimNat[2]] and [build] through
    [elimNat[1]].  [isEven] itself returns the primitive [Unit] and
    [Void] of [Type₀], and [tt : isEven 4] is accepted by computation.
    Replacing [Unit_1] by the primitive [Unit : Type₀] in the empty
    history is rejected: there is no cumulativity.

    Both are compiled through the history.  The direct translation
    refuses [half]: its call is two fields down. *)

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
From IndTypes.Programs Require Import Direct.
Open Scope string_scope.
Open Scope nterm_scope.

Definition half : nterm := NConst (Def "half").
Definition isEven : nterm := NConst (Def "isEven").

Definition half_fn (s : strategy) : fun_decl := {|
  fn_name := "half"; fn_args := [("n", Nat, Constant)]; fn_result := Nat;
  fn_struct := "n"; fn_strategy := s;
  fn_tree := Split "n" [("zero", [], Leaf zero);
                        ("succ", ["m"], Split "m" [("zero", [], Leaf zero);
                                                    ("succ", ["k"], Leaf (succ (half "k")))])] |}.

Definition even_fn : fun_decl := {|
  fn_name := "isEven"; fn_args := [("n", Nat, Constant)]; fn_result := Type@ 0;
  fn_struct := "n"; fn_strategy := History;
  fn_tree := Split "n" [("zero", [], Leaf NUnit);
                        ("succ", ["m"], Split "m" [("zero", [], Leaf NVoid);
                                                    ("succ", ["k"], Leaf (isEven "k"))])] |}.

Definition half_run : list (stage * list event) * registration :=
  compile_all predicative prog_fuel sg_nat0 [half_fn History].

Definition sg_half : signature := sg_of half_run.

(** The history of ℕ for motives in [Type₀] first, with [elimNat[1]] for
    [Below]; then the motive of the recursion, that of the split of [m],
    the body and the three equations. *)
Example half_stages :
  map fst (fst half_run) =
  [AtMotive "half" "n"; AtElimType "Nat" 1; AtRuleLhs "Nat" 1 "zero"; AtRuleRhs "Nat" 1 "zero";
   AtRuleLhs "Nat" 1 "succ"; AtRuleRhs "Nat" 1 "succ";
   AtDefType "Below_Nat_0"; AtDefBody "Below_Nat_0"; AtDefType "build_Nat_0"; AtDefBody "build_Nat_0";
   AtDefType "recBelow_Nat_0"; AtDefBody "recBelow_Nat_0";
   AtMotive "half" "n"; AtMotive "half" "m"; AtDefType "half"; AtDefBody "half";
   AtEquation "half" 0; AtEquation "half" 1; AtEquation "half" 2].
Proof. vm_compute. reflexivity. Qed.

(** [recBelow (λ_. ℕ) step n]: each split generalizes the history [t], and
    in the branch [succ (succ k)] the call [half k] is [fst (snd t)]. *)
Example half_body :
  option_map snd (sig_def sg_half "half") =
    Some (build [] (λ "n", NConst (Def "recBelow_Nat_0") (λ "_", Nat)
      (λ "n", λ "t",
         NConst (Elim "Nat" 0) (λ "m", Π "t" : NConst (Def "Below_Nat_0") (λ "_", Nat) "m", Nat)
           (λ "t", zero)
           (λ "m", λ "ih", λ "t",
              NConst (Elim "Nat" 0) (λ "k", Π "t" : NConst (Def "Below_Nat_0") (λ "_", Nat) (succ "k"), Nat)
                (λ "t", zero)
                (λ "k", λ "ih", λ "t", succ (NFst (NSnd "t")))
                "m" "t")
           "n" "t")
      "n")).
Proof. vm_compute. reflexivity. Qed.

Example half_computes :
  map (fun n => normalize sg_half prog_fuel (build [] (half (num n)))) [0; 1; 4; 5] =
  map (fun n => NormalForm (build [] (num n))) [0; 0; 2; 2] /\
  converts sg_half ["k"] (half (succ (succ "k"))) (succ (half "k")) = true.
Proof. split; vm_compute; reflexivity. Qed.

(** Through the hypothesis alone, the call on [k] has no access. *)
Example half_direct_refused :
  match refusal (compile_all predicative prog_fuel sg_nat0 [half_fn Direct]) with
  | Some (RCase (CNotImmediate _)) => True
  | _ => False
  end.
Proof. vm_compute. trivial. Qed.

(** [isEven]: the motive [λ_. Type₀] has its results in [Type₁], so the
    history needs [Unit_1], [elimNat[2]] for [Below] and [elimNat[1]] for
    [build]. *)
Definition even_run : list (stage * list event) * registration :=
  compile_all predicative prog_fuel sg_nat0 [even_fn].

Definition sg_even : signature := sg_of even_run.

Example even_stages :
  map fst (fst even_run) =
  [AtMotive "isEven" "n"; AtIndType "Unit_1"; AtCtorType "Unit_1" "tt_1";
   AtElimType "Nat" 2; AtRuleLhs "Nat" 2 "zero"; AtRuleRhs "Nat" 2 "zero";
   AtRuleLhs "Nat" 2 "succ"; AtRuleRhs "Nat" 2 "succ";
   AtElimType "Nat" 1; AtRuleLhs "Nat" 1 "zero"; AtRuleRhs "Nat" 1 "zero";
   AtRuleLhs "Nat" 1 "succ"; AtRuleRhs "Nat" 1 "succ";
   AtDefType "Below_Nat_1"; AtDefBody "Below_Nat_1"; AtDefType "build_Nat_1"; AtDefBody "build_Nat_1";
   AtDefType "recBelow_Nat_1"; AtDefBody "recBelow_Nat_1";
   AtMotive "isEven" "n"; AtMotive "isEven" "m"; AtDefType "isEven"; AtDefBody "isEven";
   AtEquation "isEven" 0; AtEquation "isEven" 1; AtEquation "isEven" 2].
Proof. vm_compute. reflexivity. Qed.

(** [isEven] returns the primitive [Unit] and [Void] of [Type₀]: [tt] is
    accepted against [isEven 4] by computation, not against
    [isEven 3]. *)
Example even_computes :
  snd (run_check predicative sg_even prog_fuel [] Tt (build [] (isEven (num 4)))) = Accepted tt /\
  snd (run_check predicative sg_even prog_fuel [] Tt (build [] (isEven (num 3))))
    = Rejected (EMismatch Tt (build [] (isEven (num 3))) Unit) /\
  converts sg_even ["k"] (isEven (succ (succ "k"))) (isEven "k") = true.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** The primitive [Unit : Type₀] does not stand for [Unit_1] in the empty
    history: Tests.history_needs_unit_1. *)
