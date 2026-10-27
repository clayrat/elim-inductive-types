(** * [append] and dependent splits of vectors

    [append : Vec A n → Vec A m → Vec A (n + m)] by recursion on the first
    vector, with the motive [λn xs. Vec A (n + m)] and [m], [ys]
    constant.  The history at level ℓ = max i j:

      Below P 0        nil          = Unit_ℓ
      Below P (succ n) (cons x xs)  = P n xs × Below P n xs

    The recursion is one step back: the access [table.1] is the
    hypothesis of the direct translation, and the history only shows how
    the indices enter its type.  The branch [nil] expects [Vec A (0 + m)]
    and [cons] [Vec A (succ n + m)]; with addition by recursion on its
    first argument both reduce to [Vec A m] and [Vec A (succ (n + m))].
    With addition on the second argument [0 + m] stays neutral, and the
    branch [nil] is rejected on [Vec A m ≡ Vec A (0 + m)]: the equality of
    indices is propositional there, not definitional.

    Also: a split of a vector under a hypothesis that depends on its
    length but not on the vector itself, which checks the generalization
    of the index and of the dependent tail of the context: in
    [sumv n v (w : ℕ^n)] the constant [w] enters the motive
    [λn v. Πw:ℕ^n. ℕ] by its dependency, and the recursive call passes it
    [snd w].

    Both through the history, over ℕ, [plus], [pow] (Programs.Direct) and
    vectors. *)

From Stdlib Require Import String List Bool.
Import ListNotations.
From DepTypes.Common Require Import Result Traced.
From DepTypes.PTS Require Import Syntax Named Signature Eval Check.
From DepTypes.Configs Require Import Predicative.
From DepTypes.SystemU Require Import Looping.
From DepTypes.MLTT Require Import Constants Families.
From IndTypes.Elim Require Import Declare.
From IndTypes.Data Require Import Nat Lists.
From IndTypes.Recursion Require Import CaseTree Compile.
From IndTypes.Programs Require Import Direct.
Open Scope string_scope.
Open Scope nterm_scope.

Definition append : nterm := NConst (Def "append").
Definition plus2 : nterm := NConst (Def "plus2").
Definition sumv : nterm := NConst (Def "sumv").

(** [append A n m xs ys : Vec A (n + m)], the sum written with [add]. *)
Definition append_fn (name : string) (add : nterm) : fun_decl := {|
  fn_name := name;
  fn_args := [("A", Type@ 0, Constant); ("n", Nat, Constant); ("m", Nat, Constant);
              ("xs", Vec "A" "n", Constant); ("ys", Vec "A" "m", Constant)];
  fn_result := Vec "A" (add "n" "m"); fn_struct := "xs"; fn_strategy := History;
  fn_tree := Split "xs" [("nil", [], Leaf "ys");
                         ("cons", ["k"; "x"; "xs'"],
                          Leaf (vcons "A" (add "k" "m") "x" (NConst (Def name) "A" "k" "m" "xs'" "ys")))] |}.

(** Addition by recursion on the second argument. *)
Definition plus2_fn : fun_decl := {|
  fn_name := "plus2"; fn_args := [("n", Nat, Constant); ("m", Nat, Constant)]; fn_result := Nat;
  fn_struct := "m"; fn_strategy := Direct;
  fn_tree := Split "m" [("zero", [], Leaf "n"); ("succ", ["k"], Leaf (succ (plus2 "n" "k")))] |}.

(** The sum of a vector and of a tuple of its length. *)
Definition sumv_fn : fun_decl := {|
  fn_name := "sumv"; fn_args := [("n", Nat, Constant); ("v", Vec Nat "n", Constant); ("w", pow "n", Constant)];
  fn_result := Nat; fn_struct := "v"; fn_strategy := History;
  fn_tree := Split "v" [("nil", [], Leaf zero);
                        ("cons", ["k"; "x"; "v'"], Leaf (plus "x" (plus (NFst "w") (sumv "k" "v'" (NSnd "w")))))] |}.

Definition sg_vec : signature := sg_of (declare_checked predicative 300 sg_direct raw_vec [0]).

Definition append_run : list (stage * list event) * registration :=
  compile_all predicative prog_fuel sg_vec [append_fn "append" plus; sumv_fn].

Definition sg_append : signature := sg_of append_run.

(** The history of vectors, with [elimVec[1]]; then each function. *)
Example append_stages :
  map fst (fst append_run) =
  [AtMotive "append" "xs"; AtElimType "Vec" 1; AtRuleLhs "Vec" 1 "nil"; AtRuleRhs "Vec" 1 "nil";
   AtRuleLhs "Vec" 1 "cons"; AtRuleRhs "Vec" 1 "cons";
   AtDefType "Below_Vec_0"; AtDefBody "Below_Vec_0"; AtDefType "build_Vec_0"; AtDefBody "build_Vec_0";
   AtDefType "recBelow_Vec_0"; AtDefBody "recBelow_Vec_0";
   AtMotive "append" "xs"; AtDefType "append"; AtDefBody "append"; AtEquation "append" 0; AtEquation "append" 1;
   AtMotive "sumv" "v"; AtMotive "sumv" "v"; AtDefType "sumv"; AtDefBody "sumv";
   AtEquation "sumv" 0; AtEquation "sumv" 1].
Proof. vm_compute. reflexivity. Qed.

Definition vec (xs : list nat) : nterm :=
  fold_right (fun '(i, x) v => vcons Nat (num i) (num x) v) (vnil Nat)
    (combine (rev (seq 0 (length xs))) xs).

Example append_computes :
  normalize sg_append prog_fuel (build [] (append Nat (num 1) (num 2) (vec [7]) (vec [8; 9]))) =
    NormalForm (build [] (vec [7; 8; 9])) /\
  normalize sg_append prog_fuel (build [] (sumv (num 2) (vec [1; 2]) ⟨ num 3, ⟨ num 4, NTt ⟩ ⟩)) =
    NormalForm (build [] (num 10)).
Proof. split; vm_compute; reflexivity. Qed.

Example append_equations :
  converts sg_append ["A"; "m"; "ys"] (append "A" zero "m" (vnil "A") "ys") "ys" &&
  converts sg_append ["A"; "n"; "m"; "x"; "xs"; "ys"]
    (append "A" (succ "n") "m" (vcons "A" "n" "x" "xs") "ys")
    (vcons "A" (plus "n" "m") "x" (append "A" "n" "m" "xs" "ys")) &&
  converts sg_append ["n"; "x"; "v"; "w"]
    (sumv (succ "n") (vcons Nat "n" "x" "v") "w") (plus "x" (plus (NFst "w") (sumv "n" "v" (NSnd "w")))) = true.
Proof. vm_compute. reflexivity. Qed.

(** The motive of [sumv]: [w] depends on the length, so it is under Π. *)
Example sumv_motive :
  match option_map snd (sig_def sg_append "sumv") with
  | Some (Lam (Lam (Lam (App (App (App (App (App (App (Const (Def "recBelow_Vec_0")) A) P) _) _) _) _)))) =>
      A = Const (Ind "Nat") /\ P = build [] (λ "n", λ "v", Π "w" : pow "n", Nat)
  | _ => False
  end.
Proof. vm_compute. split; reflexivity. Qed.

(** With addition on the second argument [0 + m] stays neutral: the branch
    [nil] is refused on [Vec A m ≡ Vec A (0 + m)]. *)
Example append_nil_refused :
  match refusal (compile_all predicative prog_fuel sg_vec [plus2_fn; append_fn "append2" plus2]) with
  | Some (RRejected (AtDefBody "append2")
            (EMismatch _ (App (App (Const (Ind "Vec")) _) (App (App (Const (Def "plus2")) (Const (Ctor "Nat" "zero"))) _))
                         (App (App (Const (Ind "Vec")) _) _))) => True
  | _ => False
  end.
Proof. vm_compute. trivial. Qed.
