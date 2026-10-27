(** * [copy] on W: a call on a functional recursive field

      copy A B (sup a f) = sup a (λb. copy A B (f b))

    The recursive call [copy A B (f b)] sits under the binder [b] of the
    right side, on the child [f b] at the position [b]: the subterm [f]
    has the path of its field and one argument, the position.  The direct
    translation turns the call into the hypothesis at [b], [h b]; the
    history into [fst (t b)], where the table [t : Πb:B a. P (f b) ×
    Below_P (f b)] is itself a function.  Both compile over the signature
    of ℕ_W and its recursor (Data/W.v), and each equation holds by
    conversion.

    [copy] is the identity only extensionally.  On ℕ_W [copy (succ_W n) ≡
    succ_W (copy n)]: [(λ_. n) b] reduces to [n], and the binder [b] goes
    unused.  But [copy zero_W] is [sup false (λb. copy (elimVoid _ b))], a
    node whose child is stuck on [elimVoid _ b], and not [zero_W]: the
    branch of zero of the refused transfer of induction again.  The two
    strategies get stuck there in different terms, so [copy zero_W] and
    [copy_h zero_W] do not convert either.  The recursor never looks at
    the children of a leaf, and through it a copy is invisible: the parity
    of a copy of three is [true]. *)

From Stdlib Require Import String List Bool.
Import ListNotations.
From DepTypes.Common Require Import Result Traced.
From DepTypes.PTS Require Import Syntax Named Signature Eval Check.
From DepTypes.Configs Require Import Predicative.
From DepTypes.SystemU Require Import Looping.
From DepTypes.MLTT Require Import Families.
From IndTypes.Elim Require Import Declare.
From IndTypes.Data Require Import W.
From IndTypes.Recursion Require Import CaseTree Compile.
From IndTypes.Programs Require Import Direct.
Open Scope string_scope.
Open Scope nterm_scope.

Definition copy : nterm := NConst (Def "copy").
Definition copy_h : nterm := NConst (Def "copy_h").
Definition Below_W : nterm := NConst (Def "Below_W_0").
Definition recBelow_W : nterm := NConst (Def "recBelow_W_0").

Definition copy_fn (name : string) (st : strategy) : fun_decl := {|
  fn_name := name;
  fn_args := [("A", Type@ 0, Constant); ("B", "A" ~> Type@ 0, Constant); ("w", W "A" "B", Constant)];
  fn_result := W "A" "B"; fn_struct := "w"; fn_strategy := st;
  fn_tree := Split "w" [("sup", ["a"; "f"],
                         Leaf (sup "A" "B" "a" (λ "b", NConst (Def name) "A" "B" ("f" "b"))))] |}.

Definition copy_run : list (stage * list event) * registration :=
  compile_all predicative prog_fuel sg_rec_w [copy_fn "copy" Direct; copy_fn "copy_h" History].

Definition sg_copy : signature := sg_of copy_run.

(** [copy] directly; [copy_h] through the history of W, with [elimW[1]]
    for [Below]. *)
Example copy_stages :
  map fst (fst copy_run) =
  [AtMotive "copy" "w"; AtDefType "copy"; AtDefBody "copy"; AtEquation "copy" 0;
   AtMotive "copy_h" "w"; AtElimType "W" 1; AtRuleLhs "W" 1 "sup"; AtRuleRhs "W" 1 "sup";
   AtDefType "Below_W_0"; AtDefBody "Below_W_0"; AtDefType "build_W_0"; AtDefBody "build_W_0";
   AtDefType "recBelow_W_0"; AtDefBody "recBelow_W_0";
   AtMotive "copy_h" "w"; AtDefType "copy_h"; AtDefBody "copy_h"; AtEquation "copy_h" 0].
Proof. vm_compute. reflexivity. Qed.

(** The call becomes the hypothesis at the position, [h b]; in the
    history the step splits [v] with the table [t] generalized, and the
    call becomes [fst (t b)]. *)
Definition copy_direct_body : nterm :=
  λ "A", λ "B", λ "w",
    elim_w "A" "B" (λ "_", W "A" "B") (λ "a", λ "f", λ "h", sup "A" "B" "a" (λ "b", "h" "b")) "w".

Definition copy_history_body : nterm :=
  λ "A", λ "B", λ "w",
    recBelow_W "A" "B" (λ "_", W "A" "B")
      (λ "v", λ "t",
         elim_w "A" "B" (λ "u", Below_W "A" "B" (λ "_", W "A" "B") "u" ~> W "A" "B")
           (λ "a", λ "f", λ "h", λ "t", sup "A" "B" "a" (λ "b", NFst ("t" "b"))) "v" "t")
      "w".

Example copy_bodies :
  option_map snd (sig_def sg_copy "copy") = Some (build [] copy_direct_body) /\
  option_map snd (sig_def sg_copy "copy_h") = Some (build [] copy_history_body).
Proof. split; vm_compute; reflexivity. Qed.

(** The equation for an open node, in both strategies; the copy of a node
    is another node, not the node itself. *)
Example copy_equations :
  converts sg_copy ["A"; "B"; "a"; "f"]
    (copy "A" "B" (sup "A" "B" "a" "f")) (sup "A" "B" "a" (λ "b", copy "A" "B" ("f" "b"))) &&
  converts sg_copy ["A"; "B"; "a"; "f"]
    (copy_h "A" "B" (sup "A" "B" "a" "f")) (sup "A" "B" "a" (λ "b", copy_h "A" "B" ("f" "b"))) &&
  negb (converts sg_copy ["A"; "B"; "a"; "f"] (copy "A" "B" (sup "A" "B" "a" "f")) (sup "A" "B" "a" "f"))
  = true.
Proof. vm_compute. reflexivity. Qed.

(** On ℕ_W: the successor commutes with the copy, zero does not survive
    it, and neither does one. *)
Definition copy_W (cp w : nterm) : nterm := cp NBool IsTrue w.

Example copy_nat_w :
  converts sg_copy ["n"] (copy_W copy (succ_W "n")) (succ_W (copy_W copy "n")) &&
  converts sg_copy ["n"] (copy_W copy_h (succ_W "n")) (succ_W (copy_W copy_h "n")) &&
  converts sg_copy [] (copy_W copy zero_W) (sup NBool IsTrue NFalse (λ "b", copy_W copy (no_child "b"))) &&
  converts sg_copy [] (copy_W copy_h zero_W) (sup NBool IsTrue NFalse (λ "b", copy_W copy_h (no_child "b"))) &&
  negb (converts sg_copy [] (copy_W copy zero_W) zero_W) &&
  negb (converts sg_copy [] (copy_W copy zero_W) (copy_W copy_h zero_W)) &&
  negb (converts sg_copy [] (copy_W copy (succ_W zero_W)) (succ_W zero_W)) = true.
Proof. vm_compute. reflexivity. Qed.

(** Through the recursor a copy is invisible. *)
Example copy_parity :
  snd (run_check predicative sg_copy prog_fuel [] (build [] (copy_W copy three_W)) (build [] Nat_W))
  = Accepted tt /\
  normalize sg_copy prog_fuel (build [] (parity_W (copy_W copy three_W))) = NormalForm BTrue /\
  normalize sg_copy prog_fuel (build [] (parity_W (copy_W copy_h three_W))) = NormalForm BTrue.
Proof. split; [ | split]; vm_compute; reflexivity. Qed.
