(** * Definitions the compiler rejects

    - [g (succ n) = g (pred n)] terminates but is rejected: [pred n] is
      not a path to a subterm, and the check is syntactic.
    - Ackermann's function as equations in two arguments is rejected for
      either choice of the structural argument: [ack (m + 1) n] does not
      decrease the first, [ack m (…)] not the second.  Nested
      higher-order structural recursion on m, as in the lecture on
      System T, does express it.
    - A recursion that changes a parameter, such as A in a recursion on
      [List A], is non-uniform and is rejected.

    The first two are refused at the call that is no path to a subterm:
    [CNotStructural]; a varying parameter at the root: [CParams]; a
    constant parameter changed in a call: [CConstantChanged].  Ackermann's
    function as higher-order structural recursion is compiled, as in the
    lecture on System T: [ack (succ m) = λn. iter (ack m) n] with
    [iter g zero = g 1] and [iter g (succ n) = g (iter g n)]. *)

From Stdlib Require Import String List Bool.
Import ListNotations.
From DepTypes.Common Require Import Result Traced.
From DepTypes.PTS Require Import Syntax Named Signature Eval Check.
From DepTypes.Configs Require Import Predicative.
From DepTypes.SystemU Require Import Looping.
From DepTypes.MLTT Require Import Constants.
From IndTypes.Elim Require Import Declare.
From IndTypes.Data Require Import Nat Lists.
From IndTypes.Recursion Require Import CaseTree Compile.
From IndTypes.Programs Require Import Direct.
Open Scope string_scope.
Open Scope nterm_scope.

Definition pred : nterm := NConst (Def "pred").
Definition g : nterm := NConst (Def "g").
Definition ack : nterm := NConst (Def "ack").
Definition iter : nterm := NConst (Def "iter").
Definition len : nterm := NConst (Def "len").

Definition refused_by (r : list (stage * list event) * registration) : option case_error :=
  match refusal r with Some (RCase e) => Some e | _ => None end.

Definition is_not_structural (e : option case_error) : bool :=
  match e with Some (CNotStructural _) => true | _ => false end.

Definition pred_fn : fun_decl := {|
  fn_name := "pred"; fn_args := [("n", Nat, Constant)]; fn_result := Nat; fn_struct := "n"; fn_strategy := Direct;
  fn_tree := Split "n" [("zero", [], Leaf zero); ("succ", ["k"], Leaf "k")] |}.

(** [g zero = zero], [g (succ n) = g (pred n)]: it terminates, but
    [pred n] is no path. *)
Definition g_fn : fun_decl := {|
  fn_name := "g"; fn_args := [("n", Nat, Constant)]; fn_result := Nat; fn_struct := "n"; fn_strategy := History;
  fn_tree := Split "n" [("zero", [], Leaf zero); ("succ", ["k"], Leaf (g (pred "k")))] |}.

(** Ackermann's equations, with the structural argument [x]; the other
    one varies. *)
Definition ack_fn (x : string) : fun_decl := {|
  fn_name := "ack";
  fn_args := [("m", Nat, if String.eqb x "m" then Constant else Varying);
              ("n", Nat, if String.eqb x "n" then Constant else Varying)];
  fn_result := Nat; fn_struct := x; fn_strategy := History;
  fn_tree := Split "m" [("zero", [], Leaf (succ "n"));
                        ("succ", ["k"], Split "n" [("zero", [], Leaf (ack "k" (succ zero)));
                                                    ("succ", ["l"], Leaf (ack "k" (ack (succ "k") "l")))])] |}.

(** The length of a list, [A] varying, or [A] changed in the call. *)
Definition len_fn (mk : mark) (A' : nterm) : fun_decl := {|
  fn_name := "len"; fn_args := [("A", Type@ 0, mk); ("xs", List "A", Constant)]; fn_result := Nat;
  fn_struct := "xs"; fn_strategy := History;
  fn_tree := Split "xs" [("nil", [], Leaf zero); ("cons", ["x"; "ys"], Leaf (succ (len A' "ys")))] |}.

Definition sg_list : signature := sg_of (declare_checked predicative 300 sg_direct raw_list [0]).

Example refusals :
  is_not_structural (refused_by (compile_all predicative prog_fuel sg_direct [pred_fn; g_fn])) &&
  is_not_structural (refused_by (compile_all predicative prog_fuel sg_direct [ack_fn "m"])) &&
  is_not_structural (refused_by (compile_all predicative prog_fuel sg_direct [ack_fn "n"])) = true /\
  refused_by (compile_all predicative prog_fuel sg_list [len_fn Varying "A"]) = Some (CParams "xs" "A") /\
  match refused_by (compile_all predicative prog_fuel sg_list [len_fn Constant (NConst (Ind "Nat"))]) with
  | Some (CConstantChanged "A" _) => True
  | _ => False
  end.
Proof. split; [ | split]; vm_compute; trivial. Qed.

(** The same [len] with [A] constant is accepted. *)
Example len_accepted : registered (compile_all predicative prog_fuel sg_list [len_fn Constant "A"]) <> None.
Proof. vm_compute. discriminate. Qed.

(** Higher-order structural recursion: [iter] on its second argument with
    [g] constant, [ack] on its only one, returning functions. *)
Definition iter_fn : fun_decl := {|
  fn_name := "iter"; fn_args := [("g", Nat ~> Nat, Constant); ("n", Nat, Constant)]; fn_result := Nat;
  fn_struct := "n"; fn_strategy := Direct;
  fn_tree := Split "n" [("zero", [], Leaf ("g" (succ zero))); ("succ", ["k"], Leaf ("g" (iter "g" "k")))] |}.

Definition ack_ho_fn : fun_decl := {|
  fn_name := "ack"; fn_args := [("m", Nat, Constant)]; fn_result := Nat ~> Nat;
  fn_struct := "m"; fn_strategy := Direct;
  fn_tree := Split "m" [("zero", [], Leaf (λ "n", succ "n")); ("succ", ["k"], Leaf (λ "n", iter (ack "k") "n"))] |}.

Definition sg_ack : signature := sg_of (compile_all predicative prog_fuel sg_direct [iter_fn; ack_ho_fn]).

Example ack_computes :
  map (fun '(m, n) => normalize sg_ack prog_fuel (build [] (ack (num m) (num n)))) [(0, 0); (1, 2); (2, 2)] =
  map (fun r => NormalForm (build [] (num r))) [1; 4; 7].
Proof. vm_compute. reflexivity. Qed.
