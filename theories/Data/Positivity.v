(** * Why the restrictions: two inadmissible declarations

    - The negative field [mk : (D → Void) → D] is rejected.  Accepted in
      the bypass mode, one case analysis suffices for a closed proof of
      Void, without [fix] and without impredicativity, like ΠA:∗. A of
      L₀: [unmk (mk g) := g], [δ := λd. unmk d d], [δ (mk δ) : Void].
      With Bool in place of Void it is Cantor's diagonal:
      [δ := λd. not (unmk d d)] gives [δ (mk δ) ↝ not (δ (mk δ))], and
      checking [tt : IsTrue (δ (mk δ))] ends [Undecided]: the negative
      field also breaks the decidability of type checking.
    - The non-strictly positive field [mk : ((D → Bool) → Bool) → D] is
      rejected: D occurs positively, but the field is not of the form
      [Πȳ. D v̄], so the generator has no hypothesis for it.  No
      contradiction is claimed for it in this predicative kernel without
      Prop: the paradox of Coquand and Paulin-Mohring for
      [((D → Prop) → Prop) → D] needs an impredicative Prop and belongs
      to the next lecture.

    Strict positivity is checked on the declaration (algorithm 1),
    structural decrease on the program (algorithm 2); the kernel sees
    only eliminators and checks no termination itself.

    Both rejections with their diagnostics; in the bypass mode, which
    classifies the offending field as non-recursive, the declaration is
    registered with its eliminator, [δ (mk δ) : Void] is accepted, and
    with Bool the check of [tt : IsTrue (δ (mk δ))] ends [Undecided]. *)

From Stdlib Require Import String List.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.Common Require Import Traced.
From DepTypes.PTS Require Import Syntax Named Signature Eval Check.
From DepTypes.Configs Require Import Predicative.
From DepTypes.SystemU Require Import Looping.
From IndTypes.Elim Require Import Decl Declare.

Open Scope string_scope.
Open Scope nterm_scope.

Definition D : nterm := NConst (Ind "D").

Definition with_mk (field : nterm) : raw_decl := {|
  rd_name := "D"; rd_params := []; rd_indices := []; rd_level := 0;
  rd_ctors := [mk_raw_ctor "mk" (build [] (field ~> D))] |}.

Definition bypassed (field : nterm) : ind_desc := {|
  ind_name := "D"; ind_params := []; ind_indices := []; ind_level := 0;
  ind_ctors := [{| ctor_name := "mk"; ctor_fields := [FArg (build [] field)]; ctor_indices := [] |}] |}.

(** ** The negative field *)

Definition raw_negative : raw_decl := with_mk (D ~> NVoid).
Definition raw_negative_bool : raw_decl := with_mk (D ~> NBool).

Example negative_rejected :
  classify_decl raw_negative = Err (ENegative "mk" 0 (build [] (D ~> NVoid))) /\
  classify_decl raw_negative_bool = Err (ENegative "mk" 0 (build [] (D ~> NBool))).
Proof. split; vm_compute; reflexivity. Qed.

Example negative_bypassed :
  classify_decl_with true raw_negative = Ok (bypassed (D ~> NVoid)) /\
  classify_decl_with true raw_negative_bool = Ok (bypassed (D ~> NBool)).
Proof. split; vm_compute; reflexivity. Qed.

(** ** The non-strictly positive field *)

Definition raw_non_strict : raw_decl := with_mk ((D ~> NBool) ~> NBool).

Example non_strict_rejected :
  classify_decl raw_non_strict = Err (ENonStrict "mk" 0 (build [] ((D ~> NBool) ~> NBool))).
Proof. vm_compute. reflexivity. Qed.

Example non_strict_bypassed :
  classify_decl_with true raw_non_strict = Ok (bypassed ((D ~> NBool) ~> NBool)).
Proof. vm_compute. reflexivity. Qed.

(** ** The diagonal, in the bypass mode *)

Definition pos_fuel : nat := 300.

Definition mk : nterm := NConst (Ctor "D" "mk").
Definition elim_d : nterm := NConst (Elim "D" 0).
Definition unmk : nterm := NConst (Def "unmk").
Definition delta : nterm := NConst (Def "delta").

(** [D] with [mk : (D → B) → D] accepted in the bypass mode, its
    eliminator, [unmk (mk g) := g] and the diagonal [delta], each checked
    when registered. *)
Definition with_diagonal (B diagonal : nterm) : list (stage * list event) * registration :=
  run_registration (
    let! s1 := declare_with predicative pos_fuel true ∅ (with_mk (D ~> B)) [0] in
    let! s2 := define predicative pos_fuel s1 "unmk" (build [] (D ~> D ~> B))
                 (build [] (λ "d", elim_d ((λ "_", D ~> B) ∷ (D ~> Type@ 0)) (λ "g", "g") "d")) in
    define predicative pos_fuel s2 "delta" (build [] (D ~> B)) (build [] diagonal)).

Definition sg_of (r : list (stage * list event) * registration) : signature :=
  match registered r with Some sg => sg | None => ∅ end.

Definition sg_void : signature := sg_of (with_diagonal NVoid (λ "d", unmk "d" "d")).

(** A closed proof of Void, by one case analysis: no [fix], no
    impredicativity.  Its normalization does not end. *)
Example delta_proves_void :
  snd (run_check predicative sg_void pos_fuel [] (build [] (delta (mk delta))) Void) = Accepted tt /\
  match normalize sg_void 50 (build [] (delta (mk delta))) with OutOfFuel _ => True | _ => False end.
Proof. split; vm_compute; [reflexivity | trivial]. Qed.

(** Cantor's diagonal: [delta (mk delta) ↝ not (delta (mk delta))], and
    checking [tt : IsTrue (delta (mk delta))] does not end. *)
Definition bnot (x : nterm) : nterm := NElimBool ((λ "_", NBool) ∷ (NBool ~> Type@ 0)) NFalse NTrue x.
Definition is_true (b : nterm) : nterm := NElimBool ((λ "_", Type@ 0) ∷ (NBool ~> Type@ 1)) NUnit NVoid b.
Definition sg_bool : signature := sg_of (with_diagonal NBool (λ "d", bnot (unmk "d" "d"))).

Example diagonal_undecided :
  registered (with_diagonal NBool (λ "d", bnot (unmk "d" "d"))) <> None /\
  snd (run_check predicative sg_bool pos_fuel [] Tt (build [] (is_true (delta (mk delta))))) = Undecided Tt.
Proof. split; vm_compute; [discriminate | reflexivity]. Qed.

(** Without the bypass the declaration is refused. *)
Example negative_refused :
  refusal (declare_checked predicative pos_fuel ∅ raw_negative [0])
  = Some (RClassify (ENegative "mk" 0 (build [] (D ~> NVoid)))).
Proof. vm_compute. reflexivity. Qed.
