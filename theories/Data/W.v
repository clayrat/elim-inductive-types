(** * W-types

      data W (A : Type_i) (B : A → Type_i) : Type_i where
        sup : Π(a : A). (B a → W A B) → W A B

    A declaration with a functional recursive field, one more input of
    algorithm 1, declared at i = 0.  The label fixes the type of the
    positions of the children, and the function maps each position to a
    subtree.  The method of [elim_W[j]] gets [a : A], [f : B a → W] and
    [h : Πb:B a. P (f b)]: generalized structural induction.  The history
    has one component, [Below_P (sup a f) := Πb:B a. (P (f b) ×
    Below_P (f b))], itself a function rather than a finite table.

    ℕ_W: labels Bool, positions [B b := elimBool (λ_. Type₀) Unit Void b]
    ([IsTrue] of lecture 6); [zero_W := sup false (λv. elimVoid _
    v)], [succ_W n := sup true (λ_. n)]; one step of the eliminator on
    [succ_W n]; the recursor with a constant motive computes on canonical
    terms.

    The direct transfer of dependent induction to ℕ_W through the
    W-eliminator fails on conversion in this kernel.  In the branch
    [false] the method must give [P (sup false f)] for an arbitrary
    [f : Void → ℕ_W] but has only [P zero_W]; in the branch [true] it
    gives [P (sup true (λ_. f tt))] for [P (sup true f)], which η for Π
    and Unit would fix, though not the branch of zero.  The trace of this
    rejection is no proof that the principle is underivable.

    So far: the declaration, whose classification is the description of
    W written by hand in the kernel (MLTT/Families.v): the field [f] is
    recursive with one position, of the type [B a].

    Generated: its eliminator, the kernel's hand-written [elimW[0]].

    Registered by [declare_checked], as the kernel's hand-written entries.

    Planned: ℕ_W and its computation, the rejected transfer. *)

From Stdlib Require Import String List.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Named Signature Check.
From DepTypes.Configs Require Import Predicative.
From DepTypes.SystemU Require Import Looping.
From DepTypes.MLTT Require Import Families.
From IndTypes.Elim Require Import Decl Generate Declare.

Open Scope string_scope.
Open Scope nterm_scope.

Definition raw_w : raw_decl := {|
  rd_name := "W"; rd_params := [Srt (Univ 0); build ["A"] ("A" ~> Type@ 0)]; rd_indices := [];
  rd_level := 0;
  rd_ctors := [mk_raw_ctor "sup" (build ["B"; "A"] (Π "a" : "A", ("B" "a" ~> W "A" "B") ~> W "A" "B"))] |}.

Example w_classified : classify_decl raw_w = Ok w_desc.
Proof. vm_compute. reflexivity. Qed.

Example w_elim_generated : elim_type w_desc 0 = build [] elim_w_ty.
Proof. vm_compute. reflexivity. Qed.

Example w_registered :
  option_map sig_entries (registered (declare_checked predicative 300 ∅ raw_w [0]))
  = Some [EElim "W" 0 (build [] elim_w_ty) true; EInd w_desc].
Proof. vm_compute. reflexivity. Qed.
