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

    ℕ_W as δ-constants over it, each checked without itself:
    [IsTrue : Bool → Type₀], [Nat_W := W Bool IsTrue],
    [zero_W : Nat_W] and [succ_W : Nat_W → Nat_W].  The motives of the
    primitive eliminators are annotated, so that they can be inferred.
    The positions of [zero_W] are [IsTrue false ≡ Void], those of a
    successor [IsTrue true ≡ Unit].

    Planned: the computation of the eliminator on ℕ_W, the rejected
    transfer. *)

From Stdlib Require Import String List Bool.
Import ListNotations.
From DepTypes.Common Require Import Result Traced.
From DepTypes.PTS Require Import Syntax Named Signature Eval Check.
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

(** ** ℕ_W *)

Definition w_fuel : nat := 300.

Definition IsTrue : nterm := NConst (Def "IsTrue").
Definition Nat_W : nterm := NConst (Def "Nat_W").
Definition zero_W : nterm := NConst (Def "zero_W").
Definition succ_W : nterm := NConst (Def "succ_W").

(** [IsTrue b := elimBool (λ_. Type₀) Unit Void b]: the positions of the
    children of a node labelled [b]. *)
Definition is_true_body : nterm := λ "b", NElimBool ((λ "_", Type@ 0) ∷ (NBool ~> Type@ 1)) NUnit NVoid "b".

(** [zero_W := sup false (λv. elimVoid _ v)]: no children. *)
Definition zero_w_body : nterm :=
  sup NBool IsTrue NFalse (λ "v", NElimVoid ((λ "_", Nat_W) ∷ (NVoid ~> Type@ 0)) "v").

(** [succ_W n := sup true (λ_. n)]: one child. *)
Definition succ_w_body : nterm := λ "n", sup NBool IsTrue NTrue (λ "_", "n").

Definition nat_w_run : list (stage * list event) * registration :=
  run_registration (
    let! s1 := declare predicative w_fuel ∅ raw_w [0] in
    let! s2 := define predicative w_fuel s1 "IsTrue" (build [] (NBool ~> Type@ 0)) (build [] is_true_body) in
    let! s3 := define predicative w_fuel s2 "Nat_W" (build [] (Type@ 0)) (build [] (W NBool IsTrue)) in
    let! s4 := define predicative w_fuel s3 "zero_W" (build [] Nat_W) (build [] zero_w_body) in
    define predicative w_fuel s4 "succ_W" (build [] (Nat_W ~> Nat_W)) (build [] succ_w_body)).

Definition sg_nat_w : signature := match registered nat_w_run with Some sg => sg | None => ∅ end.

(** W with its eliminator, then the four constants, each its type and its
    body. *)
Example nat_w_stages :
  map fst (fst nat_w_run) =
  [AtIndType "W"; AtCtorType "W" "sup"; AtField "W" "sup" 0; AtField "W" "sup" 1;
   AtElimType "W" 0; AtRuleLhs "W" 0 "sup"; AtRuleRhs "W" 0 "sup";
   AtDefType "IsTrue"; AtDefBody "IsTrue"; AtDefType "Nat_W"; AtDefBody "Nat_W";
   AtDefType "zero_W"; AtDefBody "zero_W"; AtDefType "succ_W"; AtDefBody "succ_W"].
Proof. vm_compute. reflexivity. Qed.

Example nat_w_entries :
  option_map (fun sg => map (fun e => match e with EDef f _ _ => Some f | _ => None end) (sig_entries sg))
    (registered nat_w_run) = Some [Some "succ_W"; Some "zero_W"; Some "Nat_W"; Some "IsTrue"; None; None].
Proof. vm_compute. reflexivity. Qed.

Definition w_converts (names : list string) (t u : nterm) : bool :=
  match convert sg_nat_w w_fuel (build names t) (build names u) with ConvEqual _ => true | _ => false end.

(** The positions: Void below [false], Unit below [true]; ℕ_W unfolds to
    the W-type, and [succ_W] to a node labelled [true]. *)
Example nat_w_positions :
  w_converts [] (IsTrue NFalse) NVoid &&
  w_converts [] (IsTrue NTrue) NUnit &&
  w_converts [] Nat_W (W NBool IsTrue) &&
  w_converts ["n"] (succ_W "n") (sup NBool IsTrue NTrue (λ "_", "n")) &&
  negb (w_converts [] (IsTrue NFalse) NUnit) = true.
Proof. vm_compute. reflexivity. Qed.

(** [succ_W (succ_W zero_W)] is of type ℕ_W.  A node labelled [true] has
    the position [tt], one labelled [false] none.  Yet any function out of
    its positions makes a node [sup false f], not only the one of
    [zero_W]: the transfer of induction founders on this. *)
Example nat_w_typed :
  snd (run_check predicative sg_nat_w w_fuel [] (build [] (succ_W (succ_W zero_W))) (build [] Nat_W)) = Accepted tt /\
  snd (run_check predicative sg_nat_w w_fuel [] Tt (build [] (IsTrue NTrue))) = Accepted tt /\
  match snd (run_check predicative sg_nat_w w_fuel [] Tt (build [] (IsTrue NFalse))) with
  | Rejected _ => True
  | _ => False
  end /\
  snd (run_check predicative sg_nat_w w_fuel [] (build [] (sup NBool IsTrue NFalse (λ "_", zero_W))) (build [] Nat_W))
    = Accepted tt /\
  w_converts [] (sup NBool IsTrue NFalse (λ "_", zero_W)) zero_W = false.
Proof. split; [ | split; [ | split; [ | split]]]; vm_compute; trivial. Qed.
