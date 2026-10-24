(** * Lists and vectors

    Lists, then vectors: the parameter A against the index n.  With the
    motive [P : Πn:ℕ. Vec A n → Type_j] the field [xs : Vec A n] gives the
    hypothesis [ih : P n xs], and the result of the [cons] method
    substitutes the constructor and its index [succ n] into the motive.
    Declarations are monomorphic in their level: [List] and [Vec] over
    types of different universes are separate declarations.

    So far: the declarations and their classification.  The field [x : A]
    of [cons] is non-recursive and [xs] recursive; for vectors the index
    of [xs] is the earlier field [n], and the classification is the
    description written by hand in the kernel (MLTT/Families.v).

    Generated: the eliminators of lists and vectors; for vectors it is the
    kernel's hand-written [elimVec[0]].

    Registered: lists alone, vectors over ℕ, where they are the kernel's
    hand-written entries; without ℕ the index type is refused.

    Planned: the types of the branches of a dependent split. *)

From Stdlib Require Import String List.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Named Signature Check.
From DepTypes.Configs Require Import Predicative.
From DepTypes.SystemU Require Import Looping.
From DepTypes.MLTT Require Import Constants Families.
From IndTypes.Elim Require Import Decl Generate Declare.
From IndTypes.Data Require Import Nat.

Open Scope string_scope.
Open Scope nterm_scope.

(** ** Lists *)

Definition List (A : nterm) : nterm := NConst (Ind "List") A.
Definition lnil (A : nterm) : nterm := NConst (Ctor "List" "nil") A.
Definition lcons (A x xs : nterm) : nterm := NConst (Ctor "List" "cons") A x xs.

Definition raw_list : raw_decl := {|
  rd_name := "List"; rd_params := [Srt (Univ 0)]; rd_indices := []; rd_level := 0;
  rd_ctors := [mk_raw_ctor "nil" (build ["A"] (List "A"));
               mk_raw_ctor "cons" (build ["A"] ("A" ~> List "A" ~> List "A"))] |}.

Definition list_desc : ind_desc := {|
  ind_name := "List"; ind_params := [Srt (Univ 0)]; ind_indices := []; ind_level := 0;
  ind_ctors := [
    {| ctor_name := "nil"; ctor_fields := []; ctor_indices := [] |};
    {| ctor_name := "cons"; ctor_fields := [FArg (build ["A"] "A"); FRec [] []]; ctor_indices := [] |} ] |}.

Example list_classified : classify_decl raw_list = Ok list_desc.
Proof. vm_compute. reflexivity. Qed.

Example list_elim_generated :
  elim_type list_desc 0 =
    build [] (Π "A" : Type@ 0, Π "P" : (List "A" ~> Type@ 0),
              "P" (lnil "A") ~>
              (Π "x" : "A", Π "xs" : List "A", "P" "xs" ~> "P" (lcons "A" "x" "xs")) ~>
              Π "l" : List "A", "P" "l").
Proof. vm_compute. reflexivity. Qed.

(** ** Vectors *)

Definition raw_vec : raw_decl := {|
  rd_name := "Vec"; rd_params := [Srt (Univ 0)]; rd_indices := [build ["A"] Nat]; rd_level := 0;
  rd_ctors := [
    mk_raw_ctor "nil" (build ["A"] (Vec "A" zero));
    mk_raw_ctor "cons"
      (build ["A"] (Π "n" : Nat, Π "x" : "A", Π "xs" : Vec "A" "n", Vec "A" (succ "n")))] |}.

Example vec_classified : classify_decl raw_vec = Ok vec_desc.
Proof. vm_compute. reflexivity. Qed.

Example vec_elim_generated : elim_type vec_desc 0 = build [] elim_vec_ty.
Proof. vm_compute. reflexivity. Qed.

(** ** Registration *)

Example list_registered :
  option_map sig_entries (registered (declare_checked predicative reg_fuel ∅ raw_list [0]))
  = Some [EElim "List" 0 (elim_type list_desc 0) true; EInd list_desc].
Proof. vm_compute. reflexivity. Qed.

(** Over ℕ, vectors are the kernel's hand-written entries. *)
Example vec_registered :
  option_map sig_entries (registered (declare_checked predicative reg_fuel sg_nat0 raw_vec [0]))
  = Some ([EElim "Vec" 0 (build [] elim_vec_ty) true; EInd vec_desc] ++ base_entries true)%list.
Proof. vm_compute. reflexivity. Qed.

(** Without ℕ in the signature the index type of vectors is no type. *)
Example vec_needs_nat :
  refusal (declare_checked predicative reg_fuel ∅ raw_vec [0])
  = Some (RRejected (AtIndType "Vec") (EUnknownConst (Ind "Nat"))).
Proof. vm_compute. reflexivity. Qed.
