(** * Binary trees: two recursive fields

    [node : Tree → Tree → Tree] checks the order of the generator's pass:
    the method takes [left, ih_left, right, ih_right], and the ι-rule
    passes its arguments in the same order.

    So far: the declaration, classified with two recursive fields, and the
    generated method and eliminator, in that order.  The kernel's [Tr]
    (MLTT/Families.v) checks the same order on its [twin], whose
    hand-written eliminator the generator reproduces too (Tests.v).

    Registered by [declare_checked], which checks the ι-rules of [leaf]
    and [node] in the stages logged. *)

From Stdlib Require Import String List.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Named Signature Check.
From DepTypes.Configs Require Import Predicative.
From DepTypes.SystemU Require Import Looping.
From IndTypes.Elim Require Import Decl Generate Declare.

Open Scope string_scope.
Open Scope nterm_scope.

Definition Tree : nterm := NConst (Ind "Tree").
Definition node (l r : nterm) : nterm := NConst (Ctor "Tree" "node") l r.

Definition raw_tree : raw_decl := {|
  rd_name := "Tree"; rd_params := []; rd_indices := []; rd_level := 0;
  rd_ctors := [mk_raw_ctor "leaf" (build [] Tree); mk_raw_ctor "node" (build [] (Tree ~> Tree ~> Tree))] |}.

Definition tree_desc : ind_desc := {|
  ind_name := "Tree"; ind_params := []; ind_indices := []; ind_level := 0;
  ind_ctors := [
    {| ctor_name := "leaf"; ctor_fields := []; ctor_indices := [] |};
    {| ctor_name := "node"; ctor_fields := [FRec [] []; FRec [] []]; ctor_indices := [] |} ] |}.

Example tree_classified : classify_decl raw_tree = Ok tree_desc.
Proof. vm_compute. reflexivity. Qed.

(** [left, ih_left, right, ih_right], in the context of the motive. *)
Example node_method :
  method_type tree_desc {| ctor_name := "node"; ctor_fields := [FRec [] []; FRec [] []]; ctor_indices := [] |} =
  build ["P"] (Π "l" : Tree, "P" "l" ~> Π "r" : Tree, "P" "r" ~> "P" (node "l" "r")).
Proof. vm_compute. reflexivity. Qed.

Example tree_elim_generated :
  elim_type tree_desc 0 =
    build [] (Π "P" : (Tree ~> Type@ 0), "P" (NConst (Ctor "Tree" "leaf")) ~>
              (Π "l" : Tree, "P" "l" ~> Π "r" : Tree, "P" "r" ~> "P" (node "l" "r")) ~>
              Π "t" : Tree, "P" "t").
Proof. vm_compute. reflexivity. Qed.

(** Registered, with the rules of [leaf] and [node] checked. *)
Example tree_registered :
  option_map sig_entries (registered (declare_checked predicative 300 ∅ raw_tree [0]))
  = Some [EElim "Tree" 0 (elim_type tree_desc 0) true; EInd tree_desc].
Proof. vm_compute. reflexivity. Qed.

Example tree_rule_stages :
  map fst (fst (declare_checked predicative 300 ∅ raw_tree [0])) =
  [AtIndType "Tree"; AtCtorType "Tree" "leaf"; AtCtorType "Tree" "node";
   AtField "Tree" "node" 0; AtField "Tree" "node" 1; AtElimType "Tree" 0;
   AtRuleLhs "Tree" 0 "leaf"; AtRuleRhs "Tree" 0 "leaf";
   AtRuleLhs "Tree" 0 "node"; AtRuleRhs "Tree" 0 "node"].
Proof. vm_compute. reflexivity. Qed.
