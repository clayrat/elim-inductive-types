(** * Tests

    The classification of declarations: the family [Tr] of the kernel's
    MLTT/Families.v, with indices, a recursive field with two positions
    and a field after a recursive one, classifies to its hand-written
    description, and every diagnostic of Elim.Decl arises where it should.

    The generator: on [Tr] it reproduces the hand-written eliminator, and
    on the kernel's signatures every generated ι-rule is the kernel's
    contraction, and both of its sides check against its type in its
    context.

    The registration: declaring ℕ, [Vec], [W] and [Tr] in turn gives
    exactly the kernel's hand-written signature of MLTT/Families.v; each
    refusal arises at its stage; a rule broken by hand is caught in the
    temporary signature, where its left side does not compute; [Unit_ℓ] is
    declared at level ℓ, and the primitive Unit does not stand for it.

    The history: for ℕ, vectors, binary trees, W-types, [Tr] and a family
    of types in [Type₁], [Below_D], [build_D] and [recBelow_D] register
    with what they need, and compute to the formulas of the lecture on
    open terms; the history of a motive in [Type₁] is refused with the
    primitive [Unit : Type₀] in place of [Unit_1].

    Case trees: elaborated, the leaves of [half], [append] and of
    splits of vectors, W-types, binary trees and [Tr] have the names,
    goals, left sides and paths of the lecture; every scope is a context
    the checker accepts, and every right side without recursive calls
    checks against its goal there, so the types of the fields, of the
    hypotheses and of the generalized tail are right.  A hypothesis on
    the length of a vector is generalized with it; at the root the
    varying arguments join the tail.  Every diagnostic arises.

    The compiler: the programs of the lecture and their rejections are in
    Programs/; here the diagnostics of calls: a root that is no split of
    the structural argument, a leaf reached without a split of it, the
    function not applied to all its arguments, a constant argument or an
    index changed in a call.  And the
    splits of the primitive types: of a constant [b : Bool], which
    generalizes the constant [c : IsTrue b], so that in the branch
    [false] [c] is a proof of Void; of Void and of Unit; a primitive
    structural argument is refused.

    Also: the kernel of lecture 6 is linked from the submodule. *)

From Stdlib Require Import String List Bool.
Import ListNotations.
From DepTypes.Common Require Import Result Traced.
From DepTypes.PTS Require Import Syntax Named Signature Eval Check.
From DepTypes.Configs Require Import Finite Predicative.
From DepTypes.SystemU Require Import Looping.
From DepTypes.MLTT Require Import Constants Families.
From IndTypes.Elim Require Import Decl Generate Declare.
From IndTypes.Data Require Import Nat Lists Tree W.
From IndTypes.Recursion Require Import Below CaseTree Compile.
From IndTypes.Programs Require Direct Append.

Open Scope string_scope.
Open Scope nterm_scope.

Example kernel_linked :
  snd (run_infer predicative ∅ 10 [] (Srt (Univ 0))) = Accepted (Srt (Univ 1)).
Proof. vm_compute. reflexivity. Qed.

(** ** A family with every kind of field *)

Definition raw_tr : raw_decl := {|
  rd_name := "Tr"; rd_params := [Srt (Univ 0); build ["A"] ("A" ~> "A" ~> "A")];
  rd_indices := [build ["h"; "A"] "A"]; rd_level := 0;
  rd_ctors := [
    mk_raw_ctor "leaf" (build ["h"; "A"] (Π "a" : "A", Tr "A" "h" "a"));
    mk_raw_ctor "node" (build ["h"; "A"]
      (Π "a" : "A", Π "f" : (Π "y" : "A", Tr "A" "h" ("h" "a" "y")), Tr "A" "h" "a"));
    mk_raw_ctor "fork" (build ["h"; "A"]
      (Π "a" : "A", Π "f" : (Π "y" : "A", Π "z" : "A", Tr "A" "h" ("h" ("h" "a" "y") "z")),
       Tr "A" "h" "a"));
    mk_raw_ctor "twin" (build ["h"; "A"]
      (Π "a" : "A", Π "l" : (Π "y" : "A", Tr "A" "h" ("h" "a" "y")), Π "b" : "A",
       Π "r" : (Π "y" : "A", Tr "A" "h" ("h" "b" "y")), Tr "A" "h" ("h" "a" "b")))] |}.

Example tr_classified : classify_decl raw_tr = Ok tr_desc.
Proof. vm_compute. reflexivity. Qed.

(** ** Diagnostics *)

Definition E : nterm := NConst (Ind "E").

Definition one (params indices : list term) (c : term) : raw_decl := {|
  rd_name := "E"; rd_params := params; rd_indices := indices; rd_level := 0;
  rd_ctors := [mk_raw_ctor "c" c] |}.

(** A recursive field whose domain mentions D is negative. *)
Example domain_negative :
  classify_decl (one [] [] (build [] ((E ~> E) ~> E))) = Err (ENegative "c" 0 (build [] (E ~> E))).
Proof. vm_compute. reflexivity. Qed.

(** D as an argument of another family: nested, outside the grammar. *)
Example nested :
  classify_decl (one [] [] (build [] (List E ~> E))) = Err (ENested "c" 0 (build [] (List E))).
Proof. vm_compute. reflexivity. Qed.

(** A recursive field or the result with other parameters. *)
Example non_uniform :
  classify_decl (one [Srt (Univ 0)] [] (build ["A"] (E NBool ~> E "A")))
  = Err (ENonUniform "c" (SField 0) (build ["A"] (E NBool))) /\
  classify_decl (one [Srt (Univ 0)] [] (build ["A"] (E NBool)))
  = Err (ENonUniform "c" SResult (build ["A"] (E NBool))).
Proof. split; vm_compute; reflexivity. Qed.

(** D in the indices of a recursive field or of the result. *)
Example in_indices :
  classify_decl (one [] [Srt (Univ 0)] (build [] (E (E NUnit) ~> E NUnit)))
  = Err (EInIndices "c" (SField 0) (build [] (E (E NUnit)))) /\
  classify_decl (one [] [Srt (Univ 0)] (build [] (E (E NUnit))))
  = Err (EInIndices "c" SResult (build [] (E (E NUnit)))).
Proof. split; vm_compute; reflexivity. Qed.

Example wrong_arity :
  classify_decl (one [] [] (build [] (E NBool))) = Err (EArity "c" SResult (build [] (E NBool))).
Proof. vm_compute. reflexivity. Qed.

Example not_a_family :
  classify_decl (one [] [] (build [] (NBool ~> NBool))) = Err (ENotFamily "c" Bool).
Proof. vm_compute. reflexivity. Qed.

Example open_parts :
  classify_decl (one [Var 0] [] (build [] E)) = Err EOpenParams /\
  classify_decl (one [] [Var 0] (build [] E)) = Err EOpenIndices /\
  classify_decl (one [] [] (Pi (Var 0) (Const (Ind "E")))) = Err (EOpenCtor "c").
Proof. repeat split; vm_compute; reflexivity. Qed.

Example self_reference :
  classify_decl (one [build [] E] [] (build ["x"] E)) = Err ESelfReference.
Proof. vm_compute. reflexivity. Qed.

Example duplicate_constructor :
  classify_decl {| rd_name := "E"; rd_params := []; rd_indices := []; rd_level := 0;
                   rd_ctors := [mk_raw_ctor "c" (build [] E); mk_raw_ctor "c" (build [] E)] |}
  = Err (EDuplicateCtor "c").
Proof. vm_compute. reflexivity. Qed.

(** ** Generation *)

Example tr_elim_generated : elim_type tr_desc 0 = build [] elim_tr_ty.
Proof. vm_compute. reflexivity. Qed.

Definition accepted (a : answer unit) : bool := match a with Accepted _ => true | _ => false end.

(** The kernel contracts the left side of the rule to its right side, and
    both check against its type in its context. *)
Definition rule_holds (sg : signature) (r : iota_rule) : bool :=
  match iota sg (rule_lhs r) with Some u => term_eqb u (rule_rhs r) | None => false end &&
  accepted (snd (run_check predicative sg 300 (rule_ctx r) (rule_lhs r) (rule_type r))) &&
  accepted (snd (run_check predicative sg 300 (rule_ctx r) (rule_rhs r) (rule_type r))).

Example generated_rules_hold :
  forallb (rule_holds sg_nat) (iota_rules nat_desc 0) &&
  forallb (rule_holds sg_families)
    (iota_rules vec_desc 0 ++ iota_rules w_desc 0 ++ iota_rules tr_desc 0) = true.
Proof. vm_compute. reflexivity. Qed.

Example rule_counts :
  map (fun d => length (iota_rules d 0)) [nat_desc; vec_desc; w_desc; tr_desc] = [2; 2; 1; 4].
Proof. reflexivity. Qed.

(** ** Registration *)

Definition fuel : nat := 300.

(** ℕ, then vectors, W-types and [Tr]: the kernel's hand-written
    signature. *)
Definition sg_registered : list (stage * list event) * registration :=
  run_registration (
    let! s1 := declare predicative fuel ∅ raw_nat [0] in
    let! s2 := declare predicative fuel s1 raw_vec [0] in
    let! s3 := declare predicative fuel s2 raw_w [0] in
    declare predicative fuel s3 raw_tr [0]).

Example families_registered :
  option_map sig_entries (registered sg_registered) = Some family_entries.
Proof. vm_compute. reflexivity. Qed.

Example refusals :
  refusal (declare_checked predicative fuel sg_nat0 raw_nat [0]) = Some (RTaken (Ind "Nat")) /\
  refusal (run_registration (declare_elim predicative fuel sg_nat0 "Nat" 0)) = Some (RTaken (Elim "Nat" 0)) /\
  refusal (run_registration (declare_elim predicative fuel sg_nat0 "Foo" 0)) = Some (RUndeclared "Foo") /\
  refusal (declare_checked system_u_minus fuel ∅ raw_nat [0])
    = Some (RRejected (AtIndType "Nat") (ENotInSystem (Univ 0))).
Proof. repeat split; vm_compute; reflexivity. Qed.

(** A field in [Type₀] of a type in [Type₀] would bring Type-in-Type back;
    a field that is no type is refused at the type of its constructor. *)
Example field_refusals :
  refusal (declare_checked predicative fuel ∅ (one [] [] (build [] (Type@ 0 ~> E))) [])
    = Some (RLevel "c" 0 (Univ 1) 0) /\
  refusal (declare_checked predicative fuel ∅ (one [] [] (build [] (NTt ~> E))) [])
    = Some (RRejected (AtCtorType "E" "c") (ENotASort Tt Unit)).
Proof. split; vm_compute; reflexivity. Qed.

(** The rule of [succ] with the hypothesis dropped from its right side,
    checked in the temporary signature: there the instance has no active
    rules, its left side stays neutral, and the right side is refused. *)
Definition tmp_nat : signature :=
  match sig_add sg_nat0 (EElim "Nat" 0 (elim_type nat_desc 0) false) with Some sg => sg | None => ∅ end.

Definition succ_rule : iota_rule := nth 1 (iota_rules nat_desc 0) (iota_rule_of nat_desc 0 0 (nth 0 (ind_ctors nat_desc) (mk_ctor "" [] []))).

Definition broken (r : iota_rule) : iota_rule :=
  {| rule_ctor := rule_ctor r; rule_ctx := rule_ctx r; rule_lhs := rule_lhs r;
     rule_rhs := match rule_rhs r with App f _ => f | t => t end; rule_type := rule_type r |}.

Example broken_rule_caught :
  normalize tmp_nat fuel (rule_lhs succ_rule) = NormalForm (rule_lhs succ_rule) /\
  match snd (run_traced (check_rule predicative fuel tmp_nat "Nat" 0 (broken succ_rule))) with
  | Err (Refuse (RRejected (AtRuleRhs "Nat" 0 "succ") _)) => True
  | _ => False
  end /\
  snd (run_traced (check_rule predicative fuel tmp_nat "Nat" 0 succ_rule)) = Ok tt.
Proof. split; [ | split]; vm_compute; trivial. Qed.

(** [Unit_ℓ]: the primitive at level 0, a declaration above. *)
Definition sg_unit1 : signature :=
  match snd (run_traced (ensure_unit predicative fuel ∅ 1)) with Ok sg => sg | Err _ => ∅ end.

Example units :
  unit_at 0 = Unit /\ tt_at 0 = Tt /\
  map (fun e => match e with EInd d => Some (ind_name d, ind_level d) | _ => None end) (sig_entries sg_unit1)
    = [Some ("Unit_1", 1)] /\
  snd (run_check predicative sg_unit1 fuel [] (tt_at 1) (unit_at 1)) = Accepted tt /\
  snd (run_infer predicative sg_unit1 fuel [] (unit_at 1)) = Accepted (Srt (Univ 1)) /\
  (match snd (run_traced (ensure_unit predicative fuel sg_unit1 1)) with
   | Ok sg => List.length (sig_entries sg) | Err _ => 0 end) = 1.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** No cumulativity: neither [Unit : Type₀] nor [tt] stands in for
    [Unit_1] and its element. *)
Example no_cumulativity :
  snd (run_check predicative sg_unit1 fuel [] Unit (Srt (Univ 1)))
    = Rejected (EMismatch Unit (Srt (Univ 1)) (Srt (Univ 0))) /\
  snd (run_check predicative sg_unit1 fuel [] Tt (unit_at 1))
    = Rejected (EMismatch Tt (unit_at 1) Unit).
Proof. split; vm_compute; reflexivity. Qed.

(** ** The history *)

(** For ℕ, as in the lecture: [Below] by [elimNat[j+1]] with the motive
    [λ_. Type_j], and [build (succ n) = (step (succ n) h, h)] with
    [h := build n]. *)
Example below_nat :
  below_body nat_desc 1 =
    build [] (λ "P", NConst (Elim "Nat" 2) (λ "_", Type@ 1) (NConst (Ind "Unit_1"))
                       (λ "n", λ "ih", "P" "n" ⨯ "ih")) /\
  build_body nat_desc 0 =
    build [] (λ "P", λ "s", NConst (Elim "Nat" 0)
                (λ "n", "P" "n" ⨯ NConst (Def "Below_Nat_0") "P" "n")
                ⟨ "s" zero NTt, NTt ⟩
                (λ "n", λ "h", ⟨ "s" (succ "n") "h", "h" ⟩)).
Proof. split; vm_compute; reflexivity. Qed.

(** What the history of a motive in [Type₁] needs: [Unit_1], [elimNat[2]]
    for [Below] and [elimNat[1]] for [build]. *)
Example below_stages :
  map fst (fst (run_registration (ensure_below predicative fuel sg_nat0 "Nat" 1))) =
  [AtIndType "Unit_1"; AtCtorType "Unit_1" "tt_1";
   AtElimType "Nat" 2; AtRuleLhs "Nat" 2 "zero"; AtRuleRhs "Nat" 2 "zero";
   AtRuleLhs "Nat" 2 "succ"; AtRuleRhs "Nat" 2 "succ";
   AtElimType "Nat" 1; AtRuleLhs "Nat" 1 "zero"; AtRuleRhs "Nat" 1 "zero";
   AtRuleLhs "Nat" 1 "succ"; AtRuleRhs "Nat" 1 "succ";
   AtDefType "Below_Nat_1"; AtDefBody "Below_Nat_1"; AtDefType "build_Nat_1"; AtDefBody "build_Nat_1";
   AtDefType "recBelow_Nat_1"; AtDefBody "recBelow_Nat_1"].
Proof. vm_compute. reflexivity. Qed.

(** Registered once; refused for a type not declared. *)
Example below_once :
  option_map sig_entries (registered (run_registration (
    let! sg := ensure_below predicative fuel sg_nat0 "Nat" 0 in ensure_below predicative fuel sg "Nat" 0))) =
  option_map sig_entries (registered (run_registration (ensure_below predicative fuel sg_nat0 "Nat" 0))) /\
  refusal (run_registration (ensure_below predicative fuel sg_nat0 "Foo" 0)) = Some (RUndeclared "Foo").
Proof. split; vm_compute; reflexivity. Qed.

(** Telescopes of types: a family in [Type₁], so the history of a motive in
    [Type₀] has the level 1. *)
Definition Tel : nterm := NConst (Ind "Tel").

Definition raw_tel : raw_decl := {|
  rd_name := "Tel"; rd_params := []; rd_indices := []; rd_level := 1;
  rd_ctors := [mk_raw_ctor "tnil" (build [] Tel); mk_raw_ctor "tcons" (build [] (Type@ 0 ~> Tel ~> Tel))] |}.

(** The families with their histories for motives in [Type₀], and ℕ also
    for motives in [Type₁]. *)
Definition sg_history : signature :=
  match registered (run_registration (
    let! s1 := declare predicative fuel ∅ raw_nat [0] in
    let! s2 := declare predicative fuel s1 raw_vec [0] in
    let! s3 := declare predicative fuel s2 raw_tree [0] in
    let! s4 := declare predicative fuel s3 raw_w [0] in
    let! s5 := declare predicative fuel s4 raw_tr [0] in
    let! s6 := declare predicative fuel s5 raw_tel [] in
    tfold (fun sg '(D, j) => ensure_below predicative fuel sg D j) s6
      [("Nat", 0); ("Vec", 0); ("Tree", 0); ("W", 0); ("Tr", 0); ("Tel", 0); ("Nat", 1)]))
  with Some sg => sg | None => ∅ end.

Definition history_converts (names : list string) (t u : nterm) : bool :=
  match convert sg_history fuel (build names t) (build names u) with ConvEqual _ => true | _ => false end.

Definition H (f : string) : nterm := NConst (Def f).

(** On open terms: the tuple of the components of the recursive fields,
    a functional field with its positions, fields after a recursive one,
    and [Unit_1] for the empty history at level 1. *)
Example history_computes :
  forallb (fun c => history_converts (fst (fst c)) (snd (fst c)) (snd c)) [
    (["P"], H "Below_Nat_0" "P" zero, NUnit);
    (["n"; "P"], H "Below_Nat_0" "P" (succ "n"), "P" "n" ⨯ H "Below_Nat_0" "P" "n");
    (["P"], H "Below_Nat_1" "P" zero, NConst (Ind "Unit_1"));
    (["s"; "P"], H "recBelow_Nat_0" "P" "s" zero, "s" zero NTt);
    (["n"; "s"; "P"], H "build_Nat_0" "P" "s" (succ "n"),
       ⟨ "s" (succ "n") (H "build_Nat_0" "P" "s" "n"), H "build_Nat_0" "P" "s" "n" ⟩);
    (["P"; "A"], H "Below_Vec_0" "A" "P" zero (vnil "A"), NUnit);
    (["xs"; "x"; "n"; "P"; "A"], H "Below_Vec_0" "A" "P" (succ "n") (vcons "A" "n" "x" "xs"),
       "P" "n" "xs" ⨯ H "Below_Vec_0" "A" "P" "n" "xs");
    (["r"; "l"; "P"], H "Below_Tree_0" "P" (Tree.node "l" "r"),
       ("P" "l" ⨯ H "Below_Tree_0" "P" "l") ⨯ ("P" "r" ⨯ H "Below_Tree_0" "P" "r"));
    (["f"; "a"; "P"; "B"; "A"], H "Below_W_0" "A" "B" "P" (sup "A" "B" "a" "f"),
       Π "b" : "B" "a", "P" ("f" "b") ⨯ H "Below_W_0" "A" "B" "P" ("f" "b"));
    (["f"; "a"; "P"; "h"; "A"], H "Below_Tr_0" "A" "h" "P" "a" (fork "A" "h" "a" "f"),
       Π "y" : "A", Π "z" : "A",
         "P" ("h" ("h" "a" "y") "z") ("f" "y" "z") ⨯ H "Below_Tr_0" "A" "h" "P" ("h" ("h" "a" "y") "z") ("f" "y" "z"));
    (["r"; "b"; "l"; "a"; "P"; "h"; "A"], H "Below_Tr_0" "A" "h" "P" ("h" "a" "b") (twin "A" "h" "a" "l" "b" "r"),
       (Π "y" : "A", "P" ("h" "a" "y") ("l" "y") ⨯ H "Below_Tr_0" "A" "h" "P" ("h" "a" "y") ("l" "y")) ⨯
       (Π "y" : "A", "P" ("h" "b" "y") ("r" "y") ⨯ H "Below_Tr_0" "A" "h" "P" ("h" "b" "y") ("r" "y")));
    (["P"], H "Below_Tel_0" "P" (NConst (Ctor "Tel" "tnil")), NConst (Ind "Unit_1"));
    (["t"; "A"; "P"], H "Below_Tel_0" "P" (NConst (Ctor "Tel" "tcons") "A" "t"),
       "P" "t" ⨯ H "Below_Tel_0" "P" "t")
  ] = true.
Proof. vm_compute. reflexivity. Qed.

(** And not to anything else: the components in the other order, the
    primitive Unit for [Unit_1]. *)
Example history_distinct :
  history_converts ["r"; "l"; "P"] (H "Below_Tree_0" "P" (Tree.node "l" "r"))
    (("P" "r" ⨯ H "Below_Tree_0" "P" "r") ⨯ ("P" "l" ⨯ H "Below_Tree_0" "P" "l")) = false /\
  history_converts ["P"] (H "Below_Nat_1" "P" zero) NUnit = false.
Proof. split; vm_compute; reflexivity. Qed.

(** Without cumulativity the empty history of a motive in [Type₁] cannot
    be the primitive [Unit : Type₀]: the method of [zero] is refused. *)
Example history_needs_unit_1 :
  match refusal (run_registration (
    let! sg := ensure_elim predicative fuel sg_nat0 "Nat" 2 in
    define predicative fuel sg "Below_Nat_1" (below_type nat_desc 1)
      (build [] (λ "P", NConst (Elim "Nat" 2) (λ "_", Type@ 1) NUnit (λ "n", λ "ih", "P" "n" ⨯ "ih")))))
  with
  | Some (RRejected (AtDefBody "Below_Nat_1") (EMismatch Unit _ _)) => True
  | _ => False
  end.
Proof. vm_compute. trivial. Qed.

(** ** Case trees *)

Fixpoint eqb_list {A} (eqb : A -> A -> bool) (l l' : list A) : bool :=
  match l, l' with
  | [], [] => true
  | a :: l, a' :: l' => eqb a a' && eqb_list eqb l l'
  | _, _ => false
  end.

Fixpoint all2 {A B} (f : A -> B -> bool) (l : list A) (l' : list B) : bool :=
  match l, l' with
  | [], [] => true
  | a :: l, b :: l' => f a b && all2 f l l'
  | _, _ => false
  end.

Definition elaborated (fn : fun_decl) : result case_error elab :=
  let* r := start fn in
  let '(G, goal, env) := r in
  elaborate sg_history G goal env (fn_tree fn).

(** The leaves, in the order of the constructors. *)
Fixpoint leaves (e : elab) : list (scope * term * list term * term) :=
  match e with
  | ELeaf G goal env rhs => [(G, goal, env, rhs)]
  | ESplit _ _ _ es => flat_map (fun '(_, e') => leaves e') es
  end.

Definition leaves_of (fn : fun_decl) : list (scope * term * list term * term) :=
  match elaborated fn with Ok e => leaves e | Err _ => [] end.

(** A leaf with the names [xs] in scope, innermost first, the goal [T]
    and the values [args] of the arguments, named in its scope. *)
Definition leaf_is (l : scope * term * list term * term) (xs : list string) (T : nterm) (args : list nterm) : bool :=
  let '(G, goal, env, _) := l in
  eqb_list String.eqb (visible G) xs &&
  match resolve_in G T, mapM (resolve_in G) args with
  | Ok T', Ok args' => term_eqb goal T' && eqb_list term_eqb env args'
  | _, _ => false
  end.

Definition leaves_are (ls : list (scope * term * list term * term))
    (expected : list (list string * nterm * list nterm)) : bool :=
  all2 (fun l '(xs, T, args) => leaf_is l xs T args) ls expected.

Fixpoint paths (G : scope) : list (string * path) :=
  match G with
  | [] => []
  | b :: G' => match b_tag b with User x (Some p) => (x, p) :: paths G' | _ => paths G' end
  end.

Definition paths_are (G : scope) (expected : list (string * path)) : bool :=
  eqb_list (fun a b => String.eqb (fst a) (fst b) &&
                       eqb_list (fun u v => Nat.eqb (fst u) (fst v) && Nat.eqb (snd u) (snd v)) (snd a) (snd b))
    (paths G) expected.

(** Its scope is a context and its right side checks against its goal. *)
Definition leaf_checks (l : scope * term * list term * term) : bool :=
  let '(G, goal, _, rhs) := l in
  accepted (snd (run_check predicative sg_history fuel (map b_type G) rhs goal)).

Definition plus : nterm := NConst (Def "plus").
Definition half : nterm := NConst (Def "half").

Definition half_fn : fun_decl := {|
  fn_name := "half"; fn_args := [("n", Nat, Constant)]; fn_result := Nat;
  fn_struct := "n"; fn_strategy := History;
  fn_tree := Split "n" [("zero", [], Leaf zero);
                        ("succ", ["m"], Split "m" [("zero", [], Leaf zero);
                                                    ("succ", ["k"], Leaf (succ (half "k")))])] |}.

Definition append_fn : fun_decl := {|
  fn_name := "append";
  fn_args := [("A", Type@ 0, Constant); ("n", Nat, Constant); ("m", Nat, Constant);
              ("xs", Vec "A" "n", Constant); ("ys", Vec "A" "m", Constant)];
  fn_result := Vec "A" (plus "n" "m"); fn_struct := "xs"; fn_strategy := History;
  fn_tree := Split "xs" [("cons", ["n'"; "x"; "xs'"],
                          Leaf (vcons "A" (plus "n'" "m") "x" (NConst (Def "append") "A" "n'" "m" "xs'" "ys")));
                         ("nil", [], Leaf "ys")] |}.

(** [half (succ (succ k))]: [k] two recursive fields down; the branches of
    [append] in either order, [n] and [xs] replaced in the goal and the
    left side, [m] and [ys] untouched. *)
Example case_leaves :
  leaves_are (leaves_of half_fn) [
    ([], Nat, [zero]);
    ([], Nat, [succ zero]);
    (["k"], Nat, [succ (succ "k")])] &&
  match leaves_of half_fn with [_; _; (G, _, _, _)] => paths_are G [("k", [(0, 1); (0, 1)])] | _ => false end &&
  leaves_are (leaves_of append_fn) [
    (["ys"; "m"; "A"], Vec "A" (plus zero "m"), [NVar "A"; zero; NVar "m"; vnil "A"; NVar "ys"]);
    (["xs'"; "x"; "n'"; "ys"; "m"; "A"], Vec "A" (plus (succ "n'") "m"),
       [NVar "A"; succ "n'"; NVar "m"; vcons "A" "n'" "x" "xs'"; NVar "ys"])] = true.
Proof. vm_compute. reflexivity. Qed.

(** A hypothesis [h : P n] on the length of the vector split is
    generalized with it: in the branches it is [P zero] and
    [P (succ k)], and [h] checks against the goal [P n] refined alike. *)
Definition on_length (t : case_tree) : fun_decl := {|
  fn_name := "g";
  fn_args := [("A", Type@ 0, Constant); ("P", Nat ~> Type@ 0, Constant); ("n", Nat, Constant);
              ("h", "P" "n", Constant); ("v", Vec "A" "n", Constant)];
  fn_result := "P" "n"; fn_struct := "v"; fn_strategy := History; fn_tree := t |}.

Definition on_length_tree : case_tree :=
  Split "v" [("nil", [], Leaf "h"); ("cons", ["k"; "x"; "w"], Leaf "h")].

Example case_generalizes :
  leaves_are (leaves_of (on_length on_length_tree)) [
    (["h"; "P"; "A"], "P" zero, [NVar "A"; NVar "P"; zero; NVar "h"; vnil "A"]);
    (["h"; "w"; "x"; "k"; "P"; "A"], "P" (succ "k"), [NVar "A"; NVar "P"; succ "k"; NVar "h"; vcons "A" "k" "x" "w"])] &&
  forallb leaf_checks (leaves_of (on_length on_length_tree)) = true.
Proof. vm_compute. reflexivity. Qed.

(** Splits rebuilding what they split, so that every right side checks:
    a functional field and its hypothesis (W), two recursive fields with
    their paths (binary trees), and indices through a parameter, positions
    and a field after a recursive one ([Tr]). *)
Definition rebuild (args : list (string * nterm * mark)) (T : nterm) (x : string) (t : case_tree) : fun_decl :=
  {| fn_name := "id"; fn_args := args; fn_result := T; fn_struct := x; fn_strategy := History; fn_tree := t |}.

Definition w_id : fun_decl :=
  rebuild [("A", Type@ 0, Constant); ("B", "A" ~> Type@ 0, Constant); ("w", W "A" "B", Constant)] (W "A" "B") "w"
    (Split "w" [("sup", ["a"; "f"], Leaf (sup "A" "B" "a" "f"))]).

Definition tree_id : fun_decl :=
  rebuild [("t", Tree, Constant)] Tree "t"
    (Split "t" [("leaf", [], Leaf (NConst (Ctor "Tree" "leaf"))); ("node", ["l"; "r"], Leaf (Tree.node "l" "r"))]).

Definition tr_id : fun_decl :=
  rebuild [("A", Type@ 0, Constant); ("h", "A" ~> "A" ~> "A", Constant); ("x", NVar "A", Constant);
           ("t", Tr "A" "h" "x", Constant)] (Tr "A" "h" "x") "t"
    (Split "t" [("twin", ["a"; "l"; "b"; "r"], Leaf (twin "A" "h" "a" "l" "b" "r"));
                ("leaf", ["a"], Leaf (leaf "A" "h" "a"));
                ("fork", ["a"; "f"], Leaf (fork "A" "h" "a" "f"));
                ("node", ["a"; "f"], Leaf (Families.node "A" "h" "a" "f"))]).

Example case_scopes_typed :
  forallb leaf_checks (leaves_of w_id ++ leaves_of tree_id ++ leaves_of tr_id) &&
  Nat.eqb (length (leaves_of tr_id)) 4 &&
  match leaves_of tree_id with
  | [_; (G, _, _, _)] => paths_are G [("r", [(1, 2)]); ("l", [(0, 2)])]
  | _ => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(** At the root the varying argument [b] joins the tail, and the
    hypothesis of [succ m] takes it: [ih b : Nat]. *)
Definition with_varying : fun_decl :=
  rebuild [("n", Nat, Constant); ("b", Nat, Varying)] Nat "n"
    (Split "n" [("zero", [], Leaf "b"); ("succ", ["m"], Leaf "b")]).

Example case_root_tail :
  varying with_varying = [1] /\
  match start with_varying with
  | Ok (G, goal, env) =>
      match elaborate_with sg_history [1] Aux G goal env (fn_tree with_varying) with
      | Ok (ESplit _ _ si [(_, ELeaf G0 T0 _ b0); (_, ELeaf G1 T1 _ _)]) =>
          match find_aux 0 G1, resolve_in G1 "b" with
          | Some ih, Ok b =>
              gn_tail (si_gen si) = [1] /\
              accepted (snd (run_check predicative sg_history fuel (map b_type G0) b0 T0)) = true /\
              accepted (snd (run_check predicative sg_history fuel (map b_type G1) (App (Var ih) b) T1)) = true
          | _, _ => False
          end
      | _ => False
      end
  | Err _ => False
  end.
Proof. vm_compute. repeat split. Qed.

(** The diagnostics. *)
Example case_errors :
  map elaborated [
    on_length (Split "q" []);
    on_length (Split "A" []);
    on_length (Split "v" [("nil", [], Leaf "h")]);
    on_length (Split "v" [("nil", [], Leaf "h"); ("cons", ["k"; "x"], Leaf "h")]);
    on_length (Split "v" [("nil", [], Leaf "h"); ("cons", ["k"; "k"; "w"], Leaf "h")]);
    on_length (Split "v" [("nil", [], Leaf "h"); ("cons", ["k"; "h"; "w"], Leaf "h")]);
    on_length (Split "v" [("nil", [], Leaf "nope"); ("cons", ["k"; "x"; "w"], Leaf "h")]);
    rebuild [("P", Nat ~> Type@ 0, Constant); ("n", Nat, Constant); ("v", Vec ("P" "n") "n", Constant)] Nat "v"
      (Split "v" [("nil", [], Leaf zero); ("cons", ["k"; "x"; "w"], Leaf zero)]);
    rebuild [("A", Type@ 0, Constant); ("n", Nat, Constant); ("v", Vec "A" (succ "n"), Constant)] Nat "v"
      (Split "v" []);
    rebuild [("n", Nat, Constant); ("n", Nat, Constant)] Nat "n" (Leaf zero);
    rebuild [("n", Nat, Constant)] Nat "m" (Leaf zero)] =
  [Err (CUnbound "q"); Err (CNotFamily "A" (Srt (Univ 0)));
   Err (CBranches "v"); Err (CFields "cons" 3);
   Err (CFieldName "cons" "k"); Err (CFieldName "cons" "h");
   Err (CUnbound "nope");
   Err (CParams "v" "n");
   Err (CIndices "v" (App (App (Const (Ind "Vec")) (Var 1)) (App (Const (Ctor "Nat" "succ")) (Var 0))));
   Err (CDuplicateArg "n"); Err (CNoStruct "m")] /\
  (* A varying [A] at the root: a parameter of the vector, non-uniform. *)
  match start (on_length on_length_tree) with
  | Ok (G, goal, env) => elaborate_with sg_history [0] (fun _ => Anon) G goal env on_length_tree
  | Err e => Err e
  end = Err (CParams "v" "A") /\
  (* An index whose type mentions the varying [b], outside the parameters. *)
  match start (rebuild [("A", Type@ 0, Constant); ("h", "A" ~> "A" ~> "A", Constant); ("b", Type@ 0, Varying);
                        ("x", NVar "b", Constant); ("t", Tr "A" "h" "x", Constant)] Nat "t" (Split "t" [])) with
  | Ok (G, goal, env) => elaborate_with sg_history [2] (fun _ => Anon) G goal env (Split "t" [])
  | Err e => Err e
  end = Err (CGeneralize "x" "b").
Proof. repeat split; vm_compute; reflexivity. Qed.

(** ** The compiler *)

Definition with_tree (fn : fun_decl) (t : case_tree) : fun_decl :=
  {| fn_name := fn_name fn; fn_args := fn_args fn; fn_result := fn_result fn;
     fn_struct := fn_struct fn; fn_strategy := fn_strategy fn; fn_tree := t |}.

Definition compile_error (sg : signature) (fn : fun_decl) : option case_error :=
  match refusal (compile_all predicative Direct.prog_fuel sg [fn]) with Some (RCase e) => Some e | _ => None end.

Definition plus_with (t : nterm) : fun_decl :=
  with_tree Direct.plus_fn (Split "n" [("zero", [], Leaf "m"); ("succ", ["k"], Leaf t)]).

Example call_errors :
  compile_error sg_nat0 (with_tree Direct.plus_fn (Leaf "m")) = Some (CRoot "n") /\
  match compile_error sg_nat0 (plus_with (succ (Direct.plus "k"))),
        compile_error sg_nat0 (plus_with (succ (Direct.plus "k" zero))),
        compile_error Append.sg_vec
          (with_tree (Append.append_fn "append" Direct.plus)
             (Split "xs" [("nil", [], Leaf "ys");
                          ("cons", ["k"; "x"; "xs'"],
                           Leaf (vcons "A" (Direct.plus "k" "m") "x" (Append.append "A" "m" "m" "xs'" "ys")))]))
  with
  | Some (CCallArity _), Some (CConstantChanged "m" _), Some (CIndexChanged "n" _) => True
  | _, _, _ => False
  end.
Proof. split; vm_compute; trivial. Qed.

(** ** Splits of the primitive types *)

Definition IsTrue (b : nterm) : nterm := NElimBool ((λ "_", Type@ 0) ∷ (NBool ~> Type@ 1)) NUnit NVoid b.
Definition pick : nterm := NConst (Def "pick").
Definition absurd_nat (c : nterm) : nterm := NElimVoid ((λ "_", Nat) ∷ (NVoid ~> Type@ 0)) c.

(** [pick n b c]: [n] structural, [b] and [c : IsTrue b] constant. *)
Definition pick_fn (t : case_tree) : fun_decl :=
  rebuild [("n", Nat, Constant); ("b", NBool, Constant); ("c", IsTrue "b", Constant)] Nat "n" t.

Definition on_b (t : nterm) : case_tree := Split "b" [("false", [], Leaf (absurd_nat "c")); ("true", [], Leaf t)].

(** In the scope of each branch [c] is refined with [b]: [IsTrue false]
    reduces to Void, and [elimVoid c] checks. *)
Example bool_split_generalizes :
  leaves_are (leaves_of (pick_fn (on_b "n"))) [
    (["c"; "n"], Nat, [NVar "n"; NTrue; NVar "c"]);
    (["c"; "n"], Nat, [NVar "n"; NFalse; NVar "c"])] &&
  forallb leaf_checks (leaves_of (pick_fn (on_b "n"))) = true.
Proof. vm_compute. reflexivity. Qed.

(** Compiled within a recursion on [n], the call passing [b] and [c] on;
    a split of Void and one of Unit; a structural argument of Bool. *)
Definition pick_rec : fun_decl :=
  {| fn_name := "pick"; fn_args := fn_args (pick_fn (on_b "n")); fn_result := Nat; fn_struct := "n";
     fn_strategy := History;
     fn_tree := Split "n" [("zero", [], on_b zero); ("succ", ["k"], Leaf (succ (pick "k" "b" "c")))] |}.

Definition void_fn : fun_decl :=
  {| fn_name := "absurd"; fn_args := [("n", Nat, Constant); ("v", NVoid, Constant)]; fn_result := Nat;
     fn_struct := "n"; fn_strategy := History; fn_tree := Split "v" [] |}.

Definition unit_fn (t : case_tree) : fun_decl :=
  {| fn_name := "unit_id"; fn_args := [("n", Nat, Constant); ("u", NUnit, Constant)]; fn_result := Nat;
     fn_struct := "n"; fn_strategy := History; fn_tree := t |}.

Definition unit_id : nterm := NConst (Def "unit_id").

Definition on_n_u : case_tree :=
  Split "n" [("zero", [], Split "u" [("tt", [], Leaf zero)]);
             ("succ", ["k"], Split "u" [("tt", [], Leaf (succ (unit_id "k" NTt)))])].

Definition sg_pick : signature :=
  match registered (compile_all predicative Direct.prog_fuel sg_nat0 [pick_rec; void_fn; unit_fn on_n_u]) with
  | Some sg => sg | None => ∅ end.

Example primitive_splits_compiled :
  registered (compile_all predicative Direct.prog_fuel sg_nat0 [pick_rec; void_fn; unit_fn on_n_u]) <> None /\
  normalize sg_pick Direct.prog_fuel (build [] (pick (Direct.num 2) NTrue NTt)) = NormalForm (build [] (Direct.num 2)) /\
  Direct.converts sg_pick ["c"; "n"] (pick (succ "n") NTrue "c") (succ (pick "n" NTrue "c")) = true /\
  normalize sg_pick Direct.prog_fuel (build [] (unit_id (Direct.num 3) NTt)) = NormalForm (build [] (Direct.num 3)) /\
  (* Without a split of [n] the leaf leaves [recBelow] stuck on it. *)
  compile_error sg_nat0 (unit_fn (Split "u" [("tt", [], Leaf "n")])) = Some (CUnsplit "n") /\
  compile_error sg_nat0 (rebuild [("b", NBool, Constant)] Nat "b" (Split "b" [("true", [], Leaf zero); ("false", [], Leaf zero)]))
    = Some (CNotFamily "b" Bool).
Proof. split; [vm_compute; discriminate | repeat split; vm_compute; reflexivity]. Qed.
