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

    Planned: [Below] at each level, and the compiler on every program and
    every rejection.

    Also: the kernel of lecture 6 is linked from the submodule. *)

From Stdlib Require Import String List Bool.
Import ListNotations.
From DepTypes.Common Require Import Result Traced.
From DepTypes.PTS Require Import Syntax Named Signature Eval Check.
From DepTypes.Configs Require Import Finite Predicative.
From DepTypes.SystemU Require Import Looping.
From DepTypes.MLTT Require Import Constants Families.
From IndTypes.Elim Require Import Decl Generate Declare.
From IndTypes.Data Require Import Nat Lists W.

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
Proof. repeat split; vm_compute; trivial. Qed.

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
