(** * Void, Unit and Bool as declarations

    The regression of the generator: the descriptions of Void, Unit and
    Bool at level 0 give exactly the rules of the primitives of lecture 6.
    The primitives stay in the kernel; [Unit_0] is the primitive Unit, and
    [Unit_ℓ] for ℓ > 0 is declared by algorithm 1 with result exactly
    [Type_ℓ].

    The descriptions have no constructor, one without fields, two without
    fields.  Read with the primitives in place of the constants
    ([to_prim]: [Ind "Bool"] as Bool, [Ctor "Bool" "true"] as true, a full
    spine of [Elim "Bool" j] as [elimBool]), the generated eliminator type
    is the type schema of the primitive eliminator, which the primitive
    eliminator inhabits, and every generated ι-rule is the primitive one. *)

From Stdlib Require Import String List Bool.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Named Signature Eval Check.
From DepTypes.Configs Require Import Predicative.
From DepTypes.SystemU Require Import Looping.
From IndTypes.Elim Require Import Decl Generate.

Open Scope string_scope.
Open Scope nterm_scope.

Definition empty_ctor (c : string) : ctor_desc := {| ctor_name := c; ctor_fields := []; ctor_indices := [] |}.

Definition simple (D : string) (cs : list string) : raw_decl := {|
  rd_name := D; rd_params := []; rd_indices := []; rd_level := 0;
  rd_ctors := map (fun c => mk_raw_ctor c (Const (Ind D))) cs |}.

Definition raw_void : raw_decl := simple "Void" [].
Definition raw_unit : raw_decl := simple "Unit" ["tt"].
Definition raw_bool : raw_decl := simple "Bool" ["true"; "false"].

Definition simple_desc (D : string) (cs : list string) : ind_desc := {|
  ind_name := D; ind_params := []; ind_indices := []; ind_level := 0; ind_ctors := map empty_ctor cs |}.

Example primitives_classified :
  classify_decl raw_void = Ok (simple_desc "Void" []) /\
  classify_decl raw_unit = Ok (simple_desc "Unit" ["tt"]) /\
  classify_decl raw_bool = Ok (simple_desc "Bool" ["true"; "false"]).
Proof. repeat split; vm_compute; reflexivity. Qed.

Definition void_desc : ind_desc := simple_desc "Void" [].
Definition unit_desc : ind_desc := simple_desc "Unit" ["tt"].
Definition bool_desc : ind_desc := simple_desc "Bool" ["true"; "false"].

(** ** Against the primitives *)

Definition prim_const (g : gref) : term :=
  match g with
  | Ind D =>
      if String.eqb D "Void" then Void else if String.eqb D "Unit" then Unit
      else if String.eqb D "Bool" then Bool else Const g
  | Ctor D c =>
      if String.eqb D "Unit" && String.eqb c "tt" then Tt
      else if String.eqb D "Bool" && String.eqb c "true" then BTrue
      else if String.eqb D "Bool" && String.eqb c "false" then BFalse
      else Const g
  | _ => Const g
  end.

(** A full spine of an eliminator of the three, translated bottom-up: the
    family and the branches are already translated. *)
Definition prim_app (f a : term) : term :=
  match f with
  | App (Const (Elim D _)) C => if String.eqb D "Void" then ElimVoid C a else App f a
  | App (App (Const (Elim D _)) C) c => if String.eqb D "Unit" then ElimUnit C c a else App f a
  | App (App (App (Const (Elim D _)) C) t) e => if String.eqb D "Bool" then ElimBool C t e a else App f a
  | _ => App f a
  end.

Fixpoint to_prim (t : term) : term :=
  match t with
  | Const g => prim_const g
  | App f a => prim_app (to_prim f) (to_prim a)
  | Pi A B => Pi (to_prim A) (to_prim B)
  | Lam b => Lam (to_prim b)
  | Ann u A => Ann (to_prim u) (to_prim A)
  | ElimVoid C e => ElimVoid (to_prim C) (to_prim e)
  | ElimUnit C c u => ElimUnit (to_prim C) (to_prim c) (to_prim u)
  | ElimBool C t' f b => ElimBool (to_prim C) (to_prim t') (to_prim f) (to_prim b)
  | Sigma A B => Sigma (to_prim A) (to_prim B)
  | Pair a b => Pair (to_prim a) (to_prim b)
  | Fst u => Fst (to_prim u)
  | Snd u => Snd (to_prim u)
  | Srt _ | Var _ | Void | Unit | Tt | Bool | BTrue | BFalse => t
  end.

(** The type schemas of the primitive eliminators. *)
Definition void_schema (j : nat) : nterm := Π "C" : (NVoid ~> Type@ j), Π "v" : NVoid, "C" "v".
Definition unit_schema (j : nat) : nterm :=
  Π "C" : (NUnit ~> Type@ j), "C" NTt ~> Π "u" : NUnit, "C" "u".
Definition bool_schema (j : nat) : nterm :=
  Π "C" : (NBool ~> Type@ j), "C" NTrue ~> "C" NFalse ~> Π "b" : NBool, "C" "b".

Example elim_types_are_the_schemas :
  to_prim (elim_type void_desc 0) = build [] (void_schema 0) /\
  to_prim (elim_type unit_desc 0) = build [] (unit_schema 0) /\
  to_prim (elim_type bool_desc 0) = build [] (bool_schema 0) /\
  to_prim (elim_type bool_desc 1) = build [] (bool_schema 1).
Proof. repeat split; vm_compute; reflexivity. Qed.

Definition accepted (a : answer unit) : bool := match a with Accepted _ => true | _ => false end.

(** The primitive eliminators inhabit the generated types. *)
Example primitives_inhabit :
  accepted (snd (run_check predicative ∅ 100 [] (Lam (Lam (ElimVoid (Var 1) (Var 0))))
                   (to_prim (elim_type void_desc 0)))) &&
  accepted (snd (run_check predicative ∅ 100 [] (Lam (Lam (Lam (ElimUnit (Var 2) (Var 1) (Var 0)))))
                   (to_prim (elim_type unit_desc 0)))) &&
  accepted (snd (run_check predicative ∅ 100 []
                   (Lam (Lam (Lam (Lam (ElimBool (Var 3) (Var 2) (Var 1) (Var 0))))))
                   (to_prim (elim_type bool_desc 0)))) = true.
Proof. vm_compute. reflexivity. Qed.

(** Every generated rule is the primitive contraction; Void has none. *)
Definition prim_rule (r : iota_rule) : bool :=
  match Eval.contract ∅ (to_prim (rule_lhs r)) with
  | Some u => term_eqb u (to_prim (rule_rhs r))
  | None => false
  end.

Example rules_are_the_primitive_ones :
  iota_rules void_desc 0 = [] /\
  forallb prim_rule (iota_rules unit_desc 0 ++ iota_rules bool_desc 0) = true /\
  length (iota_rules bool_desc 0) = 2.
Proof. repeat split; vm_compute; reflexivity. Qed.
