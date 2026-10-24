(** * ℕ: from recursion to induction

    ℕ of System T as the first declaration processed by algorithm 1, with
    its generation written out in full: the motive [P : ℕ → Type_j] in
    place of the constant result type of the recursor, and [elimNat]
    returning [P n].  Induction has a computational meaning here without a
    separate Prop.  Several levels are instantiated: the history of
    [isEven] needs [elimNat[1]] and [elimNat[2]].

    So far: the declaration, whose classification is the description of
    ℕ written by hand in the kernel (MLTT/Constants.v), and the generated
    eliminator, which at level 0 is the kernel's hand-written [elimNat[0]]
    and at level 1 differs only in the level of the motive.

    Registered by [declare_checked], with its instance at level 0 it is
    the kernel's hand-written signature, and [double] defined by
    [define_checked] on it is the kernel's too; instances at several
    levels are separate constants.

    Planned: the trace of the generation in the demos. *)

From Stdlib Require Import String List Program.Basics.
Local Open Scope program_scope.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Named Signature Check.
From DepTypes.Configs Require Import Predicative.
From DepTypes.SystemU Require Import Looping.
From DepTypes.MLTT Require Import Constants.
From IndTypes.Elim Require Import Decl Generate Declare.

Open Scope string_scope.
Open Scope nterm_scope.

Definition raw_nat : raw_decl := {|
  rd_name := "Nat"; rd_params := []; rd_indices := []; rd_level := 0;
  rd_ctors := [mk_raw_ctor "zero" (build [] Nat); mk_raw_ctor "succ" (build [] (Nat ~> Nat))] |}.

Example nat_classified : classify_decl raw_nat = Ok nat_desc.
Proof. vm_compute. reflexivity. Qed.

(** ** The eliminator *)

Example nat_elim_generated :
  elim_type nat_desc 0 = build [] elim_nat_ty /\
  elim_type nat_desc 1 =
    build [] (Π "P" : (Nat ~> Type@ 1), "P" zero ~> (Π "n" : Nat, "P" "n" ~> "P" (succ "n")) ~>
              Π "n" : Nat, "P" "n").
Proof. split; vm_compute; reflexivity. Qed.

(** ** Registration *)

Definition reg_fuel : nat := 300.

(** Registered with its instance at level 0, ℕ is the signature written
    by hand in the kernel; [double] defined on it is the kernel's too. *)
Example nat_registered :
  option_map sig_entries (registered (declare_checked predicative reg_fuel ∅ raw_nat [0]))
  = Some (base_entries true).
Proof. vm_compute. reflexivity. Qed.

Definition sg_nat0 : signature :=
  match registered (declare_checked predicative reg_fuel ∅ raw_nat [0]) with Some sg => sg | None => ∅ end.

Example double_defined :
  option_map sig_entries
    (registered (define_checked predicative reg_fuel sg_nat0 "double" (build [] (Nat ~> Nat))
                   (build [] double_body)))
  = Some (nat_entries true).
Proof. vm_compute. reflexivity. Qed.

(** A body that mentions the constant being defined is refused. *)
Example double_self_refused :
  refusal (define_checked predicative reg_fuel sg_nat0 "double" (build [] (Nat ~> Nat))
             (build [] (λ "n", double "n")))
  = Some (RRejected (AtDefBody "double") (EUnknownConst (Def "double"))).
Proof. vm_compute. reflexivity. Qed.

(** Instances at several levels, each its own constant. *)
Example nat_levels :
  option_map (map (fun e => match e with EElim D j _ act => Some (D, j, act) | _ => None end) ∘ sig_entries)
    (registered (declare_checked predicative reg_fuel ∅ raw_nat [0; 1; 2]))
  = Some [Some ("Nat", 2, true); Some ("Nat", 1, true); Some ("Nat", 0, true); None].
Proof. vm_compute. reflexivity. Qed.
