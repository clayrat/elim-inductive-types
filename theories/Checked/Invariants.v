(** * Invariants of checked signatures

    The properties of a signature that the registrations of a checked
    signature keep (Checked/Steps.v), stated here and proved in the
    files that follow:
    - [checked_inv]: every instance has the type the generator gives it,
      for the declaration of its family ([elim_types_generated]), and the
      constructors of every declaration have distinct names
      (Checked/Shaped.v);
    - [sig_inv]: the types of the constants are types, the δ-bodies have
      them ([bodies_typed]), and every instance with active rules has
      its rules typed in their generic contexts ([instances_checked],
      [rules_typed]), with [checked_inv] (Checked/SigTyped.v); the lemma
      on ι (Checked/IotaTyped.v) makes such a signature type-correct;
    - [rec_ok] and [singleton_ok]: a recursive field has the type of its
      family at as many indices as the family has, and the fields of the
      constructor of a singleton proposition are proofs
      (Checked/Fields.v). *)

From Stdlib Require Import List.
Import ListNotations.
From DepTypes.PTS Require Import Syntax Spec Signature Typing Inversion BidirSound.
From DepTypes.Configs Require Import Predicative.
From IndTypes.Elim Require Import Generate.

Local Open Scope list_scope.

Local Notation SP := predicative_prop.

(** ** The generated instances *)

Definition elim_types_generated (sg : signature) : Prop :=
  forall D s A act, sig_elim sg D s = Some (A, act) -> exists d, sig_ind sg D = Some d /\ A = elim_type d s.

(** The generated types of the instances, and the distinct names of
    constructors. *)
Record checked_inv (sg : signature) : Prop := {
  checked_generated : elim_types_generated sg;
  checked_distinct : ctors_distinct sg;
}.
Arguments checked_generated {sg}.
Arguments checked_distinct {sg}.

(** ** Type-correctness *)

(** The right side of every rule of an instance has the type of the
    rule, in its context. *)
Definition rules_typed (S : spec) (sg : signature) (d : ind_desc) (s : sort) : Prop :=
  forall r, In r (iota_rules d s) -> has_type S sg (rule_ctx r) (rule_rhs r) (rule_type r).

(** Every instance with active rules has the generated type, and its
    rules are typed. *)
Definition instances_checked (S : spec) (sg : signature) : Prop :=
  forall D s A, sig_elim sg D s = Some (A, true) ->
    exists d, sig_ind sg D = Some d /\ A = elim_type d s /\ rules_typed S sg d s.

(** The δ-bodies have the types of their constants. *)
Definition bodies_typed (sg : signature) : Prop :=
  forall g A b, sig_type sg g = Some A -> sig_delta sg g = Some b -> has_type SP sg [] b A.

(** The types of the constants are types, the δ-bodies and the rules of
    the instances are typed, and [checked_inv]. *)
Record sig_inv (sg : signature) : Prop := {
  inv_types : sig_types_typed SP sg;
  inv_bodies : bodies_typed sg;
  inv_instances : instances_checked SP sg;
  inv_checked : checked_inv sg;
}.
Arguments inv_types {sg}.
Arguments inv_bodies {sg}.
Arguments inv_instances {sg}.
Arguments inv_checked {sg}.

(** ** The fields of declarations *)

(** A recursive field has the type of its family at as many indices as
    the family has: classification checks it. *)
Definition rec_ok (sg : signature) : Prop :=
  forall D d c Bs vs, sig_ind sg D = Some d -> In c (ind_ctors d) -> In (FRec Bs vs) (ctor_fields c) ->
    length vs = length (ind_indices d).

(** The fields of the constructor of a singleton proposition are proofs,
    in the context of the parameters and the fields before them. *)
Definition singleton_ok (sg : signature) : Prop :=
  forall D d c, sig_ind sg D = Some d -> ind_sort d = Prp -> ind_elim d = AllSorts -> ind_ctors d = [c] ->
    forall j T, nth_error (field_types D (length (ind_params d)) 0 (ctor_fields c)) j = Some T ->
    has_type SP sg (rev (ind_params d ++ firstn j (field_types D (length (ind_params d)) 0 (ctor_fields c))))
      T (Srt Prp).
