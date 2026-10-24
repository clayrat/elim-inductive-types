(** * Contracts of the lecture on inductive types

    As in the kernel's Contracts.v: the guarantees are [Prop] definitions,
    kernel-checked independently of their proofs; a contract followed by a
    theorem [..._holds] is proved, one without a theorem is an open
    obligation, stated precisely but not proved.  [make assumptions]
    prints the assumptions of every proved contract and fails unless all
    of them are closed under the global context.

    Proved so far: the classification of declarations is faithful (the
    types rebuilt from a description are the declared ones) and strictly
    positive; and whatever a registration returns has passed its checks
    in the sense of the annotated kernel: declarations, instances of
    eliminators with their ι-rules, and δ-constants.

    Open for algorithm 1, stated below: the classification is complete
    for the grammar; for every accepted declaration and every level the
    generated instance is typed and its ι-rules keep types, declaratively;
    its registration succeeds with enough fuel; and the signatures that
    registrations build are type-correct, normalizing and consistent.

    Planned:
    - proved: the soundness of the checker and of conversion carries over
      to the kernel with Σ, δ-constants and the ι-rules of the signature
      (the kernel's CheckSound, extended in the submodule);
    - checked on every output, through [declare_checked] and
      [compile_checked], as [translate_checked] checks the outputs of the
      translator in lecture 6: every generated eliminator type is
      accepted in the signature with D and its constructors, both sides of
      every ι-rule check against one type, every compiled function is
      accepted against its declared type and satisfies its defining
      equations by conversion;
    - obligations: the general theorems for all descriptions, levels and
      case trees, among them that every signature they build is
      type-correct ([signature_typed] of the kernel's PTS.Typing: the
      premise of its declarative obligations, since a signature itself
      guarantees only closedness), and the normalization of the extended
      theory.

    Trusted beyond the Rocq kernel, as in lecture 6: the
    extraction to OCaml, the printer and the demos; the native reference
    in reference/ is covered only by differential tests. *)

From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Signature Typing Bidir.
From DepTypes.Configs Require Import Predicative.
From IndTypes.Elim Require Import Decl Generate Declare.
From Stdlib Require Import List.
Import ListNotations.

(** ** Classification (algorithm 1) *)

(** The types of D and of its constructors rebuilt from the classified
    description are the declared ones, also in the bypass mode. *)
Definition classification_faithful : Prop :=
  forall bypass d desc, classify_decl_with bypass d = Ok desc ->
  ind_name desc = rd_name d /\
  ind_type desc = pis (rd_params d ++ rd_indices d) (Srt (Univ (rd_level d))) /\
  Forall2 (fun rc cd => ctor_name cd = rc_name rc /\ ctor_type desc cd = pis (rd_params d) (rc_type rc))
    (rd_ctors d) (ind_ctors desc).

Theorem classification_faithful_holds : classification_faithful.
Proof. exact classify_decl_faithful. Qed.

(** Strict positivity: without the bypass no part of the description
    mentions D, so D occurs in the constructor types only as the head of
    the recursive fields and of the results. *)
Definition classification_strictly_positive : Prop :=
  forall d desc, classify_decl d = Ok desc -> desc_free desc = true.

Theorem classification_strictly_positive_holds : classification_strictly_positive.
Proof. exact classify_decl_strictly_positive. Qed.

(** ** Registration (algorithm 1) *)

(** A registered declaration was free in the signature, which gains
    exactly its entry; the types of D and of its constructors are types of
    the annotated kernel, and every field has a level at most that of D. *)
Definition declaration_sound : Prop :=
  forall S fuel bypass sg raw log log' sg' d,
  declare_ind_with S fuel bypass sg raw log = (log', Ok (sg', d)) ->
  classify_decl_with bypass raw = Ok d /\ sig_ind sg (rd_name raw) = None /\
  sig_entries sg' = EInd d :: sig_entries sg /\
  (exists s, is_type_of S sg' [] (ind_type d) s) /\
  Forall (fun c => (exists s, is_type_of S sg' [] (ctor_type d c) s) /\
                   fields_typed S sg' d (rev (ind_params d)) 0 (ctor_fields c)) (ind_ctors d).

Theorem declaration_sound_holds : declaration_sound.
Proof. intros S fuel. apply declare_ind_sound. Qed.

(** A registered instance has a type that is a type; both sides of every
    generated ι-rule check against its type, in its well-formed context, in
    the signature where the instance has no active rules; and only then is
    the instance added, with active rules. *)
Definition instance_sound : Prop :=
  forall S fuel sg D j log log' sg',
  declare_elim S fuel sg D j log = (log', Ok sg') ->
  exists d,
    sig_ind sg D = Some d /\ sig_elim sg D j = None /\
    (exists s, is_type_of S sg [] (elim_type d j) s) /\
    (exists tmp,
       sig_entries tmp = EElim D j (elim_type d j) false :: sig_entries sg /\
       forall r, In r (iota_rules d j) ->
         bwf_ctx S tmp (rule_ctx r) /\ btype S tmp (rule_ctx r) (rule_type r) /\
         chk S tmp (rule_ctx r) (rule_lhs r) (rule_type r) /\
         chk S tmp (rule_ctx r) (rule_rhs r) (rule_type r)) /\
    sig_entries sg' = EElim D j (elim_type d j) true :: sig_entries sg.

Theorem instance_sound_holds : instance_sound.
Proof. intros S fuel. apply declare_elim_sound. Qed.

(** A registered δ-constant has a type that is a type, and its body checks
    against it in the signature without the constant. *)
Definition definition_sound : Prop :=
  forall S fuel sg f A b log log' sg',
  define S fuel sg f A b log = (log', Ok sg') ->
  sig_def sg f = None /\ (exists s, is_type_of S sg [] A s) /\ chk S sg [] b A /\
  sig_entries sg' = EDef f A b :: sig_entries sg.

Theorem definition_sound_holds : definition_sound.
Proof. intros S fuel. apply define_sound. Qed.

(** ** Open obligations of algorithm 1

    Stated, not proved.  Every registration checks its own output (the
    contracts above); these are the general theorems behind those checks,
    for all declarations, levels and signatures built by registrations,
    and the metatheory the kernel's declarative obligations need from
    them.  The bypass mode is outside: its signatures pass every check,
    yet [δ (mk δ) : Void] holds there (Data.Positivity), so they are
    neither normalizing nor consistent. *)

(** Every declaration of the grammar is accepted.  A description is well
    formed when no part of it mentions D, every term is closed in its
    telescope, its constructors have distinct names, and every spine of D
    in it has as many indices as D.  The raw declaration rebuilt from
    such a description classifies back to it: the converse of
    [classification_faithful]. *)
Definition desc_well_formed (d : ind_desc) : Prop :=
  desc_free d = true /\ ind_closed d = true /\
  first_duplicate (map ctor_name (ind_ctors d)) = None /\
  Forall (fun c =>
    length (ctor_indices c) = length (ind_indices d) /\
    Forall (fun fd => match fd with
                      | FRec _ vs => length vs = length (ind_indices d)
                      | FArg _ => True
                      end) (ctor_fields c)) (ind_ctors d).

Definition raw_of (d : ind_desc) : raw_decl := {|
  rd_name := ind_name d; rd_params := ind_params d; rd_indices := ind_indices d;
  rd_level := ind_level d;
  rd_ctors := map (fun c =>
    mk_raw_ctor (ctor_name c)
      (pis (field_types (ind_name d) (length (ind_params d)) 0 (ctor_fields c))
           (apps (Const (Ind (ind_name d)))
                 (vars (length (ctor_fields c)) (length (ind_params d)) ++ ctor_indices c))))
    (ind_ctors d) |}.

Definition classification_complete : Prop :=
  forall d, desc_well_formed d -> classify_decl (raw_of d) = Ok d.

(** The general theorem behind the checks of [declare_elim], for every
    accepted declaration and every level [j]: in the signature with D and
    the instance without active rules, the type of the instance is a type,
    every context of a rule is well formed, and both sides of every
    generated ι-rule have its type, in the declarative rules. *)
Definition generated_instances_typed : Prop :=
  forall fuel sg raw log log' sg' d j tmp,
  signature_typed predicative sg ->
  declare_ind predicative fuel sg raw log = (log', Ok (sg', d)) ->
  sig_entries tmp = EElim (ind_name d) j (elim_type d j) false :: sig_entries sg' ->
  (exists s, has_type predicative tmp [] (elim_type d j) (Srt s)) /\
  forall r, In r (iota_rules d j) ->
    wf_ctx predicative tmp (rule_ctx r) /\
    has_type predicative tmp (rule_ctx r) (rule_lhs r) (rule_type r) /\
    has_type predicative tmp (rule_ctx r) (rule_rhs r) (rule_type r).

(** The signatures that registrations build from the empty one. *)
Inductive built : signature -> Prop :=
| BuiltEmpty : built ∅
| BuiltInd : forall fuel sg raw log log' sg' d,
    built sg -> declare_ind predicative fuel sg raw log = (log', Ok (sg', d)) -> built sg'
| BuiltElim : forall fuel sg D j log log' sg',
    built sg -> declare_elim predicative fuel sg D j log = (log', Ok sg') -> built sg'
| BuiltDef : forall fuel sg f A b log log' sg',
    built sg -> define predicative fuel sg f A b log = (log', Ok sg') -> built sg'.

(** The checks of an instance pass: for a declaration in a built signature,
    with enough fuel the registration of its instance at any level
    succeeds.  It rests on the normalization below and on the completeness
    of the kernel's checker. *)
Definition instances_registrable : Prop :=
  forall sg D d j, built sg -> sig_ind sg D = Some d -> sig_elim sg D j = None ->
  exists n, forall m, n <= m -> exists log sg', declare_elim predicative m sg D j [] = (log, Ok sg').

(** Built signatures are type-correct: the premise of the kernel's
    [progress] and [bidir_declarative_sound]. *)
Definition registrations_typed : Prop :=
  forall sg, built sg -> signature_typed predicative sg.

(** Built signatures are normalizing: the extended theory of the lecture,
    MLTT with strictly positive inductive families. *)
Definition registrations_normalizing : Prop :=
  forall sg, built sg -> normalizing_types predicative sg.

(** And consistent: no closed term has type Void.  Strict positivity is
    what the bypass gives up. *)
Definition registrations_consistent : Prop :=
  forall sg t, built sg -> ~ has_type predicative sg [] t Void.
