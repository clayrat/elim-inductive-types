(** * The walk over the registrations of a checked signature

    A step of [wf_checked] (Checked/Steps.v) is a registration: a
    declaration with its instances (algorithm 1), a δ-constant, or
    functions compiled by algorithm 2 with the history and the instances
    they need.  Each of them adds entries only through three
    registrations: a checked declaration ([declare_ind_with] in the mode
    [Checked]), an instance ([declare_elim]) and a δ-constant
    ([define]).  So a step keeps every invariant of signatures that
    these three keep ([walk_run_step]), whatever the table a step checks
    in; the invariants of Checked/Shaped.v and Checked/SigTyped.v are
    proved so. *)

From Stdlib Require Import List.
Import ListNotations.
From DepTypes.Common Require Import Result Traced.
From DepTypes.PTS Require Import Syntax Spec Signature.
From IndTypes Require Import Registration.
From IndTypes.Elim Require Import Decl Declare.
From IndTypes.Recursion Require Import Below CaseTree Compile.
From IndTypes.Checked Require Import Steps.

(** The walk over the registrations of a step, for any invariant kept
    by a checked declaration, an instance and a δ-constant. *)
Section Walk.
  Variable Sp : spec.
  Variable fuel : nat.
  Variable I : signature -> Prop.
  Hypothesis I_ind : forall sg raw log log' sg' d,
    declare_ind_with Sp fuel Checked sg raw log = (log', Ok (sg', d)) -> I sg -> I sg'.
  Hypothesis I_elim : forall sg D s log log' sg',
    declare_elim Sp fuel sg D s log = (log', Ok sg') -> I sg -> I sg'.
  Hypothesis I_def : forall sg f A b log log' sg',
    define Sp fuel sg f A b log = (log', Ok sg') -> I sg -> I sg'.

  Lemma walk_declare_elims : forall sorts D sg log log' sg',
    tfold (fun sg s => declare_elim_with Sp fuel CheckElim sg D s) sg sorts log = (log', Ok sg') ->
    I sg -> I sg'.
  Proof.
    induction sorts as [|s sorts IH]; intros D sg log log' sg' H Hg; cbn [tfold] in H.
    - apply tret_ok in H. subst. exact Hg.
    - tbind_in H sg2 H2. exact (IH _ _ _ _ _ H (I_elim _ _ _ _ _ _ H2 Hg)).
  Qed.

  (** A declaration and its instances. *)
  Lemma walk_declare : forall sg raw sorts log log' sg',
    declare Sp fuel sg raw sorts log = (log', Ok sg') -> I sg -> I sg'.
  Proof.
    intros sg raw sorts log log' sg' H Hg. unfold declare, declare_with in H.
    tbind_in H r Hr. destruct r as [sg1 d]. cbn [fst] in H.
    exact (walk_declare_elims _ _ _ _ _ _ H (I_ind _ _ _ _ _ _ Hr Hg)).
  Qed.

  Lemma walk_ensure_unit : forall sg l log log' sg',
    ensure_unit Sp fuel sg l log = (log', Ok sg') -> I sg -> I sg'.
  Proof.
    intros sg l log log' sg' H Hg. unfold ensure_unit in H.
    destruct l as [|l]; [apply tret_ok in H; subst; exact Hg | ].
    destruct (sig_ind sg (unit_name (S l))); [apply tret_ok in H; subst; exact Hg | ].
    tbind_in H r Hr. apply tret_ok in H. subst sg'. destruct r as [sg1 d].
    exact (I_ind _ _ _ _ _ _ Hr Hg).
  Qed.

  Lemma walk_ensure_elim : forall sg D s log log' sg',
    ensure_elim Sp fuel sg D s log = (log', Ok sg') -> I sg -> I sg'.
  Proof.
    intros sg D s log log' sg' H Hg. unfold ensure_elim in H.
    destruct (sig_elim sg D s) as [[T [|]]|]; [apply tret_ok in H; subst; exact Hg | | ].
    all: exact (I_elim _ _ _ _ _ _ H Hg).
  Qed.

  (** The history of algorithm 2: [Unit_ℓ], two instances and three
      δ-constants. *)
  Lemma walk_ensure_below : forall sg D j log log' sg',
    ensure_below Sp fuel sg D j log = (log', Ok sg') -> I sg -> I sg'.
  Proof.
    intros sg D j log log' sg' H Hg. unfold ensure_below in H.
    destruct (sig_def sg (recbelow_name D j)); [apply tret_ok in H; subst; exact Hg | ].
    tbind_in H d0 Hd. tbind_in H l Hl.
    tbind_in H sg1 H1. tbind_in H sg2 H2. tbind_in H sg3 H3.
    tbind_in H sg4 H4. tbind_in H sg5 H5.
    apply (I_def _ _ _ _ _ _ _ H), (I_def _ _ _ _ _ _ _ H5),
      (I_def _ _ _ _ _ _ _ H4), (walk_ensure_elim _ _ _ _ _ _ H3),
      (walk_ensure_elim _ _ _ _ _ _ H2), (walk_ensure_unit _ _ _ _ _ H1).
    exact Hg.
  Qed.

  Lemma walk_instances : forall needed sg log log' sg',
    tfold (fun sg '(D, k) => ensure_elim Sp fuel sg D (Univ k)) sg needed log = (log', Ok sg') ->
    I sg -> I sg'.
  Proof.
    induction needed as [|[D k] needed IH]; intros sg log log' sg' H Hg; cbn in H.
    - apply tret_ok in H. subst. exact Hg.
    - tbind_in H sg1 H1. exact (IH _ _ _ _ H (walk_ensure_elim _ _ _ _ _ _ H1 Hg)).
  Qed.

  Lemma walk_compile_term : forall sg fn log log' sg0 A b eqs,
    compile_term Sp fuel sg fn log = (log', Ok (sg0, A, b, eqs)) -> I sg -> I sg0.
  Proof.
    intros sg fn log log' sg0 A b eqs H Hg. unfold compile_term, compile_with in H.
    tbind_in H s0 Hs. destruct s0 as [[G0 goal0] env0].
    tbind_in H si Hp.
    tbind_in H w Hw.
    tbind_in H r Hr. destruct r as [[[sg1 root] needed] e].
    tbind_in H w' Hw'.
    tbind_in H sg2 H2. apply tret_ok in H. injection H as <- _ _ _.
    apply (walk_instances _ _ _ _ _ H2).
    destruct (fn_strategy fn).
    - unfold compile_direct in Hr.
      tbind_in Hr u Hu. tbind_in Hr e' He. tbind_in Hr t Ht.
      apply tret_ok in Hr. injection Hr as <- _ _ _. exact Hg.
    - unfold compile_history in Hr.
      tbind_in Hr j Hj. tbind_in Hr sg1' H1.
      match type of Hr with context [introduce ?G ?gn ?B ?vs] => destruct (introduce G gn B vs) as [[G1 goal1] sb] end.
      tbind_in Hr e' He. tbind_in Hr t Ht.
      apply tret_ok in Hr. injection Hr as <- _ _ _.
      exact (walk_ensure_below _ _ _ _ _ _ H1 Hg).
  Qed.

  Lemma walk_compile : forall sg fn log log' sg',
    compile Sp fuel sg fn log = (log', Ok sg') -> I sg -> I sg'.
  Proof.
    intros sg fn log log' sg' H Hg. unfold compile in H.
    tbind_in H r Hr. destruct r as [[[sg0 A] b] eqs].
    tbind_in H sg1 H1. tbind_in H u Hu. apply tret_ok in H. subst sg1.
    exact (I_def _ _ _ _ _ _ _ H1 (walk_compile_term _ _ _ _ _ _ _ _ Hr Hg)).
  Qed.

  Lemma walk_compile_all : forall fns sg log log' sg',
    tfold (compile Sp fuel) sg fns log = (log', Ok sg') -> I sg -> I sg'.
  Proof.
    induction fns as [|fn fns IH]; intros sg log log' sg' H Hg; cbn [tfold] in H.
    - apply tret_ok in H. subst. exact Hg.
    - tbind_in H sg1 H1. exact (IH _ _ _ _ H (walk_compile _ _ _ _ _ H1 Hg)).
  Qed.
End Walk.

(** A step keeps an invariant that every checked registration of its
    table keeps. *)
Theorem walk_run_step : forall (I : signature -> Prop) sg st sg',
  (forall Sp fuel sg raw log log' sg' d, checking_spec Sp ->
     declare_ind_with Sp fuel Checked sg raw log = (log', Ok (sg', d)) -> I sg -> I sg') ->
  (forall Sp fuel sg D s log log' sg', checking_spec Sp ->
     declare_elim Sp fuel sg D s log = (log', Ok sg') -> I sg -> I sg') ->
  (forall Sp fuel sg f A b log log' sg', checking_spec Sp ->
     define Sp fuel sg f A b log = (log', Ok sg') -> I sg -> I sg') ->
  checking_spec (step_spec st) -> run_step sg st = Some sg' -> I sg -> I sg'.
Proof.
  intros I sg st sg' Hi He Hd Hs H Hg.
  destruct st as [Sp fuel raw sorts | Sp fuel f A b | Sp fuel fns]; cbn [run_step step_spec] in H, Hs.
  - apply registered_run in H as [log H].
    exact (walk_declare Sp fuel I (fun sg0 raw log log' sg0' d => Hi Sp fuel sg0 raw log log' sg0' d Hs)
               (fun sg0 D s log log' sg0' => He Sp fuel sg0 D s log log' sg0' Hs) _ _ _ _ _ _ H Hg).
  - apply registered_run in H as [log H].
    exact (Hd Sp fuel _ _ _ _ _ _ _ Hs H Hg).
  - apply registered_run in H as [log H].
    exact (walk_compile_all Sp fuel I (fun sg0 raw log log' sg0' d => Hi Sp fuel sg0 raw log log' sg0' d Hs)
               (fun sg0 D s log log' sg0' => He Sp fuel sg0 D s log log' sg0' Hs)
               (fun sg0 f A b log log' sg0' => Hd Sp fuel sg0 f A b log log' sg0' Hs) _ _ _ _ _ H Hg).
Qed.

