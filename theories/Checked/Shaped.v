(** * The types of the instances of a checked signature

    Every instance of a checked signature has the type the generator of
    elim-inductive-types gives it, [elim_type d s] for the declaration [d]
    of its family in the same signature ([checked_elim_types]); and that
    type is a telescope of the arity of the eliminator
    ([elim_type_shape]).  So a checked signature is [instances_shaped]
    (PTS/Values.v of the kernel): the contract [checked_instances_shaped]
    of erasure-cic.

    The invariant [elim_types_generated] (Checked/Invariants.v) is kept
    by every entry a registration adds: a declaration whose name is free, an instance at
    its generated type for a family already declared, a δ-constant.  The
    registrations are those of the steps of [wf_checked]: a declaration
    with its instances (algorithm 1), a δ-constant, and functions
    compiled by algorithm 2 with the history and the instances they need.
    An instance is registered once its name is free, so no later entry
    shadows it; a declaration once its name is free, so it does not
    shadow the family of an instance.

    The same walk keeps a second invariant: the constructors of every
    declaration have distinct names, which classification checks
    ([checked_ctors_distinct]).  The kernel's soundness for the
    declarative rules assumes it (PTS.BidirSound). *)

From Stdlib Require Import List Arith Lia Bool.
From Stdlib Require String.
Import ListNotations.
From DepTypes.Common Require Import Result Traced.
From DepTypes.PTS Require Import Syntax Spec Signature Inversion BidirSound Values.
From IndTypes Require Import Registration Telescope.
From IndTypes.Elim Require Import Decl Generate Declare.
From IndTypes.Recursion Require Import Below CaseTree Compile.
From IndTypes.Checked Require Import Steps Invariants Walk.

Local Open Scope list_scope.

(** ** The shape of the generated types *)

Lemma length_lifted : forall l i, length (lifted i l) = length l.
Proof. induction l as [|A l IH]; intros i; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma pis_nest : forall Ts1 A Ts2 Ts3 B R,
  pis Ts1 (Pi A (pis Ts2 (pis Ts3 (Pi B R)))) = pis (Ts1 ++ A :: Ts2 ++ Ts3 ++ [B]) R.
Proof. intros. rewrite pis_app. cbn [pis]. rewrite !pis_app. cbn [pis]. reflexivity. Qed.

(** [Π(Δ). ΠP. M̄ → Πθ̄. Πx. P θ̄ x]: a telescope of the arity of the
    eliminator. *)
Lemma elim_type_shape : forall d s, exists Ts R, elim_type d s = pis Ts R /\ length Ts = elim_arity d.
Proof.
  intros d s. unfold elim_type. rewrite pis_nest. eexists _, _. split; [reflexivity | ].
  rewrite ?length_app. cbn [length]. rewrite ?length_app, length_rename_tele.
  unfold methods. rewrite length_lifted, length_map. unfold elim_arity. cbn [length]. lia.
Qed.

Lemma generated_entries : forall sg sg', sig_entries sg' = sig_entries sg ->
  checked_inv sg -> checked_inv sg'.
Proof.
  intros sg sg' E [H Hc]. split.
  - intros D s A act He. unfold sig_elim in He. unfold sig_ind. rewrite E in He |- *.
    exact (H D s A act He).
  - intros D d Hd. unfold sig_ind in Hd. rewrite E in Hd. exact (Hc D d Hd).
Qed.

Lemma generated_empty : forall sg, sig_entries sg = [] -> checked_inv sg.
Proof.
  intros sg E. split.
  - intros D s A act He. unfold sig_elim in He. rewrite E in He. discriminate He.
  - intros D d Hd. unfold sig_ind in Hd. rewrite E in Hd. discriminate Hd.
Qed.

(** A declaration whose name is free, with distinct constructor names. *)
Lemma generated_add_ind : forall sg sg' d, checked_inv sg -> sig_ind sg (ind_name d) = None ->
  NoDup (map ctor_name (ind_ctors d)) ->
  sig_entries sg' = EInd d :: sig_entries sg -> checked_inv sg'.
Proof.
  intros sg sg' d [H Hc] Hn Hnd E. split.
  - intros D s A act He. unfold sig_elim, sig_ind in *. rewrite E in He |- *.
    cbn [find_elim find_ind] in He |- *.
    destruct (H D s A act He) as (d0 & Hd0 & ->). unfold sig_ind in Hd0.
    destruct (String.eqb (ind_name d) D) eqn:Ed.
    + apply String.eqb_eq in Ed. subst D. congruence.
    + exists d0. auto.
  - intros D d' Hd. unfold sig_ind in Hd. rewrite E in Hd. cbn [find_ind] in Hd.
    destruct (String.eqb (ind_name d) D); [injection Hd as <-; exact Hnd | exact (Hc D d' Hd)].
Qed.

(** An instance at its generated type, for a family declared. *)
Lemma generated_add_elim : forall sg sg' D s d act, checked_inv sg -> sig_ind sg D = Some d ->
  sig_entries sg' = EElim D s (elim_type d s) act :: sig_entries sg -> checked_inv sg'.
Proof.
  intros sg sg' D s d act [H Hc] Hd E. split.
  - intros D' s' A act' He. unfold sig_elim, sig_ind in *. rewrite E in He |- *.
    cbn [find_elim find_ind] in He |- *.
    destruct (String.eqb D D' && sort_eqb s s') eqn:Em.
    + injection He as <- <-. apply andb_prop in Em as [E1 E2].
      apply String.eqb_eq in E1. apply sort_eqb_eq in E2. subst. exists d. auto.
    + exact (H D' s' A act' He).
  - intros D' d' Hd'. unfold sig_ind in Hd'. rewrite E in Hd'. exact (Hc D' d' Hd').
Qed.

Lemma generated_add_def : forall sg sg' f A b, checked_inv sg ->
  sig_entries sg' = EDef f A b :: sig_entries sg -> checked_inv sg'.
Proof.
  intros sg sg' f A b [H Hc] E. split.
  - intros D s A' act He. unfold sig_elim, sig_ind in *. rewrite E in He |- *.
    cbn [find_elim find_ind] in He |- *. exact (H D s A' act He).
  - intros D d Hd. unfold sig_ind in Hd. rewrite E in Hd. exact (Hc D d Hd).
Qed.

(** ** The registrations keep it *)

(** The invariant of this file: kept by every registration, whatever its
    table. *)
Lemma declare_ind_generated : forall Sp fuel mode sg raw log log' sg' d,
  declare_ind_with Sp fuel mode sg raw log = (log', Ok (sg', d)) -> checked_inv sg -> checked_inv sg'.
Proof.
  intros Sp fuel mode sg raw log log' sg' d H Hg.
  destruct (declare_ind_sound Sp fuel _ _ _ _ _ _ _ H) as (d0 & sg1 & fss & Hc & Hn & _ & _ & _ & -> & E).
  eapply (generated_add_ind sg sg' _ Hg); [ | | exact E].
  - cbn [with_elim ind_name]. rewrite (classify_name _ _ _ Hc). exact Hn.
  - cbn [with_elim ind_ctors]. exact (classify_distinct _ _ _ Hc).
Qed.

Lemma declare_elim_generated : forall Sp fuel sg D s log log' sg',
  declare_elim Sp fuel sg D s log = (log', Ok sg') -> checked_inv sg -> checked_inv sg'.
Proof.
  intros Sp fuel sg D s log log' sg' H Hg. destruct (declare_elim_extends Sp fuel _ _ _ _ _ _ H) as (d & Hd & E).
  exact (generated_add_elim sg sg' D s d true Hg Hd E).
Qed.

Lemma define_generated : forall Sp fuel sg f A b log log' sg',
  define Sp fuel sg f A b log = (log', Ok sg') -> checked_inv sg -> checked_inv sg'.
Proof.
  intros Sp fuel sg f A b log log' sg' H Hg. destruct (define_sound Sp fuel _ _ _ _ _ _ _ H) as (_ & _ & _ & E).
  exact (generated_add_def sg sg' f A b Hg E).
Qed.

Lemma run_step_generated : forall sg st sg', checking_spec (step_spec st) -> run_step sg st = Some sg' ->
  checked_inv sg -> checked_inv sg'.
Proof.
  intros sg st sg' Hs H Hg. apply (walk_run_step checked_inv sg st sg'); try assumption.
  - intros Sp fuel sg0 raw log log' sg0' d _ H0. exact (declare_ind_generated _ _ _ _ _ _ _ _ _ H0).
  - intros Sp fuel sg0 D s log log' sg0' _ H0. exact (declare_elim_generated _ _ _ _ _ _ _ _ H0).
  - intros Sp fuel sg0 f A b log log' sg0' _ H0. exact (define_generated _ _ _ _ _ _ _ _ _ H0).
Qed.

(** ** Checked signatures *)

Theorem checked_invariant : forall sg, wf_checked sg -> checked_inv sg.
Proof.
  intros sg H. induction H as [sg E | sg st sg' sg'' _ IH Hs Hrun E].
  - exact (generated_empty sg E).
  - exact (generated_entries sg' sg'' E (run_step_generated _ _ _ Hs Hrun IH)).
Qed.

Corollary checked_elim_types : forall sg, wf_checked sg -> elim_types_generated sg.
Proof. intros sg H. exact (checked_generated (checked_invariant sg H)). Qed.

Corollary checked_ctors_distinct : forall sg, wf_checked sg -> ctors_distinct sg.
Proof. intros sg H. exact (checked_distinct (checked_invariant sg H)). Qed.

Corollary checked_shaped : forall sg, wf_checked sg -> instances_shaped sg.
Proof.
  intros sg H D s A act He. destruct (checked_elim_types sg H D s A act He) as (d & Hd & ->).
  destruct (elim_type_shape d s) as (Ts & R & E & Hl). exists d, Ts, R. auto.
Qed.
