(** * Checked signatures are type-correct

    [signature_typed] asks three things of a signature: the types of the
    constants are types, every δ-body has the type of its constant, and
    every ι-contraction keeps the type of the redex.  A checked signature
    ([wf_checked]) is built by registrations that check each entry with
    the kernel's checker: the type and the body of a δ-constant in the
    signature before it, the type of an instance in the signature before
    it and its ι-rules in a signature where it is inactive, the types of
    a declaration and of its constructors in the signature where the
    declaration is added.

    The invariant kept by the registrations ([sig_inv]) is the first two
    conditions, the generated types of the instances with their rules
    typed by the declarative rules in their generic contexts
    ([instances_checked] of Checked/Invariants.v), and the invariant of
    Checked/Shaped.v.  The third condition follows from it by the lemma
    on ι ([iota_typed]), so the invariant gives a type-correct signature
    ([inv_typed]), and with it the soundness of the checker for the
    declarative rules (PTS/BidirSound.v) carries the checks of the next
    registration over.  The checks of the hierarchy without Prop are
    checks of the one with Prop ([bidir_spec_mono]); a judgment of a
    signature holds in every extension ([typing_sig_mono]).

    A δ-constant and an instance are covered so.  A declaration is
    checked in the signature that contains it, whose type-correctness
    asks of these very types that they be types, so the soundness of the
    checker does not apply there directly.  Its check mentions D only as
    [Ind D]: the type of D not at all, and is a check in the signature
    before it; the type of a constructor, renamed to an inactive instance
    of the type of D, is a check in a type-correct signature without the
    declaration, and renamed back a declarative judgment in the signature
    with it (PTS/ConstRename.v of the kernel, [declaration_typed_holds]).  So every
    checked signature is type-correct ([checked_typed]). *)

From Stdlib Require Import List Arith Lia Bool.
From Stdlib Require String.
Import ListNotations.
From DepTypes.Common Require Import Result Traced Lists.
From DepTypes.PTS Require Import Syntax Spec Signature Reduction Typing TypingSubst Inversion Bidir
  BidirSound Monotone ConstRename.
From DepTypes.Configs Require Import Predicative.
From IndTypes Require Import Registration.
From IndTypes.Elim Require Import Decl Generate Declare.
From IndTypes.Checked Require Import Steps Invariants Walk Shaped IotaTyped.

Local Open Scope list_scope.

Local Notation SP := predicative_prop.

(** ** The invariant *)

Theorem inv_typed : forall sg, sig_inv sg -> signature_typed SP sg.
Proof.
  intros sg [Hty Hb Hi _]. split; [exact Hty | split; [exact Hb | ]].
  intros G t u T Hu Ht. exact (iota_typed SP sg Hty predicative_prop_full Hi G t u T Hu Ht).
Qed.

Lemma rules_typed_mono : forall sg sg' d s, sig_le sg sg' -> rules_typed SP sg d s -> rules_typed SP sg' d s.
Proof. intros sg sg' d s Hle H r Hr. exact (typed_sig_mono SP sg sg' Hle _ _ _ (H r Hr)). Qed.

(** ** The checks, read by the declarative rules *)

Lemma checking_le : forall Sp, checking_spec Sp -> spec_le Sp SP.
Proof.
  intros Sp H. destruct H; [exact predicative_le_prop | ].
  constructor; auto.
Qed.

Section Checks.
  Variable sg : signature.
  Hypothesis Hsig : signature_typed SP sg.
  Hypothesis Hdist : ctors_distinct sg.
  Variable Sp : spec.
  Hypothesis HSp : checking_spec Sp.

  Lemma is_type_typed : forall G A s, bwf_ctx Sp sg G -> is_type_of Sp sg G A s -> has_type SP sg G A (Srt s).
  Proof.
    intros G A s HG (T & HA & Hr).
    pose proof (checking_le _ HSp) as Hle.
    destruct (synth_sound SP sg Hsig (fun _ => predicative_prop_full) Hdist G A T
                (bwf_spec_mono _ _ _ Hle _ HG) (proj1 (bidir_spec_mono _ _ _ Hle) _ _ _ HA)) as [_ Ht].
    exact (typed_red_srt SP sg Hsig _ _ _ _ Ht Hr).
  Qed.

  Lemma chk_typed : forall G t A, bwf_ctx Sp sg G -> btype Sp sg G A -> chk Sp sg G t A -> has_type SP sg G t A.
  Proof.
    intros G t A HG HA H. pose proof (checking_le _ HSp) as Hle.
    exact (chk_sound SP sg Hsig (fun _ => predicative_prop_full) Hdist G t A
             (bwf_spec_mono _ _ _ Hle _ HG) (btype_spec_mono _ _ _ Hle _ _ HA)
             (proj1 (proj2 (bidir_spec_mono _ _ _ Hle)) _ _ _ H)).
  Qed.
End Checks.

(** ** The registrations keep it *)

Lemma define_inv : forall Sp fuel sg f A b log log' sg', checking_spec Sp ->
  define Sp fuel sg f A b log = (log', Ok sg') -> sig_inv sg -> sig_inv sg'.
Proof.
  intros Sp fuel sg f A b log log' sg' HSp H Hinv.
  pose proof (define_generated _ _ _ _ _ _ _ _ _ H (inv_checked Hinv)) as Hc'.
  pose proof (inv_typed _ Hinv) as Hsig.
  destruct (define_sound Sp fuel _ _ _ _ _ _ _ H) as (Hf & [s HA] & Hb & E).
  destruct Hinv as [Hty Hbd Hins Hc].
  pose proof (is_type_typed sg Hsig (checked_distinct Hc) Sp HSp [] A s (BW_Nil _ _) HA) as HA'.
  assert (HAb : btype Sp sg [] A) by (destruct HA as (T & HT & Hr); right; exists T, s; split; assumption).
  pose proof (chk_typed sg Hsig (checked_distinct Hc) Sp HSp [] b A (BW_Nil _ _) HAb Hb) as Hb'.
  pose proof (sig_le_def _ _ _ _ _ Hf E) as Hle.
  split; [ | | | exact Hc'].
  - intros [D | D c | D s0 | f'] T HT.
    + destruct (Hty (Ind D) T ltac:(cbn [sig_type] in *; rewrite (add_def_ind _ _ _ _ _ E) in HT; exact HT)) as [s' Hs'].
      exists s'. exact (typed_sig_mono _ _ _ Hle _ _ _ Hs').
    + destruct (Hty (Ctor D c) T ltac:(cbn [sig_type] in *; rewrite (add_def_ind _ _ _ _ _ E) in HT; exact HT)) as [s' Hs'].
      exists s'. exact (typed_sig_mono _ _ _ Hle _ _ _ Hs').
    + destruct (Hty (Elim D s0) T ltac:(cbn [sig_type] in *; rewrite (add_def_elim _ _ _ _ _ E) in HT; exact HT)) as [s' Hs'].
      exists s'. exact (typed_sig_mono _ _ _ Hle _ _ _ Hs').
    + cbn [sig_type] in HT. rewrite (add_def_def _ _ _ _ _ E) in HT.
      destruct (String.eqb f f') eqn:Ef.
      * injection HT as <-. exists s. exact (typed_sig_mono _ _ _ Hle _ _ _ HA').
      * destruct (Hty (Def f') T HT) as [s' Hs']. exists s'. exact (typed_sig_mono _ _ _ Hle _ _ _ Hs').
  - intros [D | D c | D s0 | f'] T b0 HT Hd; cbn [sig_delta] in Hd; try discriminate Hd.
    cbn [sig_type] in HT. rewrite (add_def_def _ _ _ _ _ E) in HT, Hd.
    destruct (String.eqb f f') eqn:Ef.
    + injection HT as <-. injection Hd as <-. exact (typed_sig_mono _ _ _ Hle _ _ _ Hb').
    + apply (typed_sig_mono _ _ _ Hle). apply (Hbd (Def f') T b0); cbn [sig_type sig_delta]; [exact HT | exact Hd].
  - intros D s0 T He. rewrite (add_def_elim _ _ _ _ _ E) in He.
    destruct (Hins D s0 T He) as (d & Hd & -> & Hr). exists d. split; [exact (le_ind _ _ Hle _ _ Hd) | ].
    split; [reflexivity | exact (rules_typed_mono _ _ _ _ Hle Hr)].
Qed.

Lemma declare_elim_inv : forall Sp fuel sg D s log log' sg', checking_spec Sp ->
  declare_elim Sp fuel sg D s log = (log', Ok sg') -> sig_inv sg -> sig_inv sg'.
Proof.
  intros Sp fuel sg D s log log' sg' HSp H Hinv.
  pose proof (declare_elim_generated _ _ _ _ _ _ _ _ H (inv_checked Hinv)) as Hc'.
  pose proof (inv_typed _ Hinv) as Hsig.
  destruct (declare_elim_sound Sp fuel _ _ _ _ _ _ H) as (d & Hd & Hn & _ & [s' HT] & (tmp & Et & Hr) & E).
  destruct Hinv as [Hty Hbd Hins Hc].
  pose proof (is_type_typed sg Hsig (checked_distinct Hc) Sp HSp [] _ s' (BW_Nil _ _) HT) as HT'.
  (* the signature where the rules are checked *)
  pose proof (sig_le_elim _ _ _ _ _ _ Hn Et) as Hle1.
  assert (Htmp : sig_inv tmp).
  { split.
    - intros [D' | D' c | D' s0 | f] T HT0.
      + destruct (Hty (Ind D') T ltac:(cbn [sig_type] in *; rewrite (add_elim_ind _ _ _ _ _ _ Et) in HT0; exact HT0))
          as [s1 Hs1]. exists s1. exact (typed_sig_mono _ _ _ Hle1 _ _ _ Hs1).
      + destruct (Hty (Ctor D' c) T ltac:(cbn [sig_type] in *; rewrite (add_elim_ind _ _ _ _ _ _ Et) in HT0; exact HT0))
          as [s1 Hs1]. exists s1. exact (typed_sig_mono _ _ _ Hle1 _ _ _ Hs1).
      + cbn [sig_type] in HT0. rewrite (add_elim_elim _ _ _ _ _ _ Et) in HT0.
        destruct (String.eqb D D' && sort_eqb s s0) eqn:Em.
        * injection HT0 as <-. exists s'. exact (typed_sig_mono _ _ _ Hle1 _ _ _ HT').
        * destruct (Hty (Elim D' s0) T HT0) as [s1 Hs1]. exists s1. exact (typed_sig_mono _ _ _ Hle1 _ _ _ Hs1).
      + destruct (Hty (Def f) T ltac:(cbn [sig_type] in *; rewrite (add_elim_def _ _ _ _ _ _ Et) in HT0; exact HT0))
          as [s1 Hs1]. exists s1. exact (typed_sig_mono _ _ _ Hle1 _ _ _ Hs1).
    - intros [D' | D' c | D' s0 | f] T b0 HT0 Hb0; cbn [sig_delta] in Hb0; try discriminate Hb0.
      cbn [sig_type] in HT0. rewrite (add_elim_def _ _ _ _ _ _ Et) in HT0, Hb0.
      apply (typed_sig_mono _ _ _ Hle1). apply (Hbd (Def f) T b0); cbn [sig_type sig_delta]; assumption.
    - intros D' s0 T He. rewrite (add_elim_elim _ _ _ _ _ _ Et) in He.
      destruct (String.eqb D D' && sort_eqb s s0); [discriminate He | ].
      destruct (Hins D' s0 T He) as (d' & Hd' & -> & Hr'). exists d'. split; [exact (le_ind _ _ Hle1 _ _ Hd') | ].
      split; [reflexivity | exact (rules_typed_mono _ _ _ _ Hle1 Hr')].
    - exact (generated_add_elim sg tmp D s d false Hc Hd Et). }
  pose proof (inv_typed _ Htmp) as Hsig_tmp.
  assert (Hrules : rules_typed SP tmp d s).
  { intros r Hin. destruct (Hr r Hin) as (Hctx & Hty' & _ & Hrhs).
    exact (chk_typed tmp Hsig_tmp (checked_distinct (inv_checked Htmp)) Sp HSp _ _ _ Hctx Hty' Hrhs). }
  (* the signature with the instance active *)
  pose proof (sig_le_elim _ _ _ _ _ _ Hn E) as Hle2.
  pose proof (sig_le_activate _ _ _ _ _ _ Et E) as Hle3.
  split; [ | | | exact Hc'].
  - intros [D' | D' c | D' s0 | f] T HT0.
    + destruct (Hty (Ind D') T ltac:(cbn [sig_type] in *; rewrite (add_elim_ind _ _ _ _ _ _ E) in HT0; exact HT0))
        as [s1 Hs1]. exists s1. exact (typed_sig_mono _ _ _ Hle2 _ _ _ Hs1).
    + destruct (Hty (Ctor D' c) T ltac:(cbn [sig_type] in *; rewrite (add_elim_ind _ _ _ _ _ _ E) in HT0; exact HT0))
        as [s1 Hs1]. exists s1. exact (typed_sig_mono _ _ _ Hle2 _ _ _ Hs1).
    + cbn [sig_type] in HT0. rewrite (add_elim_elim _ _ _ _ _ _ E) in HT0.
      destruct (String.eqb D D' && sort_eqb s s0) eqn:Em.
      * injection HT0 as <-. exists s'. exact (typed_sig_mono _ _ _ Hle2 _ _ _ HT').
      * destruct (Hty (Elim D' s0) T HT0) as [s1 Hs1]. exists s1. exact (typed_sig_mono _ _ _ Hle2 _ _ _ Hs1).
    + destruct (Hty (Def f) T ltac:(cbn [sig_type] in *; rewrite (add_elim_def _ _ _ _ _ _ E) in HT0; exact HT0))
        as [s1 Hs1]. exists s1. exact (typed_sig_mono _ _ _ Hle2 _ _ _ Hs1).
  - intros [D' | D' c | D' s0 | f] T b0 HT0 Hb0; cbn [sig_delta] in Hb0; try discriminate Hb0.
    cbn [sig_type] in HT0. rewrite (add_elim_def _ _ _ _ _ _ E) in HT0, Hb0.
    apply (typed_sig_mono _ _ _ Hle2). apply (Hbd (Def f) T b0); cbn [sig_type sig_delta]; assumption.
  - intros D' s0 T He. rewrite (add_elim_elim _ _ _ _ _ _ E) in He.
    destruct (String.eqb D D' && sort_eqb s s0) eqn:Em.
    + injection He as <-. apply andb_prop in Em as [E1 E2]. apply String.eqb_eq in E1. apply sort_eqb_eq in E2.
      subst D' s0. exists d. split; [exact (le_ind _ _ Hle2 _ _ Hd) | ].
      split; [reflexivity | exact (rules_typed_mono _ _ _ _ Hle3 Hrules)].
    + destruct (Hins D' s0 T He) as (d' & Hd' & -> & Hr'). exists d'. split; [exact (le_ind _ _ Hle2 _ _ Hd') | ].
      split; [reflexivity | exact (rules_typed_mono _ _ _ _ Hle2 Hr')].
Qed.

(** ** The types of a declaration

    The types of a declaration are checked in [sg1], with D.  The type of
    D does not mention D: renamed by the identity, its check is a check
    in [sg].  The type of a constructor mentions D only as [Ind D]:
    renamed to an inactive instance [Elim D Prp] of the same type, its
    check is a check in [sgn], the signature [sg] with that instance
    alone, which is type-correct once the type of D is a type.  Renamed
    back, the declarative judgment of [sgn] is one of [sg'], where
    [Ind D] has that type (PTS/ConstRename.v of the kernel). *)

Definition notD (D : String.string) (g : gref) : bool := negb (of_family D g).
Definition notDk (D : String.string) (D' : String.string) : bool := negb (String.eqb D' D).
Definition onlyInd (D : String.string) (g : gref) : bool :=
  match g with Ctor D' _ | Elim D' _ => negb (String.eqb D' D) | _ => true end.
Definition fwd (D : String.string) (g : gref) : gref :=
  match g with Ind D' => if String.eqb D' D then Elim D Prp else g | _ => g end.
Definition bwd (D : String.string) (g : gref) : gref :=
  match g with Elim D' s => if String.eqb D' D && sort_eqb s Prp then Ind D else g | _ => g end.

Lemma notD_fwd : forall D g, notD D g = true -> fwd D g = g.
Proof.
  intros D [D' | D' c | D' s | f] H; unfold notD in H; cbn [of_family fwd] in *; try reflexivity.
  destruct (String.eqb D' D); [discriminate H | reflexivity].
Qed.

Lemma notD_bwd : forall D g, notD D g = true -> bwd D g = g.
Proof.
  intros D [D' | D' c | D' s | f] H; unfold notD in H; cbn [of_family bwd] in *; try reflexivity.
  destruct (String.eqb D' D); [discriminate H | reflexivity].
Qed.

Lemma onlyInd_back : forall D g, onlyInd D g = true -> bwd D (fwd D g) = g.
Proof.
  intros D [D' | D' c | D' s | f] H; cbn [onlyInd fwd] in *; try reflexivity.
  - destruct (String.eqb D' D) eqn:E; [ | reflexivity].
    cbn [bwd]. rewrite String.eqb_refl. cbn. apply String.eqb_eq in E. subst. reflexivity.
  - cbn [bwd]. destruct (String.eqb D' D); [discriminate H | reflexivity].
Qed.

Lemma notD_onlyInd : forall D g, notD D g = true -> onlyInd D g = true.
Proof. intros D [D' | D' c | D' s | f] H; unfold notD in H; cbn [of_family onlyInd] in *; auto. Qed.

Lemma notD_true : forall D D', notDk D D' = true -> D' <> D.
Proof. intros D D' H E. subst. unfold notDk in H. rewrite String.eqb_refl in H. discriminate H. Qed.

Lemma neq_notDk : forall D D', D' <> D -> notDk D D' = true.
Proof. intros D D' H. unfold notDk. destruct (String.eqb D' D) eqn:E; [apply String.eqb_eq in E; contradiction | reflexivity]. Qed.

Lemma mentions_an : forall D t, mentions D t = false -> allnodes (notD D) (notDk D) t = true.
Proof.
  intros D t. induction t using term_ind'; intros H; cbn [mentions allnodes] in *;
    repeat match goal with H : _ || _ = false |- _ => apply orb_false_iff in H as [? ?] end;
    repeat (apply andb_true_intro; split); auto.
  - unfold notD. rewrite H. reflexivity.
  - unfold notDk. match goal with H : String.eqb _ _ = false |- _ => rewrite H end. reflexivity.
  - rewrite forallb_forall. intros b Hb. rewrite Forall_forall in IHl. apply IHl; [exact Hb | ].
    destruct (mentions D b) eqn:E; [ | reflexivity]. exfalso.
    match goal with H : ?X = false |- _ =>
      lazymatch X with context [existsb] =>
        assert (Hx : X = true) by (apply existsb_exists; exists b; auto); rewrite Hx in H; discriminate H end end.
Qed.

Lemma free_an : forall D t, free_of D t = true -> allnodes (notD D) (notDk D) t = true.
Proof. intros D t H. apply mentions_an. unfold free_of in H. destruct (mentions D t); [discriminate H | reflexivity]. Qed.

Lemma fixok_pis : forall pcf pkf Ts R, fixok pcf pkf (pis Ts R) = forallb (fixok pcf pkf) Ts && fixok pcf pkf R.
Proof.
  intros pcf pkf Ts. induction Ts as [|T Ts IH]; intros R; [reflexivity | ].
  cbn [pis fixok forallb]. rewrite IH. apply andb_assoc.
Qed.

Lemma fixok_apps : forall pcf pkf l h, fixok pcf pkf (apps h l) = fixok pcf pkf h && forallb (fixok pcf pkf) l.
Proof.
  intros pcf pkf l. induction l as [|a l IH]; intros h; cbn [forallb]; [rewrite andb_true_r; reflexivity | ].
  change (apps h (a :: l)) with (apps (App h a) l). rewrite IH. cbn [fixok]. symmetry. apply andb_assoc.
Qed.

Lemma fixok_vars : forall pcf pkf base n, forallb (fixok pcf pkf) (vars base n) = true.
Proof. intros pcf pkf base n. induction n as [|n IH]; [reflexivity | exact IH]. Qed.

(** The free terms of a description, read off its field types. *)
Lemma fields_vs : forall pc pk D p fs l Bs vs,
  Forall (fun T => allnodes pc pk T = true) (field_types D p l fs) -> In (FRec Bs vs) fs ->
  forallb (allnodes pc pk) vs = true.
Proof.
  intros pc pk D p fs. induction fs as [|fd fs IH]; intros l Bs vs H Hin; [destruct Hin | ].
  cbn [field_types] in H. inversion H as [|? ? Hfd Hfs]; subst. destruct Hin as [-> | Hin].
  - cbn [field_type] in Hfd. rewrite an_pis, an_apps, forallb_app in Hfd.
    apply andb_prop in Hfd as [_ Hfd]. apply andb_prop in Hfd as [_ Hfd]. apply andb_prop in Hfd as [_ Hfd]. exact Hfd.
  - exact (IH _ _ _ Hfs Hin).
Qed.

(** The type of a constructor of a description free of D. *)
Lemma ctor_type_good : forall d c, desc_free d = true -> In c (ind_ctors d) ->
  allnodes (onlyInd (ind_name d)) (notDk (ind_name d)) (ctor_type d c) = true /\
  fixok (notD (ind_name d)) (notDk (ind_name d)) (ctor_type d c) = true.
Proof.
  intros d c Hf Hc. unfold desc_free in Hf. cbv zeta in Hf. apply andb_prop in Hf as [Hpi Hcs].
  rewrite forallb_app in Hpi. apply andb_prop in Hpi as [Hp _].
  rewrite forallb_forall in Hcs. pose proof (Hcs c Hc) as Hcc. apply andb_prop in Hcc as [Hfs Hidx].
  set (D := ind_name d) in *.
  assert (Hw : forall t, free_of D t = true -> allnodes (onlyInd D) (notDk D) t = true /\ fixok (notD D) (notDk D) t = true).
  { intros t Ht. pose proof (free_an _ _ Ht) as H. split; [ | exact (fixok_of_an _ _ _ H)].
    exact (an_weaken _ _ _ _ _ (notD_onlyInd D) (fun _ x => x) H). }
  assert (Hft : forall fs l, forallb (field_free D) fs = true ->
            forallb (allnodes (onlyInd D) (notDk D)) (field_types D (length (ind_params d)) l fs) = true /\
            forallb (fixok (notD D) (notDk D)) (field_types D (length (ind_params d)) l fs) = true).
  { intros fs. induction fs as [|fd fs IH]; intros l H; [split; reflexivity | ].
    cbn [forallb] in H. apply andb_prop in H as [Hfd H]. destruct (IH (Datatypes.S l) H) as [IH1 IH2].
    cbn [field_types forallb]. rewrite IH1, IH2, !andb_true_r.
    destruct fd as [A | Bs vs]; cbn [field_free field_type] in *.
    - exact (Hw A Hfd).
    - apply andb_prop in Hfd as [HBs Hvs]. rewrite an_pis, fixok_pis, an_apps, fixok_apps, !forallb_app.
      cbn [allnodes fixok onlyInd]. rewrite an_vars, fixok_vars.
      assert (HB : forallb (allnodes (onlyInd D) (notDk D)) Bs = true /\ forallb (fixok (notD D) (notDk D)) Bs = true).
      { rewrite !forallb_forall in *. split; intros x Hx; exact (proj1 (Hw x (HBs x Hx))) || exact (proj2 (Hw x (HBs x Hx))). }
      assert (HV : forallb (allnodes (onlyInd D) (notDk D)) vs = true /\ forallb (fixok (notD D) (notDk D)) vs = true).
      { rewrite !forallb_forall in *. split; intros x Hx; exact (proj1 (Hw x (Hvs x Hx))) || exact (proj2 (Hw x (Hvs x Hx))). }
      rewrite (proj1 HB), (proj2 HB), (proj1 HV), (proj2 HV). split; reflexivity. }
  destruct (Hft (ctor_fields c) 0 Hfs) as [HF1 HF2].
  assert (HP : forallb (allnodes (onlyInd D) (notDk D)) (ind_params d) = true /\ forallb (fixok (notD D) (notDk D)) (ind_params d) = true).
  { rewrite !forallb_forall in *. split; intros x Hx; exact (proj1 (Hw x (Hp x Hx))) || exact (proj2 (Hw x (Hp x Hx))). }
  assert (HI : forallb (allnodes (onlyInd D) (notDk D)) (ctor_indices c) = true /\ forallb (fixok (notD D) (notDk D)) (ctor_indices c) = true).
  { rewrite !forallb_forall in *. split; intros x Hx; exact (proj1 (Hw x (Hidx x Hx))) || exact (proj2 (Hw x (Hidx x Hx))). }
  unfold ctor_type. cbv zeta. fold D.
  rewrite an_pis, fixok_pis, an_apps, fixok_apps, !forallb_app. cbn [allnodes fixok onlyInd].
  rewrite an_vars, fixok_vars, (proj1 HP), (proj2 HP), HF1, HF2, (proj1 HI), (proj2 HI). split; reflexivity.
Qed.

Section Declaration.
  Variable sg : signature.
  Hypothesis Hinv : sig_inv sg.
  Variable d0 : ind_desc.
  Local Notation D := (ind_name d0).
  Hypothesis Hn : sig_ind sg D = None.
  Hypothesis Hfree : desc_free d0 = true.
  Variable sg1 : signature.
  Hypothesis E1 : sig_entries sg1 = EInd d0 :: sig_entries sg.

  Lemma hsig : signature_typed SP sg.
  Proof. exact (inv_typed _ Hinv). Qed.

  Lemma hdist : ctors_distinct sg.
  Proof. exact (checked_distinct (inv_checked Hinv)). Qed.

  Lemma fam_none : forall g, of_family D g = true -> sig_type sg g = None.
  Proof.
    pose proof (checked_generated (inv_checked Hinv)) as Hgen.
    intros [D' | D' c | D' s | f] H; cbn [of_family] in H; try discriminate H;
      apply String.eqb_eq in H; subst D'; cbn [sig_type].
    - rewrite Hn. reflexivity.
    - rewrite Hn. reflexivity.
    - destruct (sig_elim sg D s) as [[A act]|] eqn:E; [ | reflexivity].
      destruct (Hgen D s A act E) as (d & Hd & _). rewrite Hn in Hd. discriminate Hd.
  Qed.

  Lemma elim_not_D : forall D' s A, sig_elim sg D' s = Some A -> D' <> D.
  Proof.
    intros D' s [A act] H E. subst D'. pose proof (fam_none (Elim D s) ltac:(cbn; apply String.eqb_refl)) as H0.
    cbn [sig_type] in H0. rewrite H in H0. discriminate H0.
  Qed.

  Lemma typed_free : forall G t A, has_type SP sg G t A -> allnodes (notD D) (notDk D) t = true.
  Proof.
    apply (typed_an SP sg).
    - intros g H. apply fam_none. unfold notD in H. destruct (of_family D g); [reflexivity | discriminate H].
    - intros D' H. unfold notDk in H. destruct (String.eqb D' D) eqn:E; [ | discriminate H].
      apply String.eqb_eq in E. subst. exact Hn.
  Qed.

  Lemma types_free : forall g A, sig_type sg g = Some A -> allnodes (notD D) (notDk D) A = true.
  Proof. intros g A H. destruct (inv_types Hinv g A H) as [s Hs]. exact (typed_free _ _ _ Hs). Qed.

  Lemma bodies_free : forall g b, sig_delta sg g = Some b -> allnodes (notD D) (notDk D) b = true.
  Proof.
    intros [D' | D' c | D' s | f] b H; cbn [sig_delta] in H; try discriminate H.
    destruct (sig_def sg f) as [[A b0]|] eqn:E; [ | discriminate H]. cbn [option_map snd] in H. injection H as <-.
    apply (typed_free []) with (A := A). apply (inv_bodies Hinv (Def f)); cbn [sig_type sig_delta]; rewrite E; reflexivity.
  Qed.

  Lemma descs_free : forall D' d', sig_ind sg D' = Some d' ->
    Forall (fun T => allnodes (notD D) (notDk D) T = true) (ind_indices d') /\
    (forall c, In c (ind_ctors d') ->
       Forall (fun T => allnodes (notD D) (notDk D) T = true)
         (field_types (ind_name d') (length (ind_params d')) 0 (ctor_fields c)) /\
       Forall (fun T => allnodes (notD D) (notDk D) T = true) (ctor_indices c)).
  Proof.
    intros D' d' Hd. split.
    - pose proof (types_free _ _ (sig_type_ind _ _ _ Hd)) as H. unfold ind_type in H.
      rewrite an_pis, forallb_app in H. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H].
      rewrite Forall_forall. rewrite forallb_forall in H. exact H.
    - intros c Hc. destruct (find_ctor_nodup _ _ (hdist _ _ Hd) Hc) as [i Hi].
      assert (Ht : sig_type sg (Ctor D' (ctor_name c)) = Some (ctor_type d' c)) by (cbn [sig_type]; rewrite Hd, Hi; reflexivity).
      pose proof (types_free _ _ Ht) as H. unfold ctor_type in H. cbv zeta in H.
      rewrite an_pis, forallb_app, an_apps, forallb_app in H.
      apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [_ H1]. apply andb_prop in H2 as [_ H2].
      apply andb_prop in H2 as [_ H2].
      rewrite !Forall_forall. rewrite !forallb_forall in *. split; [exact H1 | exact H2].
  Qed.

  Lemma free_fixed : forall r t pk, (forall g, notD D g = true -> r g = g) -> allnodes (notD D) pk t = true ->
    fixed r t.
  Proof. intros r t pk Hr H. exact (cren_fixed_an r _ _ t Hr H). Qed.

  Lemma free_cases : forall t, allnodes (notD D) (notDk D) t = true -> cases_in (notDk D) t = true.
  Proof. intros t H. exact (an_weaken _ _ _ _ _ (fun _ _ => eq_refl) (fun _ x => x) H). Qed.

  Lemma free_all : forall t, cases_in (fun _ => true) t = true.
  Proof. intros t. apply an_true. Qed.

  (** ** The lookups of [sg1] *)

  Lemma ind1 : forall D', D' <> D -> sig_ind sg1 D' = sig_ind sg D'.
  Proof.
    intros D' H. rewrite (add_ind_ind _ _ _ E1). destruct (String.eqb D D') eqn:E; [ | reflexivity].
    apply String.eqb_eq in E. symmetry in E. contradiction.
  Qed.

  Lemma ind1_D : sig_ind sg1 D = Some d0.
  Proof. rewrite (add_ind_ind _ _ _ E1), String.eqb_refl. reflexivity. Qed.

  Lemma type1 : forall g, notD D g = true -> sig_type sg1 g = sig_type sg g.
  Proof.
    intros [D' | D' c | D' s | f] H; unfold notD in H; cbn [of_family sig_type] in *.
    - rewrite ind1; [reflexivity | ]. intros E. subst. rewrite String.eqb_refl in H. discriminate H.
    - rewrite ind1; [reflexivity | ]. intros E. subst. rewrite String.eqb_refl in H. discriminate H.
    - rewrite (add_ind_elim _ _ _ E1). reflexivity.
    - rewrite (add_ind_def _ _ _ E1). reflexivity.
  Qed.

  Lemma delta1 : forall g, sig_delta sg1 g = sig_delta sg g.
  Proof. intros [D' | D' c | D' s | f]; cbn [sig_delta]; try reflexivity. rewrite (add_ind_def _ _ _ E1). reflexivity. Qed.

  Lemma elim1 : forall D' s, sig_elim sg1 D' s = sig_elim sg D' s.
  Proof. intros D' s. exact (add_ind_elim _ _ _ E1 D' s). Qed.

  (** The checks of [sg1] on terms free of D are checks of [sg]. *)
  Lemma closure_free : forall D' s A d', sig_elim sg1 D' s = Some (A, true) -> sig_ind sg1 D' = Some d' ->
    notD D (Elim D' s) = true /\
    (forall c, In c (ind_ctors d') -> forall Bs vs, In (FRec Bs vs) (ctor_fields c) ->
       forallb (allnodes (notD D) (notDk D)) vs = true).
  Proof.
    intros D' s A d' He Hd. rewrite elim1 in He. pose proof (elim_not_D _ _ _ He) as HD.
    rewrite (ind1 _ HD) in Hd. split.
    - unfold notD. cbn [of_family]. destruct (String.eqb D' D) eqn:E; [apply String.eqb_eq in E; contradiction | reflexivity].
    - intros c Hc Bs vs Hin. destruct (descs_free _ _ Hd) as [_ Hcs]. destruct (Hcs c Hc) as [HF _].
      exact (fields_vs _ _ _ _ _ _ _ _ HF Hin).
  Qed.

  Lemma sg1_closed : an_closed (notD D) (notDk D) sg1.
  Proof. split; [intros g b H; rewrite delta1 in H; exact (bodies_free _ _ H) | exact closure_free]. Qed.

  Lemma ind_type_free : allnodes (notD D) (notDk D) (ind_type d0) = true.
  Proof.
    unfold desc_free in Hfree. cbv zeta in Hfree. apply andb_prop in Hfree as [H _].
    unfold ind_type. rewrite an_pis. rewrite andb_true_r. rewrite forallb_forall in *.
    intros x Hx. apply free_an. exact (H x Hx).
  Qed.

  Theorem ind_type_typed_sg : forall Sp s0, checking_spec Sp -> is_type_of Sp sg1 [] (ind_type d0) s0 ->
    has_type SP sg [] (ind_type d0) (Srt s0).
  Proof.
    intros Sp s0 HSp (T & HT & Hr).
    assert (HR : cren_ok (fun g => g) sg1 sg (notDk D)).
    { split; [reflexivity | | | ].
      - intros g b H. rewrite delta1 in H. rewrite cren_id. split; [exact H | exact (free_cases _ (bodies_free _ _ H))].
      - intros D' s A d' He Hd. destruct (closure_free _ _ _ _ He Hd) as [_ Hvs].
        rewrite elim1 in He. pose proof (elim_not_D _ _ _ He) as HD. rewrite (ind1 _ HD) in Hd.
        split; [reflexivity | split; [exact He | split; [exact Hd | ]]].
        intros c Hc Bs vs Hin. pose proof (Hvs c Hc Bs vs Hin) as H. rewrite Forall_forall. rewrite forallb_forall in H.
        intros v Hv. split; [apply cren_id | exact (free_cases _ (H v Hv))].
      - intros D' d' H Hk. rewrite (ind1 _ (notD_true _ _ Hk)) in H. exact H. }
    assert (Hpcf : forall D', notD D (Ind D') = true -> (fun g => g) (Ind D') = Ind D' /\
              (forall d', sig_ind sg1 D' = Some d' -> sig_ind sg D' = Some d')).
    { intros D' H. split; [reflexivity | ]. intros d' Hd. rewrite ind1 in Hd; [exact Hd | ].
      intros E. subst. unfold notD in H. cbn in H. rewrite String.eqb_refl in H. discriminate H. }
    assert (Htype_f : forall g A, sig_type sg1 g = Some A -> notD D g = true ->
              sig_type sg ((fun g => g) g) = Some (cren (fun g => g) A) /\ cases_in (notDk D) A = true).
    { intros g A H Hg. rewrite type1 in H by exact Hg. rewrite cren_id. split; [exact H | exact (free_cases _ (types_free _ _ H))]. }
    assert (Hdesc_f : forall D' d', sig_ind sg1 D' = Some d' -> notDk D D' = true ->
              desc_fixed (fun g => g) d' /\ desc_cases (notDk D) d').
    { intros D' d' H Hk. rewrite (ind1 _ (notD_true _ _ Hk)) in H.
      destruct (descs_free _ _ H) as [HI HC].
      split; [split; [reflexivity | split] | split].
      - rewrite Forall_forall. intros x _. apply cren_id.
      - intros c Hc. split; rewrite Forall_forall; intros x _; apply cren_id.
      - rewrite Forall_forall in HI |- *. intros x Hx. exact (free_cases _ (HI x Hx)).
      - intros c Hc. destruct (HC c Hc) as [HF HU]. rewrite Forall_forall in HF, HU. rewrite !Forall_forall.
        split; intros x Hx; [exact (free_cases _ (HF x Hx)) | exact (free_cases _ (HU x Hx))]. }
    destruct (proj1 (synth_cren Sp (fun g => g) sg1 sg (notDk D) (notD D) (notD D) (notDk D)
                       HR sg1_closed Hpcf Htype_f Hdesc_f)
                    [] _ _ HT ind_type_free (fixok_of_an _ _ _ ind_type_free) eq_refl) as [HT' HcT].
    rewrite !cren_id in HT'. cbn [map] in HT'.
    pose proof (red_cren _ _ _ _ HR _ _ Hr HcT) as Hr'. rewrite !cren_id in Hr'.
    exact (is_type_typed sg hsig hdist Sp HSp [] _ s0 (BW_Nil _ _) (ex_intro _ T (conj HT' Hr'))).
  Qed.

  (** ** The signature with the inactive instance *)

  Variable s0 : sort.
  Hypothesis Hind : has_type SP sg [] (ind_type d0) (Srt s0).
  Variable sgn : signature.
  Hypothesis En : sig_entries sgn = EElim D Prp (ind_type d0) false :: sig_entries sg.

  Lemma elimn_none : sig_elim sg D Prp = None.
  Proof. destruct (sig_elim sg D Prp) as [A|] eqn:E; [exfalso; exact (elim_not_D _ _ _ E eq_refl) | reflexivity]. Qed.

  Lemma le_n : sig_le sg sgn.
  Proof. exact (sig_le_elim _ _ _ _ _ _ elimn_none En). Qed.

  Lemma indn : forall D', sig_ind sgn D' = sig_ind sg D'.
  Proof. intros D'. exact (add_elim_ind _ _ _ _ _ _ En D'). Qed.

  Lemma deltan : forall g, sig_delta sgn g = sig_delta sg g.
  Proof. intros [D' | D' c | D' s | f]; cbn [sig_delta]; try reflexivity. rewrite (add_elim_def _ _ _ _ _ _ En). reflexivity. Qed.

  Lemma elimn : forall D' s, D' <> D -> sig_elim sgn D' s = sig_elim sg D' s.
  Proof.
    intros D' s H. rewrite (add_elim_elim _ _ _ _ _ _ En). destruct (String.eqb D D') eqn:E; [ | reflexivity].
    apply String.eqb_eq in E. symmetry in E. contradiction.
  Qed.

  Lemma elimn_active : forall D' s A, sig_elim sgn D' s = Some (A, true) -> sig_elim sg D' s = Some (A, true).
  Proof.
    intros D' s A H. rewrite (add_elim_elim _ _ _ _ _ _ En) in H.
    destruct (String.eqb D D' && sort_eqb Prp s); [discriminate H | exact H].
  Qed.

  Lemma typen : forall g, notD D g = true -> sig_type sgn g = sig_type sg g.
  Proof.
    intros [D' | D' c | D' s | f] H; cbn [sig_type].
    - rewrite indn. reflexivity.
    - rewrite indn. reflexivity.
    - rewrite elimn; [reflexivity | ]. intros E. subst. unfold notD in H. cbn in H. rewrite String.eqb_refl in H.
      discriminate H.
    - rewrite (add_elim_def _ _ _ _ _ _ En). reflexivity.
  Qed.

  Lemma typen_c : sig_type sgn (Elim D Prp) = Some (ind_type d0).
  Proof. cbn [sig_type]. rewrite (add_elim_elim _ _ _ _ _ _ En), String.eqb_refl. reflexivity. Qed.

  Lemma sgn_typed : signature_typed SP sgn /\ ctors_distinct sgn.
  Proof.
    pose proof (checked_distinct (inv_checked Hinv)) as Hdist.
    destruct Hinv as [Hty Hbd Hins _].
    assert (Hty' : sig_types_typed SP sgn).
    { intros g A H. destruct (of_family D g) eqn:Ef.
      - destruct g as [D' | D' c | D' s | f]; cbn [of_family] in Ef; try discriminate Ef;
          apply String.eqb_eq in Ef; subst D'.
        + cbn [sig_type] in H. rewrite indn, Hn in H. discriminate H.
        + cbn [sig_type] in H. rewrite indn, Hn in H. discriminate H.
        + cbn [sig_type] in H. rewrite (add_elim_elim _ _ _ _ _ _ En), String.eqb_refl in H.
          destruct (sort_eqb Prp s) eqn:Es.
          * apply sort_eqb_eq in Es. subst s. cbn in H. injection H as <-. exists s0.
            exact (typed_sig_mono _ _ _ le_n _ _ _ Hind).
          * cbn in H. destruct (sig_elim sg D s) as [x|] eqn:E; [exfalso; exact (elim_not_D _ _ _ E eq_refl) | ].
            discriminate H.
      - assert (Hg : notD D g = true) by (unfold notD; rewrite Ef; reflexivity).
        rewrite typen in H by exact Hg. destruct (Hty g A H) as [s1 Hs1]. exists s1.
        exact (typed_sig_mono _ _ _ le_n _ _ _ Hs1). }
    split; [split; [exact Hty' | split] | ].
    - intros [D' | D' c | D' s | f] A b HA Hb; rewrite deltan in Hb; cbn [sig_delta] in Hb; try discriminate Hb.
      cbn [sig_type] in HA. rewrite (add_elim_def _ _ _ _ _ _ En) in HA.
      apply (typed_sig_mono _ _ _ le_n). exact (Hbd (Def f) A b HA Hb).
    - intros G t u T Hu Ht. refine (iota_typed SP sgn Hty' predicative_prop_full _ G t u T Hu Ht).
      intros D' s A He. apply elimn_active in He. destruct (Hins D' s A He) as (d' & Hd & -> & Hr).
      exists d'. split; [rewrite indn; exact Hd | split; [reflexivity | exact (rules_typed_mono _ _ _ _ le_n Hr)]].
    - intros D' d' H. rewrite indn in H. exact (Hdist _ _ H).
  Qed.

  (** The type of a constructor, renamed, in [sgn]. *)
  Theorem ctor_type_typed_sgn : forall Sp c sc, checking_spec Sp -> In c (ind_ctors d0) ->
    is_type_of Sp sg1 [] (ctor_type d0 c) sc ->
    has_type SP sgn [] (cren (fwd D) (ctor_type d0 c)) (Srt sc).
  Proof.
    intros Sp c sc HSp Hc (T & HT & Hr).
    assert (HR : cren_ok (fwd D) sg1 sgn (notDk D)).
    { split; [reflexivity | | | ].
      - intros g b H. rewrite delta1 in H. pose proof (bodies_free _ _ H) as Hb.
        destruct g as [D' | D' c' | D' s | f]; cbn [sig_delta] in H; try discriminate H.
        cbn [fwd]. rewrite deltan. cbn [sig_delta]. rewrite (cren_fixed_an _ _ _ _ (notD_fwd D) Hb).
        split; [exact H | exact (free_cases _ Hb)].
      - intros D' s A d' He Hd. destruct (closure_free _ _ _ _ He Hd) as [_ Hvs].
        rewrite elim1 in He. pose proof (elim_not_D _ _ _ He) as HD. rewrite (ind1 _ HD) in Hd.
        split; [reflexivity | split; [rewrite elimn by exact HD; exact He | split; [rewrite indn; exact Hd | ]]].
        intros c' Hc' Bs vs Hin. pose proof (Hvs c' Hc' Bs vs Hin) as H. rewrite Forall_forall. rewrite forallb_forall in H.
        intros v Hv. split; [exact (cren_fixed_an _ _ _ _ (notD_fwd D) (H v Hv)) | exact (free_cases _ (H v Hv))].
      - intros D' d' H Hk. rewrite (ind1 _ (notD_true _ _ Hk)) in H. rewrite indn. exact H. }
    assert (Hpcf : forall D', notD D (Ind D') = true -> fwd D (Ind D') = Ind D' /\
              (forall d', sig_ind sg1 D' = Some d' -> sig_ind sgn D' = Some d')).
    { intros D' H. split; [exact (notD_fwd D _ H) | ]. intros d' Hd. rewrite indn. rewrite ind1 in Hd; [exact Hd | ].
      intros E. subst. unfold notD in H. cbn in H. rewrite String.eqb_refl in H. discriminate H. }
    assert (Htype_f : forall g A, sig_type sg1 g = Some A -> onlyInd D g = true ->
              sig_type sgn (fwd D g) = Some (cren (fwd D) A) /\ cases_in (notDk D) A = true).
    { intros g A H Hg. destruct (notD D g) eqn:Eg.
      - rewrite type1 in H by exact Eg. pose proof (types_free _ _ H) as HA.
        rewrite (notD_fwd D _ Eg), typen by exact Eg. rewrite (cren_fixed_an _ _ _ _ (notD_fwd D) HA).
        split; [exact H | exact (free_cases _ HA)].
      - destruct g as [D' | D' c' | D' s | f]; unfold notD in Eg; cbn [of_family onlyInd] in Eg, Hg.
        + apply negb_false_iff in Eg. apply String.eqb_eq in Eg. subst D'.
          cbn [sig_type] in H. rewrite ind1_D in H. cbn [option_map] in H. injection H as <-.
          cbn [fwd]. rewrite String.eqb_refl, typen_c, (cren_fixed_an _ _ _ _ (notD_fwd D) ind_type_free).
          split; [reflexivity | exact (free_cases _ ind_type_free)].
        + rewrite Eg in Hg. discriminate Hg.
        + rewrite Eg in Hg. discriminate Hg.
        + discriminate Eg. }
    assert (Hdesc_f : forall D' d', sig_ind sg1 D' = Some d' -> notDk D D' = true ->
              desc_fixed (fwd D) d' /\ desc_cases (notDk D) d').
    { intros D' d' H Hk. pose proof (notD_true _ _ Hk) as HD. rewrite (ind1 _ HD) in H.
      destruct (descs_free _ _ H) as [HI HC].
      split; [split; [ | split] | split].
      - rewrite (sig_ind_name _ _ _ H). cbn [fwd]. destruct (String.eqb D' D) eqn:E; [apply String.eqb_eq in E; contradiction | reflexivity].
      - rewrite Forall_forall in HI |- *. intros x Hx. exact (cren_fixed_an _ _ _ _ (notD_fwd D) (HI x Hx)).
      - intros c' Hc'. destruct (HC c' Hc') as [HF HU]. rewrite Forall_forall in HF, HU. rewrite !Forall_forall.
        split; intros x Hx; [exact (cren_fixed_an _ _ _ _ (notD_fwd D) (HF x Hx))
                            | exact (cren_fixed_an _ _ _ _ (notD_fwd D) (HU x Hx))].
      - rewrite Forall_forall in HI |- *. intros x Hx. exact (free_cases _ (HI x Hx)).
      - intros c' Hc'. destruct (HC c' Hc') as [HF HU]. rewrite Forall_forall in HF, HU. rewrite !Forall_forall.
        split; intros x Hx; [exact (free_cases _ (HF x Hx)) | exact (free_cases _ (HU x Hx))]. }
    destruct (ctor_type_good d0 c Hfree Hc) as [Hg1 Hg2].
    destruct (proj1 (synth_cren Sp (fwd D) sg1 sgn (notDk D) (onlyInd D) (notD D) (notDk D)
                       HR sg1_closed Hpcf Htype_f Hdesc_f)
                    [] _ _ HT Hg1 Hg2 eq_refl) as [HT' HcT].
    cbn [map] in HT'.
    pose proof (red_cren _ _ _ _ HR _ _ Hr HcT) as Hr'. cbn [cren] in Hr'.
    destruct sgn_typed as [Hsign Hdistn].
    exact (is_type_typed sgn Hsign Hdistn Sp HSp [] _ sc (BW_Nil _ _) (ex_intro _ (cren (fwd D) T) (conj HT' Hr'))).
  Qed.

  (** ** Renamed back, in the signature with the declaration *)

  Variable d : ind_desc.
  Hypothesis Hdname : ind_name d = D.
  Hypothesis Hdtype : ind_type d = ind_type d0.
  Variable sg' : signature.
  Hypothesis E : sig_entries sg' = EInd d :: sig_entries sg.

  Lemma le' : sig_le sg sg'.
  Proof. apply (sig_le_ind _ _ d); [rewrite Hdname; exact Hn | exact E]. Qed.

  Theorem ctor_type_typed_sg' : forall c sc, In c (ind_ctors d0) ->
    has_type SP sgn [] (cren (fwd D) (ctor_type d0 c)) (Srt sc) -> has_type SP sg' [] (ctor_type d0 c) (Srt sc).
  Proof.
    intros c sc Hc H.
    assert (HR : cren_ok (bwd D) sgn sg' (fun _ => true)).
    { split; [reflexivity | | | ].
      - intros g b Hb. rewrite deltan in Hb. pose proof (bodies_free _ _ Hb) as Hf.
        destruct g as [D' | D' c' | D' s | f]; cbn [sig_delta] in Hb; try discriminate Hb.
        cbn [bwd sig_delta]. rewrite (add_ind_def _ _ _ E), (cren_fixed_an _ _ _ _ (notD_bwd D) Hf).
        split; [exact Hb | apply an_true].
      - intros D' s A d' He Hd. apply elimn_active in He. pose proof (elim_not_D _ _ _ He) as HD.
        rewrite indn in Hd.
        split; [cbn [bwd]; destruct (String.eqb D' D) eqn:Ee; [apply String.eqb_eq in Ee; contradiction | reflexivity] | ].
        split; [rewrite (add_ind_elim _ _ _ E); exact He | split; [exact (le_ind _ _ le' _ _ Hd) | ]].
        intros c' Hc' Bs vs Hin. destruct (descs_free _ _ Hd) as [_ HC]. destruct (HC c' Hc') as [HF _].
        pose proof (fields_vs _ _ _ _ _ _ _ _ HF Hin) as Hvs. rewrite forallb_forall in Hvs. rewrite Forall_forall.
        intros v Hv. split; [exact (cren_fixed_an _ _ _ _ (notD_bwd D) (Hvs v Hv)) | apply an_true].
      - intros D' d' Hd _. rewrite indn in Hd. exact (le_ind _ _ le' _ _ Hd). }
    assert (Hfixed : forall D' d', sig_ind sgn D' = Some d' -> desc_fixed (bwd D) d').
    { intros D' d' Hd. rewrite indn in Hd.
      destruct (descs_free _ _ Hd) as [HI HC]. split; [reflexivity | split].
      - rewrite Forall_forall in HI |- *. intros x Hx. exact (cren_fixed_an _ _ _ _ (notD_bwd D) (HI x Hx)).
      - intros c' Hc'. destruct (HC c' Hc') as [HF HU]. rewrite Forall_forall in HF, HU. rewrite !Forall_forall.
        split; intros x Hx; [exact (cren_fixed_an _ _ _ _ (notD_bwd D) (HF x Hx))
                            | exact (cren_fixed_an _ _ _ _ (notD_bwd D) (HU x Hx))]. }
    assert (Htype : forall g A, sig_type sgn g = Some A -> sig_type sg' (bwd D g) = Some (cren (bwd D) A)).
    { intros g A HA. destruct (notD D g) eqn:Eg.
      - rewrite typen in HA by exact Eg. rewrite (notD_bwd D _ Eg), (le_type _ _ le' _ _ HA).
        rewrite (cren_fixed_an _ _ _ _ (notD_bwd D) (types_free _ _ HA)). reflexivity.
      - destruct g as [D' | D' c' | D' s | f]; unfold notD in Eg; cbn [of_family] in Eg; try discriminate Eg;
          apply negb_false_iff, String.eqb_eq in Eg; subst D'.
        + cbn [sig_type] in HA. rewrite indn, Hn in HA. discriminate HA.
        + cbn [sig_type] in HA. rewrite indn, Hn in HA. discriminate HA.
        + cbn [sig_type] in HA. rewrite (add_elim_elim _ _ _ _ _ _ En), String.eqb_refl in HA.
          destruct (sort_eqb Prp s) eqn:Es.
          * apply sort_eqb_eq in Es. subst s. cbn in HA. injection HA as <-.
            cbn [bwd]. rewrite String.eqb_refl.
            replace (sort_eqb Prp Prp) with true by (symmetry; apply sort_eqb_eq; reflexivity). cbn [andb].
            cbn [sig_type]. rewrite (add_ind_ind _ _ _ E), Hdname, String.eqb_refl. cbn [option_map].
            rewrite Hdtype, (cren_fixed_an _ _ _ _ (notD_bwd D) ind_type_free). reflexivity.
          * cbn in HA. destruct (sig_elim sg D s) as [x|] eqn:Ex; [exfalso; exact (elim_not_D _ _ _ Ex eq_refl) | ].
            discriminate HA. }
    pose proof (proj1 (proj2 (typing_cren SP (bwd D) sgn sg' HR Hfixed Htype)) [] _ _ H) as H'.
    cbn [map cren] in H'. rewrite cren_compose in H'.
    rewrite (cren_fixed_an _ (onlyInd D) (notDk D) _ (onlyInd_back D) (proj1 (ctor_type_good d0 c Hfree Hc))) in H'.
    exact H'.
  Qed.

  (** ** A judgment of [sg1] in the signature with the declaration

      [sg1] and [sg'] differ in the category of D alone, which a term
      mentioning of D only its family never reads: a type checked in
      [sg1] at a sort, a field of a constructor say, is one in [sg'] at
      that sort, by the identity renaming. *)
  Theorem is_type_sg' : forall Sp G t s, is_type_of Sp sg1 G t s ->
    allnodes (onlyInd D) (notDk D) t = true -> fixok (notD D) (notDk D) t = true ->
    forallb (cases_in (notDk D)) G = true -> is_type_of Sp sg' G t s.
  Proof.
    intros Sp G t s (T & HT & Hr) Hg1 Hg2 HG.
    set (r := fun g : gref => g).
    assert (HR : cren_ok r sg1 sg' (notDk D)).
    { split; [reflexivity | | | ].
      - intros g b H. rewrite delta1 in H. pose proof (bodies_free _ _ H) as Hb.
        unfold r. rewrite cren_id. split; [ | exact (free_cases _ Hb)].
        destruct g as [D' | D' c' | D' s' | f]; cbn [sig_delta] in H |- *; try discriminate H.
        rewrite (add_ind_def _ _ _ E). exact H.
      - intros D' s' A d' He Hd. destruct (closure_free _ _ _ _ He Hd) as [_ Hvs].
        rewrite elim1 in He. pose proof (elim_not_D _ _ _ He) as HD. rewrite (ind1 _ HD) in Hd.
        split; [reflexivity | split; [rewrite (add_ind_elim _ _ _ E); exact He | split; [exact (le_ind _ _ le' _ _ Hd) | ]]].
        intros c' Hc' Bs vs Hin. pose proof (Hvs c' Hc' Bs vs Hin) as H. rewrite Forall_forall. rewrite forallb_forall in H.
        intros v Hv. split; [unfold fixed, r; exact (cren_id v) | exact (free_cases _ (H v Hv))].
      - intros D' d' H Hk. rewrite (ind1 _ (notD_true _ _ Hk)) in H. exact (le_ind _ _ le' _ _ H). }
    assert (Hpcf : forall D', notD D (Ind D') = true -> r (Ind D') = Ind D' /\
              (forall d', sig_ind sg1 D' = Some d' -> sig_ind sg' D' = Some d')).
    { intros D' H. split; [reflexivity | ]. intros d' Hd. rewrite ind1 in Hd; [exact (le_ind _ _ le' _ _ Hd) | ].
      intros Eq. subst. unfold notD in H. cbn in H. rewrite String.eqb_refl in H. discriminate H. }
    assert (Htype_f : forall g A, sig_type sg1 g = Some A -> onlyInd D g = true ->
              sig_type sg' (r g) = Some (cren r A) /\ cases_in (notDk D) A = true).
    { intros g A H Hg. unfold r. rewrite cren_id. destruct (notD D g) eqn:Eg.
      - rewrite type1 in H by exact Eg. split; [exact (le_type _ _ le' _ _ H) | exact (free_cases _ (types_free _ _ H))].
      - destruct g as [D' | D' c' | D' s' | f]; unfold notD in Eg; cbn [of_family onlyInd] in Eg, Hg.
        + apply negb_false_iff in Eg. apply String.eqb_eq in Eg. subst D'.
          cbn [sig_type] in H |- *. rewrite ind1_D in H. cbn [option_map] in H. injection H as <-.
          rewrite (add_ind_ind _ _ _ E), Hdname, String.eqb_refl. cbn [option_map]. rewrite Hdtype.
          split; [reflexivity | exact (free_cases _ ind_type_free)].
        + rewrite Eg in Hg. discriminate Hg.
        + rewrite Eg in Hg. discriminate Hg.
        + discriminate Eg. }
    assert (Hdesc_f : forall D' d', sig_ind sg1 D' = Some d' -> notDk D D' = true ->
              desc_fixed r d' /\ desc_cases (notDk D) d').
    { intros D' d' H Hk. pose proof (notD_true _ _ Hk) as HD. rewrite (ind1 _ HD) in H.
      destruct (descs_free _ _ H) as [HI HC].
      split; [split; [ | split] | split].
      - reflexivity.
      - rewrite Forall_forall. intros x _. unfold fixed, r. apply cren_id.
      - intros c' _. split; rewrite Forall_forall; intros x _; unfold fixed, r; apply cren_id.
      - rewrite Forall_forall in HI |- *. intros x Hx. exact (free_cases _ (HI x Hx)).
      - intros c' Hc'. destruct (HC c' Hc') as [HF HU]. rewrite Forall_forall in HF, HU. rewrite !Forall_forall.
        split; intros x Hx; [exact (free_cases _ (HF x Hx)) | exact (free_cases _ (HU x Hx))]. }
    destruct (proj1 (synth_cren Sp r sg1 sg' (notDk D) (onlyInd D) (notD D) (notDk D)
                       HR sg1_closed Hpcf Htype_f Hdesc_f) G t T HT Hg1 Hg2 HG)
      as [HT' HcT].
    pose proof (red_cren _ _ _ _ HR _ _ Hr HcT) as Hr'.
    unfold r in HT', Hr'. cbn [cren] in Hr'. rewrite cren_id in HT', Hr'. rewrite cren_id in HT'.
    rewrite (map_ext (cren (fun g => g)) (fun x => x) cren_id G), map_id in HT'.
    exists T. split; [exact HT' | exact Hr'].
  Qed.
End Declaration.

(** The types of a declaration and of its constructors are types in the
    signature it is registered into, when that signature is
    type-correct. *)
Definition declaration_typed : Prop :=
  forall Sp fuel sg raw log log' sg' d, checking_spec Sp -> sig_inv sg ->
    declare_ind_with Sp fuel Checked sg raw log = (log', Ok (sg', d)) ->
    (exists s, has_type SP sg' [] (ind_type d) (Srt s)) /\
    (forall c, In c (ind_ctors d) -> exists s, has_type SP sg' [] (ctor_type d c) (Srt s)).

Theorem declaration_typed_holds : declaration_typed.
Proof.
  intros Sp fuel sg raw log log' sg' d HSp Hinv H.
  destruct (declare_ind_sound Sp fuel _ _ _ _ _ _ _ H) as (d0 & sg1 & fss & Hcl & Hn & E1 & [s0 HI] & Hcs & Ed & E).
  pose proof (classify_name _ _ _ Hcl) as Hname. rewrite <- Hname in Hn.
  pose proof (classify_decl_strictly_positive raw d0 Hcl) as Hfree.
  pose proof (ind_type_typed_sg sg Hinv d0 Hn Hfree sg1 E1 Sp s0 HSp HI) as Hind.
  assert (Hcl0 : closed (ind_type d0) = true).
  { apply (sig_type_closed sg1 (Ind (ind_name d0))). cbn [sig_type]. rewrite (ind1_D sg d0 sg1 E1). reflexivity. }
  set (e := EElim (ind_name d0) Prp (ind_type d0) false).
  set (sgn := {| sig_entries := e :: sig_entries sg; sig_wf := entries_closed_cons sg e Hcl0 |}).
  assert (En : sig_entries sgn = e :: sig_entries sg) by reflexivity.
  subst d.
  assert (Hdname : ind_name (with_elim d0 (elim_class_of (ind_sort d0) fss)) = ind_name d0) by reflexivity.
  assert (Hdtype : ind_type (with_elim d0 (elim_class_of (ind_sort d0) fss)) = ind_type d0) by reflexivity.
  assert (Hle : sig_le sg sg') by (apply (sig_le_ind _ _ _ ltac:(rewrite Hdname; exact Hn) E)).
  split.
  - exists s0. rewrite Hdtype. exact (typed_sig_mono _ _ _ Hle _ _ _ Hind).
  - intros c Hc. cbn [with_elim ind_ctors] in Hc.
    destruct (forall2_in_l _ _ _ _ Hcs Hc) as (ss & [sc Hsc] & _).
    pose proof (ctor_type_typed_sgn sg Hinv d0 Hn Hfree sg1 E1 s0 Hind sgn En Sp c sc HSp Hc Hsc) as Hn'.
    exists sc. change (ctor_type (with_elim d0 (elim_class_of (ind_sort d0) fss)) c) with (ctor_type d0 c).
    exact (ctor_type_typed_sg' sg Hinv d0 Hn Hfree sgn En _ Hdname Hdtype sg' E c sc Hc Hn').
Qed.

Lemma declare_ind_inv : declaration_typed -> forall Sp fuel sg raw log log' sg' d, checking_spec Sp ->
  declare_ind_with Sp fuel Checked sg raw log = (log', Ok (sg', d)) -> sig_inv sg -> sig_inv sg'.
Proof.
  intros Hdecl Sp fuel sg raw log log' sg' d HSp H Hinv.
  pose proof (declare_ind_generated _ _ _ _ _ _ _ _ _ H (inv_checked Hinv)) as Hc'.
  pose proof (inv_typed _ Hinv) as Hsig.
  destruct (Hdecl Sp fuel sg raw log log' sg' d HSp Hinv H) as [[si Hi] Hcs].
  destruct (declare_ind_sound Sp fuel _ _ _ _ _ _ _ H) as (d0 & sg1 & fss & Hcl & Hn & _ & _ & _ & Ed & E).
  assert (Hname : ind_name d = rd_name raw) by (rewrite Ed; exact (classify_name _ _ _ Hcl)).
  rewrite <- Hname in Hn.
  pose proof (sig_le_ind _ _ _ Hn E) as Hle.
  destruct Hinv as [Hty Hbd Hins Hc].
  split; [ | | | exact Hc'].
  - intros [D | D c | D s0 | f] T HT; cbn [sig_type] in HT.
    + rewrite (add_ind_ind _ _ _ E) in HT. destruct (String.eqb (ind_name d) D) eqn:ED.
      * injection HT as <-. exists si. exact Hi.
      * destruct (Hty (Ind D) T HT) as [s1 Hs1]. exists s1. exact (typed_sig_mono _ _ _ Hle _ _ _ Hs1).
    + rewrite (add_ind_ind _ _ _ E) in HT. destruct (String.eqb (ind_name d) D) eqn:ED.
      * destruct (find_ctor (ind_ctors d) c) as [[i cd]|] eqn:Ec; [ | discriminate HT].
        injection HT as <-. exact (Hcs cd (nth_error_In _ _ (find_ctor_nth_error _ _ _ _ Ec))).
      * destruct (Hty (Ctor D c) T HT) as [s1 Hs1]. exists s1. exact (typed_sig_mono _ _ _ Hle _ _ _ Hs1).
    + rewrite (add_ind_elim _ _ _ E) in HT.
      destruct (Hty (Elim D s0) T HT) as [s1 Hs1]. exists s1. exact (typed_sig_mono _ _ _ Hle _ _ _ Hs1).
    + rewrite (add_ind_def _ _ _ E) in HT.
      destruct (Hty (Def f) T HT) as [s1 Hs1]. exists s1. exact (typed_sig_mono _ _ _ Hle _ _ _ Hs1).
  - intros [D | D c | D s0 | f] T b0 HT0 Hb0; cbn [sig_delta] in Hb0; try discriminate Hb0.
    cbn [sig_type] in HT0. rewrite (add_ind_def _ _ _ E) in HT0, Hb0.
    apply (typed_sig_mono _ _ _ Hle). apply (Hbd (Def f) T b0); cbn [sig_type sig_delta]; assumption.
  - intros D s0 T He. rewrite (add_ind_elim _ _ _ E) in He.
    destruct (Hins D s0 T He) as (d' & Hd' & -> & Hr'). exists d'. split; [exact (le_ind _ _ Hle _ _ Hd') | ].
    split; [reflexivity | exact (rules_typed_mono _ _ _ _ Hle Hr')].
Qed.

(** ** Checked signatures *)

Lemma inv_empty : forall sg, sig_entries sg = [] -> sig_inv sg.
Proof.
  intros sg E.
  assert (Hi : forall D, sig_ind sg D = None) by (intros D; unfold sig_ind; rewrite E; reflexivity).
  assert (He : forall D s, sig_elim sg D s = None) by (intros D s; unfold sig_elim; rewrite E; reflexivity).
  assert (Hd : forall f, sig_def sg f = None) by (intros f; unfold sig_def; rewrite E; reflexivity).
  split; [ | | | exact (generated_empty sg E)].
  - intros [D | D c | D s | f] T HT; cbn [sig_type] in HT;
      [rewrite Hi in HT | rewrite Hi in HT | rewrite He in HT | rewrite Hd in HT]; discriminate HT.
  - intros [D | D c | D s | f] T b HT Hb; cbn [sig_delta] in Hb; try discriminate Hb.
    rewrite Hd in Hb. discriminate Hb.
  - intros D s T H. rewrite He in H. discriminate H.
Qed.

Lemma inv_entries : forall sg sg', sig_entries sg' = sig_entries sg -> sig_inv sg -> sig_inv sg'.
Proof.
  intros sg sg' E [Hty Hbd Hins Hc].
  pose proof (sig_le_entries _ _ E) as Hle'. pose proof (sig_le_entries _ _ (eq_sym E)) as Hle.
  split; [ | | | exact (generated_entries sg sg' E Hc)].
  - intros g T HT. destruct (Hty g T (le_type _ _ Hle' _ _ HT)) as [s Hs].
    exists s. exact (typed_sig_mono _ _ _ Hle _ _ _ Hs).
  - intros g T b HT Hb. exact (typed_sig_mono _ _ _ Hle _ _ _ (Hbd g T b (le_type _ _ Hle' _ _ HT) (le_delta _ _ Hle' _ _ Hb))).
  - intros D s T H. destruct (Hins D s T (le_elim _ _ Hle' _ _ _ H)) as (d & Hd & -> & Hr).
    exists d. split; [exact (le_ind _ _ Hle _ _ Hd) | split; [reflexivity | exact (rules_typed_mono _ _ _ _ Hle Hr)]].
Qed.

Theorem checked_inv_typed : forall sg, wf_checked sg -> sig_inv sg.
Proof.
  pose proof declaration_typed_holds as Hdecl. intros sg H. induction H as [sg E | sg st sg' sg'' _ IH Hs Hrun E].
  - exact (inv_empty sg E).
  - apply (inv_entries sg' sg'' E). apply (walk_run_step sig_inv sg st sg'); try assumption.
    + intros Sp fuel sg0 raw log log' sg0' d HSp H0. exact (declare_ind_inv Hdecl _ _ _ _ _ _ _ _ HSp H0).
    + intros Sp fuel sg0 D s log log' sg0' HSp H0. exact (declare_elim_inv _ _ _ _ _ _ _ _ HSp H0).
    + intros Sp fuel sg0 f A b log log' sg0' HSp H0. exact (define_inv _ _ _ _ _ _ _ _ _ HSp H0).
Qed.

Corollary checked_typed : forall sg, wf_checked sg -> signature_typed SP sg.
Proof. intros sg H. exact (inv_typed _ (checked_inv_typed sg H)). Qed.
