(** * The fields of the declarations of a checked signature

    Two invariants of Checked/Invariants.v, kept by every registration
    ([checked_fields]):
    - [rec_ok]: a recursive field has the type of its family at as many
      indices as the family has, which classification checks
      ([family_args] of Elim/Decl.v);
    - [singleton_ok]: the fields of the constructor of a singleton
      proposition are proofs.  The checker found the sort Prop for each
      field when the declaration was registered, in the signature
      [sg1] where the family has the category of its sort, and only
      then is the category [AllSorts] ([elim_class_of]).  That judgment
      holds in the final signature ([is_type_sg'] of
      Checked/SigTyped.v), and the declarative typing of the type of
      the constructor gives each field some sort; the uniqueness of
      synthesized types ([synth_unique] of PTS/BidirSound.v) makes the
      two the same. *)

From Stdlib Require Import String List Bool Arith Lia.
Import ListNotations.
From DepTypes.Common Require Import Result Traced Lists.
From DepTypes.PTS Require Import Syntax Telescope Spec Signature Reduction SubstLaws Typing TypingSubst Inversion
  Bidir BidirSound Monotone ConstRename.
From DepTypes.Configs Require Import Predicative.
From IndTypes Require Import Registration Telescope.
From IndTypes.Elim Require Import Decl Generate Declare.
From IndTypes.Checked Require Import Steps Invariants Walk Shaped IotaTyped SigTyped.

Local Open Scope list_scope.

Local Notation SP := predicative_prop.

(** ** The fields of a declaration, one at a time *)

Lemma fields_typed_nth : forall Sp sg d fs G l ss j T, fields_typed Sp sg d G l fs ss ->
  nth_error (field_types (ind_name d) (length (ind_params d)) l fs) j = Some T ->
  exists s, nth_error ss j = Some s /\
    is_type_of Sp sg (rev (firstn j (field_types (ind_name d) (length (ind_params d)) l fs)) ++ G) T s.
Proof.
  intros Sp sg d fs. induction fs as [|fd fs IH]; intros G l ss j T H HT; [destruct j; discriminate HT | ].
  destruct ss as [|s ss]; [destruct H | ]. cbn [fields_typed] in H. destruct H as [[Hfd _] Hfs].
  destruct j as [|j]; cbn [field_types nth_error] in HT.
  - injection HT as <-. exists s. split; [reflexivity | exact Hfd].
  - destruct (IH _ _ _ j T Hfs HT) as (s' & Hs' & Ht). exists s'. split; [exact Hs' | ].
    cbn [field_types firstn rev]. rewrite <- app_assoc. exact Ht.
Qed.

(** A telescope that is a type gives each of its entries some sort. *)
Lemma pis_nth_typed : forall sg Ts G R s j T, has_type SP sg G (pis Ts R) (Srt s) -> nth_error Ts j = Some T ->
  exists s', has_type SP sg (rev (firstn j Ts) ++ G) T (Srt s').
Proof.
  intros sg Ts. induction Ts as [|T0 Ts IH]; intros G R s j T H HT; [destruct j; discriminate HT | ].
  cbn [pis] in H. destruct (inv_pi SP sg _ _ _ _ H) as (s1 & s2 & _ & HT0 & HB & _ & _).
  destruct j as [|j]; cbn [nth_error] in HT.
  - injection HT as <-. exists s1. exact HT0.
  - destruct (IH _ _ _ j T HB HT) as [s' Hs']. exists s'. cbn [firstn rev]. rewrite <- app_assoc. exact Hs'.
Qed.

(** ** The invariant *)

Definition fields_inv (sg : signature) : Prop := sig_inv sg /\ rec_ok sg /\ singleton_ok sg.

Lemma inv_ext : forall sg sg', sig_le sg sg' -> (forall D, sig_ind sg' D = sig_ind sg D) ->
  rec_ok sg -> singleton_ok sg -> rec_ok sg' /\ singleton_ok sg'.
Proof.
  intros sg sg' Hle Hind Hrec Hsing. split.
  - intros D d c Bs vs Hd. rewrite Hind in Hd. exact (Hrec D d c Bs vs Hd).
  - intros D d c Hd Hs He Hc j T HT. rewrite Hind in Hd.
    exact (typed_sig_mono _ _ _ Hle _ _ _ (Hsing D d c Hd Hs He Hc j T HT)).
Qed.

(** The fields of the constructor of a singleton proposition just
    declared are proofs. *)
Lemma declared_singleton : forall Sp fuel sg raw log log' sg' d, checking_spec Sp ->
  declare_ind_with Sp fuel Checked sg raw log = (log', Ok (sg', d)) -> sig_inv sg ->
  ind_sort d = Prp -> ind_elim d = AllSorts -> forall c, ind_ctors d = [c] ->
  forall j T, nth_error (field_types (ind_name d) (length (ind_params d)) 0 (ctor_fields c)) j = Some T ->
  has_type SP sg' (rev (ind_params d ++ firstn j (field_types (ind_name d) (length (ind_params d)) 0 (ctor_fields c))))
    T (Srt Prp).
Proof.
  intros Sp fuel sg raw log log' sg' d HSp H Hinv Hs He c Hc j T HT.
  destruct (declaration_typed_holds Sp fuel sg raw log log' sg' d HSp Hinv H) as [_ Hcty].
  destruct (declare_ind_sound Sp fuel _ _ _ _ _ _ _ H) as (d0 & sg1 & fss & Hcl & Hn & E1 & _ & Hcs & Ed & E).
  pose proof (classify_name _ _ _ Hcl) as Hname. rewrite <- Hname in Hn.
  pose proof (classify_decl_strictly_positive raw d0 Hcl) as Hfree.
  assert (Hdname : ind_name d = ind_name d0) by (subst d; reflexivity).
  assert (Hdtype : ind_type d = ind_type d0) by (subst d; reflexivity).
  assert (Hctors : ind_ctors d = ind_ctors d0) by (subst d; reflexivity).
  assert (Hparams : ind_params d = ind_params d0) by (subst d; reflexivity).
  assert (Hsort : ind_sort d = ind_sort d0) by (subst d; reflexivity).
  (* the sorts the checker found are Prop *)
  rewrite Hctors in Hc. rewrite Hc in Hcs.
  destruct (forall2_singleton _ _ _ Hcs) as (ss & Efss & _ & Hft).
  assert (Hss : forallb (sort_eqb Prp) ss = true).
  { rewrite Ed in He. cbn [with_elim ind_elim] in He. rewrite Efss in He.
    rewrite Hsort in Hs. rewrite Hs in He. cbn [elim_class_of] in He.
    destruct (forallb (sort_eqb Prp) ss); [reflexivity | discriminate He]. }
  rewrite Hdname, Hparams in HT |- *.
  set (D := ind_name d0) in *. set (p := length (ind_params d0)) in *.
  set (Fs := field_types D p 0 (ctor_fields c)) in *.
  destruct (fields_typed_nth _ _ _ _ _ _ _ j T Hft HT) as (s0 & Hs0 & Hist).
  assert (Es0 : s0 = Prp).
  { rewrite forallb_forall in Hss. symmetry. apply sort_eqb_eq. exact (Hss s0 (nth_error_In _ _ Hs0)). }
  subst s0. fold Fs in Hist. rewrite <- rev_app_distr in Hist.
  (* the side conditions, read off the type of the constructor *)
  assert (Hin : In c (ind_ctors d0)) by (rewrite Hc; left; reflexivity).
  destruct (ctor_type_good d0 c Hfree Hin) as [Hg1 Hg2].
  unfold ctor_type in Hg1, Hg2. cbv zeta in Hg1, Hg2. fold D p Fs in Hg1, Hg2.
  rewrite an_pis in Hg1. rewrite fixok_pis in Hg2.
  apply andb_prop in Hg1 as [Hg1 _]. apply andb_prop in Hg2 as [Hg2 _].
  rewrite forallb_forall in Hg1, Hg2.
  assert (HTin : In T (ind_params d0 ++ Fs)) by (apply in_or_app; right; exact (nth_error_In _ _ HT)).
  assert (HG : forallb (allnodes (fun _ => true) (notDk D)) (rev (ind_params d0 ++ firstn j Fs)) = true).
  { rewrite forallb_forall. intros x Hx. apply in_rev in Hx.
    assert (Hx' : In x (ind_params d0 ++ Fs)).
    { apply in_app_or in Hx as [Hx | Hx]; apply in_or_app; [left; exact Hx | right].
      rewrite <- (firstn_skipn j Fs). apply in_or_app. left. exact Hx. }
    exact (an_weaken _ _ _ _ _ (fun _ _ => eq_refl) (fun _ x => x) (Hg1 x Hx')). }
  pose proof (is_type_sg' sg Hinv d0 Hn Hfree sg1 E1 d Hdname Hdtype sg' E Sp _ T Prp Hist
                (Hg1 T HTin) (Hg2 T HTin) HG) as (TT & HTT & Hr).
  (* the declarative type of the constructor gives the field a sort, which is Prop *)
  assert (Hcin : In c (ind_ctors d)) by (rewrite Hctors, Hc; left; reflexivity).
  destruct (Hcty c Hcin) as [sc Hsc].
  unfold ctor_type in Hsc. cbv zeta in Hsc. rewrite Hdname, Hparams in Hsc. fold D p Fs in Hsc.
  assert (HT' : nth_error (ind_params d0 ++ Fs) (p + j) = Some T).
  { rewrite nth_error_app2 by (unfold p; lia). replace (p + j - length (ind_params d0)) with j by (unfold p; lia).
    exact HT. }
  destruct (pis_nth_typed sg' _ [] _ _ _ _ Hsc HT') as [s' Hs'].
  rewrite app_nil_r, firstn_app, (firstn_all2 (ind_params d0)) in Hs' by (unfold p; lia).
  replace (p + j - length (ind_params d0)) with j in Hs' by (unfold p; lia).
  pose proof (proj1 (bidir_spec_mono _ _ _ (checking_le _ HSp)) _ _ _ HTT) as HTT'.
  pose proof (synth_unique SP sg' _ _ _ HTT' _ Hs') as Hc1.
  assert (E' : s' = Prp).
  { apply (conv_srt_inj sg'). eapply conv_trans; [apply conv_sym, Hc1 | apply red_conv, Hr]. }
  subst s'. exact Hs'.
Qed.

Lemma declare_fields_inv : forall Sp fuel sg raw log log' sg' d, checking_spec Sp ->
  declare_ind_with Sp fuel Checked sg raw log = (log', Ok (sg', d)) -> fields_inv sg -> fields_inv sg'.
Proof.
  intros Sp fuel sg raw log log' sg' d HSp H (Hinv & Hrec & Hsing).
  split; [exact (declare_ind_inv declaration_typed_holds _ _ _ _ _ _ _ _ HSp H Hinv) | ].
  destruct (declare_ind_sound Sp fuel _ _ _ _ _ _ _ H) as (d0 & sg1 & fss & Hcl & Hn & E1 & _ & Hcs & Ed & E).
  pose proof (classify_name _ _ _ Hcl) as Hname. rewrite <- Hname in Hn.
  assert (Hdname : ind_name d = ind_name d0) by (subst d; reflexivity).
  pose proof (sig_le_ind _ _ d ltac:(rewrite Hdname; exact Hn) E) as Hle.
  split.
  - intros D' d' c Bs vs Hd'. rewrite (add_ind_ind _ _ _ E) in Hd'. destruct (String.eqb (ind_name d) D') eqn:ED.
    + injection Hd' as <-. subst d. exact (classify_rec raw d0 Hcl c Bs vs).
    + exact (Hrec D' d' c Bs vs Hd').
  - intros D' d' c Hd' Hs He Hc j T HT. rewrite (add_ind_ind _ _ _ E) in Hd'. destruct (String.eqb (ind_name d) D') eqn:ED.
    + injection Hd' as <-. apply String.eqb_eq in ED. subst D'.
      exact (declared_singleton Sp fuel sg raw log log' sg' d HSp H Hinv Hs He c Hc j T HT).
    + exact (typed_sig_mono _ _ _ Hle _ _ _ (Hsing D' d' c Hd' Hs He Hc j T HT)).
Qed.

Theorem checked_fields : forall sg, wf_checked sg -> fields_inv sg.
Proof.
  intros sg H. induction H as [sg E | sg st sg' sg'' _ IH Hs Hrun E].
  - split; [exact (inv_empty sg E) | split].
    + intros D d c Bs vs Hd. unfold sig_ind in Hd. rewrite E in Hd. discriminate Hd.
    + intros D d c Hd. unfold sig_ind in Hd. rewrite E in Hd. discriminate Hd.
  - assert (Hstep : fields_inv sg').
    { apply (walk_run_step fields_inv sg st sg'); try assumption.
      - intros Sp fuel sg0 raw log log' sg0' d HSp H0. exact (declare_fields_inv _ _ _ _ _ _ _ _ HSp H0).
      - intros Sp fuel sg0 D s log log' sg0' HSp H0 (Hinv & Hrec & Hsing).
        split; [exact (declare_elim_inv _ _ _ _ _ _ _ _ HSp H0 Hinv) | ].
        destruct (declare_elim_sound Sp fuel _ _ _ _ _ _ H0) as (d & _ & Hn & _ & _ & _ & E0).
        exact (inv_ext _ _ (sig_le_elim _ _ _ _ _ _ Hn E0) (add_elim_ind _ _ _ _ _ _ E0) Hrec Hsing).
      - intros Sp fuel sg0 f A b log log' sg0' HSp H0 (Hinv & Hrec & Hsing).
        split; [exact (define_inv _ _ _ _ _ _ _ _ _ HSp H0 Hinv) | ].
        destruct (define_sound Sp fuel _ _ _ _ _ _ _ H0) as (Hf & _ & _ & E0).
        exact (inv_ext _ _ (sig_le_def _ _ _ _ _ Hf E0) (add_def_ind _ _ _ _ _ E0) Hrec Hsing). }
    destruct Hstep as (Hinv & Hrec & Hsing). split; [exact (inv_entries sg' sg'' E Hinv) | ].
    apply (inv_ext sg' sg'' (sig_le_entries _ _ (eq_sym E))); [ | exact Hrec | exact Hsing].
    intros D. unfold sig_ind. rewrite E. reflexivity.
Qed.
