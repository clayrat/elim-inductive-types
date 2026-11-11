(** * ι keeps the declarative type, from the checked rules

    A registration checks the ι-rules of an instance [elim_D[s]] once,
    each in the generic context of the parameters, the motive, the
    methods and the fields of its constructor (Elim/Generate.v).  This file shows that the check covers every
    ι-contraction of the kernel ([iota_typed]): if the right side of each
    rule has the type of the rule there, then every redex
    [elim_D[s] ps P m̄ is (c ps' xs)] typed at [T] contracts to a term of
    type [T].

    The contraction is the right side of the rule of [c] with the
    parameters, motive and methods of the redex and the fields [xs] of
    its object substituted for the variables of the context
    ([typing_tsub] of PTS.Inversion).  The arguments of the redex are
    typed against the telescope of the type of the instance; the fields
    against the fields of [c] at the parameters [ps'] of the object, which
    are convertible to [ps] since the object has type [D ps is]
    ([conv_ind_spine]).  The type of the instance gives the redex the
    type [P is x]; the rule gives the contraction [P ū[ps, xs] (c ps xs)],
    convertible to it.  This reading of a typed redex, in any table and
    context, is [redex_typed]; the erasure of ι in erasure-cic rests on it
    too.

    Only the types of the constants are needed of the signature
    ([sig_types_typed]), with a full table for the case where [T] is a
    sort: so the lemma serves to show a signature type-correct, ι being
    the last condition of [signature_typed]. *)

From Stdlib Require Import List Arith Lia Bool.
From Stdlib Require String.
Import ListNotations.
From DepTypes.Common Require Import Lists.
From DepTypes.PTS Require Import Syntax Telescope Spec Signature Reduction SubstLaws Typing TypingSubst
  Confluence Inversion SubjectRed BidirSound.
From IndTypes Require Import Telescope.
From IndTypes.Elim Require Import Generate.
From IndTypes.Checked Require Import Invariants Shaped.

Local Open Scope list_scope.

(** ** Renamed telescopes *)

Lemma subst_tele_rename_tele : forall Ts sb r,
  subst_tele sb (rename_tele r Ts) = subst_tele (fun i => sb (r i)) Ts.
Proof.
  induction Ts as [|T Ts IH]; intros sb r; [reflexivity | ]. cbn [rename_tele subst_tele].
  rewrite subst_rename, IH. f_equal. apply subst_tele_ext. intros [|i]; reflexivity.
Qed.

(** ** The arguments of an eliminator *)

Lemma split5 : forall (a : list term) n1 n2 n3, length a = n1 + 1 + n2 + n3 + 1 ->
  exists l1 y l2 l3 z, a = l1 ++ [y] ++ l2 ++ l3 ++ [z] /\
    length l1 = n1 /\ length l2 = n2 /\ length l3 = n3.
Proof.
  intros a n1 n2 n3 H.
  assert (H1 : length (skipn n1 a) = S (n2 + n3 + 1)) by (rewrite length_skipn; lia).
  destruct (skipn n1 a) as [|y r2] eqn:Er1; [discriminate H1 | ]. injection H1 as H1.
  assert (H4 : length (skipn n3 (skipn n2 r2)) = 1) by (rewrite !length_skipn; lia).
  destruct (skipn n3 (skipn n2 r2)) as [|z [|]] eqn:Er4; try discriminate H4.
  exists (firstn n1 a), y, (firstn n2 r2), (firstn n3 (skipn n2 r2)), z. split.
  - rewrite <- (firstn_skipn n1 a) at 1. rewrite Er1. cbn [app]. f_equal.
    rewrite <- (firstn_skipn n2 r2) at 1. f_equal.
    rewrite <- (firstn_skipn n3 (skipn n2 r2)) at 1. rewrite Er4. reflexivity.
  - rewrite !length_firstn, !length_skipn. repeat split; lia.
Qed.

(** ** The generated types *)

Lemma length_methods : forall d, length (methods d) = length (ind_ctors d).
Proof. intros d. unfold methods. rewrite length_lifted, length_map. reflexivity. Qed.

Lemma elim_type_tele : forall d s, elim_type d s =
  pis (ind_params d ++ [motive_type d s] ++ methods d ++
       rename_tele (Nat.add (S (length (ind_ctors d)))) (ind_indices d) ++
       [apps (Const (Ind (ind_name d)))
          (vars (length (ind_indices d) + S (length (ind_ctors d))) (length (ind_params d)) ++
           vars 0 (length (ind_indices d)))])
      (apps (Var (S (length (ind_ctors d) + length (ind_indices d))))
            (vars 1 (length (ind_indices d)) ++ [Var 0])).
Proof. intros d s. unfold elim_type. rewrite !pis_app. reflexivity. Qed.

Lemma rules_from_nth : forall d s cs j i c, nth_error cs i = Some c ->
  nth_error (rules_from d s j cs) i = Some (iota_rule_of d s (j + i) c).
Proof.
  intros d s cs. induction cs as [|c' cs IH]; intros j i c H; [destruct i; discriminate H | ].
  destruct i as [|i]; cbn [nth_error rules_from] in H |- *.
  - injection H as <-. rewrite Nat.add_0_r. reflexivity.
  - rewrite (IH (S j) i c H). do 2 f_equal. lia.
Qed.

(** ** The shape of a redex *)

Lemma iota_inv : forall sg t u, iota sg t = Some u ->
  exists D s A d ps P ms is x i cd c ps' xs m,
    sig_elim sg D s = Some (A, true) /\ sig_ind sg D = Some d /\
    t = apps (Const (Elim D s)) (ps ++ [P] ++ ms ++ is ++ [x]) /\
    length ps = length (ind_params d) /\ length ms = length (ind_ctors d) /\
    length is = length (ind_indices d) /\
    x = apps (Const (Ctor D c)) (ps' ++ xs) /\ find_ctor (ind_ctors d) c = Some (i, cd) /\
    length ps' = length (ind_params d) /\ length xs = length (ctor_fields cd) /\
    nth_error ms i = Some m /\
    u = apps m (iota_args D s (ps ++ [P] ++ ms) (rev ps) (ctor_fields cd) xs).
Proof.
  intros sg t u Hi.
  unfold iota in Hi. destruct (elim_view sg t) as [[[D s] d]|] eqn:Ev; [ | discriminate Hi].
  unfold elim_view, elim_head in Ev.
  destruct (spine_head t) eqn:Eh; try discriminate Ev. destruct g as [ | | D' s' | ]; try discriminate Ev.
  destruct (sig_elim sg D' s') as [[A [|]]|] eqn:Ee; try discriminate Ev.
  destruct (sig_ind sg D') as [d'|] eqn:Ed; try discriminate Ev.
  destruct (Nat.eqb (length (spine_args t)) (elim_arity d')) eqn:El; [ | discriminate Ev].
  injection Ev as -> -> ->. apply Nat.eqb_eq in El. unfold elim_arity in El.
  destruct (split5 _ _ _ _ El) as (ps & P & ms & is & x & Ea & Hlp & Hlk & Hlq).
  assert (Et : t = apps (Const (Elim D s)) (spine_args t)) by (rewrite <- Eh; symmetry; apply apps_spine).
  rewrite Ea in Et, Hi.
  unfold iota_at in Hi.
  assert (E1 : last (ps ++ [P] ++ ms ++ is ++ [x]) (Var 0) = x) by (rewrite !app_assoc; apply last_last).
  assert (E2 : skipn (S (length (ind_params d))) (ps ++ [P] ++ ms ++ is ++ [x]) = ms ++ is ++ [x]).
  { rewrite (app_assoc ps [P]). apply skipn_app_exact. rewrite length_app. cbn [length]. lia. }
  assert (E3 : firstn (S (length (ind_params d)) + length (ind_ctors d)) (ps ++ [P] ++ ms ++ is ++ [x]) =
               ps ++ [P] ++ ms).
  { rewrite (app_assoc [P] ms (is ++ [x])), (app_assoc ps ([P] ++ ms) (is ++ [x])).
    apply firstn_app_exact. rewrite !length_app. cbn [length]. lia. }
  assert (E4 : firstn (length (ind_params d)) (ps ++ [P] ++ ms ++ is ++ [x]) = ps) by (apply firstn_app_exact; lia).
  rewrite E1, E2, E3, E4, (firstn_app_exact ms _ (length (ind_ctors d))) in Hi by lia. rewrite rev'_rev in Hi.
  destruct (ctor_view D d x) as [[[i cd] xs]|] eqn:Ecv; [ | discriminate Hi].
  destruct (nth_error ms i) as [m|] eqn:Em; [ | discriminate Hi].
  injection Hi as <-.
  destruct (ctor_view_spec _ _ _ _ _ _ Ecv) as (c & ps' & Ex & Ec & Hlp' & Hlx).
  exists D, s, A, d, ps, P, ms, is, x, i, cd, c, ps', xs, m. repeat split; try assumption; reflexivity.
Qed.

(** ** The typing of a redex

    A typed redex of an instance whose object is a constructor applied to
    parameters [ps'] and fields [xs], read against the type of the
    instance: the parameters, motive and methods have the types of the
    telescope of the eliminator, the object has the family at the
    parameters and indices of the redex, the parameters of the
    constructor are convertible with those of the redex, the fields have
    the types of the fields at the parameters of the redex, within a
    type, and the type of the redex is convertible with the motive at the
    indices of the constructor and the constructor.  [iota_typed] below
    rests on it, and so does the erasure of ι in erasure-cic. *)

(** The family applied to the parameters and indices of a redex. *)
Lemma inst_family : forall D ps P ms is p k q,
  length ps = p -> length ms = k -> length is = q ->
  subst (tsub ((ps ++ [P] ++ ms) ++ is)) (apps (Const (Ind D)) (vars (q + Datatypes.S k) p ++ vars 0 q)) =
  apps (Const (Ind D)) (ps ++ is).
Proof.
  intros D ps P ms is p k q Hp Hk Hq. rewrite subst_apps, map_app. cbn [subst]. f_equal. f_equal.
  - rewrite <- !app_assoc.
    replace (q + Datatypes.S k) with (length ([P] ++ ms ++ is)) by (rewrite !length_app; cbn [length]; lia).
    rewrite <- Hp. apply map_tsub_vars_in with (l0 := []).
  - rewrite <- Hq. apply map_tsub_vars_last.
Qed.

Section Redex.
  Variable S : spec.
  Variable sg : signature.
  Hypothesis Htypes : sig_types_typed S sg.
  Local Notation typed := (has_type S sg).

  Lemma redex_typed : forall G D s act d ps P ms is x c cd i ps' xs T,
    sig_elim sg D s = Some (elim_type d s, act) -> sig_ind sg D = Some d ->
    length ps = length (ind_params d) -> length ms = length (ind_ctors d) -> length is = length (ind_indices d) ->
    x = apps (Const (Ctor D c)) (ps' ++ xs) -> find_ctor (ind_ctors d) c = Some (i, cd) ->
    length ps' = length (ind_params d) -> length xs = length (ctor_fields cd) ->
    typed G (apps (Const (Elim D s)) (ps ++ [P] ++ ms ++ is ++ [x])) T ->
    args_typed S sg G (ind_params d ++ [motive_type d s] ++ methods d) (ps ++ [P] ++ ms) /\
    typed G x (apps (Const (Ind D)) (ps ++ is)) /\
    Forall2 (conv sg) ps' ps /\
    args_typed S sg G (subst_tele (tsub ps) (field_types D (length (ind_params d)) 0 (ctor_fields cd))) xs /\
    (exists R sF, typed G (pis (subst_tele (tsub ps) (field_types D (length (ind_params d)) 0 (ctor_fields cd))) R)
                     (Srt sF)) /\
    conv sg (apps P (map (subst (tsub (ps ++ xs))) (ctor_indices cd) ++ [apps (Const (Ctor D c)) (ps ++ xs)])) T.
  Proof.
    intros G D s act d ps P ms is x c cd i ps' xs T Ee Ed Hlp Hlk Hlq Ex Ec Hlp' Hlx Ht.
    pose proof (sig_ind_name _ _ _ Ed) as Hname.
    remember (length (ind_params d)) as p eqn:Ep.
    remember (length (ind_ctors d)) as k eqn:Ek.
    remember (length (ind_indices d)) as q eqn:Eq.
    remember (length (ctor_fields cd)) as n eqn:En.
    set (pre := ps ++ [P] ++ ms).
    assert (Hlpre : length pre = p + Datatypes.S k) by (unfold pre; rewrite !length_app; cbn [length]; lia).
    assert (Eargs : ps ++ [P] ++ ms ++ is ++ [x] = pre ++ (is ++ [x])) by (unfold pre; rewrite <- !app_assoc; reflexivity).
    rewrite Eargs in Ht.
    pose proof (typed_wf _ _ _ _ _ Ht) as HG.
    assert (HtyE : sig_type sg (Elim D s) = Some (elim_type d s)) by (cbn [sig_type]; rewrite Ee; reflexivity).
    destruct (const_type_typed_t S sg Htypes G _ _ HG HtyE) as [s0 Hs0].
    pose proof (const_head S sg G _ _ HtyE) as Hhd.
    rewrite elim_type_tele, Hname, <- Ep, <- Ek, <- Eq in Hs0, Hhd.
    set (X := apps (Const (Ind D)) (vars (q + Datatypes.S k) p ++ vars 0 q)) in *.
    assert (ETel : ind_params d ++ [motive_type d s] ++ methods d ++ rename_tele (Nat.add (Datatypes.S k)) (ind_indices d) ++ [X] =
                   (ind_params d ++ [motive_type d s] ++ methods d) ++
                   (rename_tele (Nat.add (Datatypes.S k)) (ind_indices d) ++ [X]))
      by (rewrite <- !app_assoc; reflexivity).
    rewrite ETel in Hs0, Hhd.
    assert (HlTel : length ((ind_params d ++ [motive_type d s] ++ methods d) ++
                            (rename_tele (Nat.add (Datatypes.S k)) (ind_indices d) ++ [X])) = length (pre ++ (is ++ [x]))).
    { rewrite !length_app, length_methods, length_rename_tele, Hlpre. cbn [length]. lia. }
    destruct (apps_inv S sg _ G _ _ _ _ _ HlTel Ht Hhd Hs0) as [Hargs HcT].
    assert (Hlpre' : length (ind_params d ++ [motive_type d s] ++ methods d) = length pre).
    { rewrite Hlpre, !length_app, length_methods. cbn [length]. lia. }
    destruct (proj1 (args_typed_app S sg pre G _ _ _ Hlpre') Hargs) as [Hpre Hrest].
    rewrite subst_tele_app in Hrest.
    assert (Hlq' : length (subst_tele (tsub pre) (rename_tele (Nat.add (Datatypes.S k)) (ind_indices d))) = length is).
    { rewrite subst_tele_length, length_rename_tele. lia. }
    destruct (proj1 (args_typed_app S sg is G _ _ _ Hlq') Hrest) as [_ Hx].
    cbn [subst_tele] in Hx. apply args_typed_cons_inv in Hx as [Hx _].
    rewrite length_rename_tele, <- Eq, subst_subst in Hx.
    assert (EX : subst (fun j => subst (tsub is) (upn q (tsub pre) j)) X = apps (Const (Ind D)) (ps ++ is)).
    { rewrite (subst_ext X _ (tsub (pre ++ is))) by (intros j; replace q with (length is) by lia; apply tsub_app).
      unfold X, pre. apply inst_family; lia. }
    rewrite EX in Hx. clear EX.
    assert (HtyC : sig_type sg (Ctor D c) = Some (ctor_type d cd)) by (cbn [sig_type]; rewrite Ed, Ec; reflexivity).
    destruct (const_type_typed_t S sg Htypes G _ _ HG HtyC) as [sc Hsc].
    pose proof (const_head S sg G _ _ HtyC) as Hhc.
    rewrite (ctor_type_split _ _ _ cd Ed), <- pis_app, <- Ep, <- En in Hsc, Hhc.
    set (Fs := field_types D p 0 (ctor_fields cd)) in *.
    assert (HlFs : length Fs = n) by (unfold Fs; rewrite field_types_length; lia).
    assert (Hlc : length (ind_params d ++ Fs) = length (ps' ++ xs)) by (rewrite !length_app; lia).
    pose proof Hx as Hx0. rewrite Ex in Hx.
    destruct (apps_inv S sg _ G _ _ _ _ _ Hlc Hx Hhc Hsc) as [Hargc Hcc].
    rewrite subst_apps, map_app in Hcc. cbn [subst] in Hcc.
    replace n with (length xs) in Hcc by lia. replace p with (length ps') in Hcc by lia.
    rewrite map_tsub_vars in Hcc.
    apply conv_ind_spine in Hcc.
    destruct (forall2_app_split (conv sg) ps' ps _ _ ltac:(lia) Hcc) as [Hpp Hii].
    assert (Hlp'' : length (ind_params d) = length ps') by lia.
    destruct (proj1 (args_typed_app S sg ps' G _ _ _ Hlp'') Hargc) as [_ Hxs].
    assert (Hps : args_typed S sg G (ind_params d) ps).
    { unfold pre in Hpre.
      exact (proj1 (proj1 (args_typed_app S sg ps G (ind_params d) ([motive_type d s] ++ methods d) ([P] ++ ms)
                             ltac:(lia)) Hpre)). }
    pose proof Hsc as Hsc'. rewrite pis_app in Hsc'.
    destruct (typed_pis_inst S sg _ _ _ _ _ Hps Hsc') as [sF HF].
    rewrite subst_pis in HF.
    assert (Hxs' : args_typed S sg G (subst_tele (tsub ps) Fs) xs)
      by exact (args_typed_conv S sg _ _ _ Hxs _ _ _ (conv_subst_tele_tsub sg _ _ Hpp Fs 0) HF).
    assert (ER : subst (tsub (pre ++ is ++ [x])) (apps (Var (Datatypes.S (k + q))) (vars 1 q ++ [Var 0])) =
                 apps P (is ++ [x])).
    { rewrite subst_apps, map_app. cbn [subst map]. f_equal; [ | f_equal; [ | f_equal]].
      - unfold pre. replace (Datatypes.S (k + q)) with (length (ms ++ is ++ [x]) + 0)
          by (rewrite !length_app; cbn [length]; lia).
        rewrite <- !app_assoc, (app_assoc ps [P]), tsub_app_ge. unfold tsub. rewrite rev_app_distr. reflexivity.
      - replace q with (length is) by lia. replace 1 with (length [x]) by reflexivity.
        apply map_tsub_vars_in.
      - unfold tsub. rewrite !rev_app_distr. reflexivity. }
    rewrite ER in HcT.
    assert (Hpp' : Forall2 (conv sg) (ps ++ xs) (ps' ++ xs)).
    { apply Forall2_app; [exact (forall2_conv_sym _ _ _ Hpp) | apply forall2_conv_refl]. }
    split; [exact Hpre | split; [exact Hx0 | split; [exact Hpp | split; [exact Hxs' | split; [eauto | ]]]]].
    eapply conv_trans; [ | exact HcT]. apply conv_apps; [apply conv_refl | ]. apply Forall2_app.
    - eapply forall2_conv_trans; [ | exact Hii].
      apply forall2_conv_map. intros v. exact (conv_subst_tsub sg _ _ Hpp' 0 v).
    - constructor; [ | constructor]. rewrite Ex. apply conv_apps; [apply conv_refl | exact Hpp'].
  Qed.
End Redex.

(** ** The lemma *)

Section Iota.
  Variable S : spec.
  Variable sg : signature.
  Hypothesis Htypes : sig_types_typed S sg.
  Hypothesis Hfull : full_table S.
  Local Notation typed := (has_type S sg).

  Hypothesis Hinst : instances_checked S sg.

  (** A type of a term is a type: a sort of a full table has one. *)
  Lemma type_typed : forall G t T, typed G t T -> exists s, typed G T (Srt s).
  Proof.
    intros G t T H. destruct (validity_t S sg Htypes _ _ _ H) as [[s ->] | HT]; [ | exact HT].
    destruct (proj1 Hfull s (typed_srt_spec S sg Htypes _ _ _ H)) as [s' Hs'].
    exists s'. exact (T_Sort _ _ _ _ _ (typed_wf _ _ _ _ _ H) Hs').
  Qed.

  Theorem iota_typed : forall G t u T, iota sg t = Some u -> typed G t T -> typed G u T.
  Proof.
    intros G t u T Hi Ht.
    destruct (iota_inv _ _ _ Hi) as (D & s & A & d & ps & P & ms & is & x & i & cd & c & ps' & xs & m &
      Ee & Ed & Et & Hlp & Hlk & Hlq & Ex & Ec & Hlp' & Hlx & Em & Eu).
    subst t u.
    destruct (Hinst _ _ _ Ee) as (d0 & Hd0 & -> & Hrules). rewrite Ed in Hd0. injection Hd0 as <-.
    destruct (redex_typed S sg Htypes G D s true d ps P ms is x c cd i ps' xs T Ee Ed Hlp Hlk Hlq Ex Ec Hlp' Hlx Ht)
      as (Hpre & _ & _ & Hxs' & _ & Hc).
    pose proof (typed_wf _ _ _ _ _ Ht) as HG.
    pose proof (sig_ind_name _ _ _ Ed) as Hname.
    pose proof (proj2 (sig_ind_closed _ _ _ Ed)) as Hcs. rewrite forallb_forall in Hcs.
    pose proof (find_ctor_nth_error _ _ _ _ Ec) as Ecd.
    pose proof (find_ctor_name _ _ _ _ Ec) as Ecn.
    pose proof (Hcs cd (nth_error_In _ _ Ecd)) as Hccl. unfold ctor_closed in Hccl.
    apply andb_prop in Hccl as [Hfcl _].
    remember (length (ind_params d)) as p eqn:Ep.
    remember (length (ind_ctors d)) as k eqn:Ek.
    remember (length (ind_indices d)) as q eqn:Eq.
    remember (length (ctor_fields cd)) as n eqn:En.
    set (pre := ps ++ [P] ++ ms).
    set (Fs := field_types D p 0 (ctor_fields cd)) in *.
    assert (Hlpre' : length (ind_params d ++ [motive_type d s] ++ methods d) = length pre).
    { unfold pre. rewrite !length_app, length_methods. cbn [length]. lia. }
    (* the rule of the constructor, instantiated *)
    assert (Hin : In (iota_rule_of d s i cd) (iota_rules d s)).
    { apply (nth_error_In _ i). unfold iota_rules. exact (rules_from_nth d s _ 0 i cd Ecd). }
    pose proof (Hrules _ Hin) as Hr. unfold iota_rule_of in Hr. cbv zeta in Hr.
    cbn [rule_ctx rule_rhs rule_type] in Hr.
    rewrite Hname, <- Ep, <- Ek, <- En in Hr. fold Fs in Hr.
    set (Fr := rename_tele (Nat.add (Datatypes.S k)) Fs) in *.
    assert (Ectx : rev Fr ++ rev (methods d) ++ [motive_type d s] ++ rev (ind_params d) =
                   rev ((ind_params d ++ [motive_type d s] ++ methods d) ++ Fr)).
    { rewrite !rev_app_distr. cbn [rev app]. rewrite <- !app_assoc. reflexivity. }
    rewrite Ectx in Hr.
    assert (Hall : args_typed S sg G ((ind_params d ++ [motive_type d s] ++ methods d) ++ Fr) (pre ++ xs)).
    { apply (proj2 (args_typed_app S sg pre G _ _ _ Hlpre')). split; [exact Hpre | ].
      unfold Fr. rewrite subst_tele_rename_tele.
      rewrite (subst_tele_ext _ _ (tsub ps)); [exact Hxs' | ].
      intros j. unfold pre.
      replace (Datatypes.S k + j) with (length ([P] ++ ms) + j) by (rewrite length_app; cbn [length]; lia).
      apply tsub_app_ge. }
    destruct (typed_weaken_below S sg _ G (typed_wf _ _ _ _ _ Hr) HG) as [_ Hw].
    pose proof (typing_tsub S sg _ _ _ Hall _ _ (Hw _ _ Hr)) as Hu.
    (* the substituted right side is the contraction *)
    set (sb := tsub (pre ++ xs)) in *.
    assert (Hsb_params : map (subst sb) (vars (n + Datatypes.S k) p) = ps).
    { unfold sb, pre. replace (n + Datatypes.S k) with (length ([P] ++ ms ++ xs)) by (rewrite !length_app; cbn [length]; lia).
      replace p with (length ps) by lia. rewrite <- !app_assoc. apply map_tsub_vars_in with (l0 := []). }
    assert (Hsb_P : sb (n + k) = P).
    { unfold sb, pre. replace (n + k) with (length xs + (length ms + 0)) by lia.
      rewrite tsub_app_ge, app_assoc, tsub_app_ge. unfold tsub. rewrite rev_app_distr. reflexivity. }
    assert (Hsb_ms : map (subst sb) (vars n k) = ms).
    { unfold sb, pre. replace n with (length xs) by lia. replace k with (length ms) by lia.
      rewrite <- !app_assoc, (app_assoc ps [P]). apply map_tsub_vars_in. }
    assert (Hsb_xs : map (subst sb) (vars 0 n) = xs).
    { unfold sb. replace n with (length xs) by lia. apply map_tsub_vars_last. }
    assert (Hik : i < k).
    { assert (i < length ms) by (apply nth_error_Some; congruence). lia. }
    assert (Hsb_m : sb (n + k - 1 - i) = m).
    { unfold sb. replace (n + k - 1 - i) with (length xs + (k - 1 - i)) by lia. rewrite tsub_app_ge.
      unfold pre. rewrite (app_assoc ps [P]), tsub_app_lt by lia. unfold tsub.
      rewrite (nth_indep _ _ m) by (rewrite length_rev; lia).
      rewrite rev_nth by lia. replace (length ms - Datatypes.S (k - 1 - i)) with i by lia.
      apply nth_error_nth. exact Em. }
    rewrite subst_apps in Hu. cbn [subst] in Hu. rewrite Hsb_m in Hu.
    rewrite iota_args_subst in Hu by (rewrite length_rev, length_vars; exact Hfcl).
    rewrite !map_app, map_rev, Hsb_params, Hsb_ms, Hsb_xs in Hu. cbn [map subst] in Hu. rewrite Hsb_P in Hu.
    (* its type *)
    rewrite subst_apps, map_app, map_map in Hu. cbn [subst map] in Hu. rewrite Hsb_P in Hu.
    rewrite subst_apps, map_app, Hsb_params, Hsb_xs in Hu. cbn [subst] in Hu. rewrite Ecn in Hu.
    rewrite (map_ext _ (subst (tsub (ps ++ xs)))) in Hu.
    2: { intros v. rewrite subst_rename. apply subst_ext. intros j.
         destruct (Nat.lt_ge_cases j n) as [Hj | Hj].
         - rewrite upn_ren_lt by exact Hj. unfold sb. rewrite !tsub_app_lt by lia. reflexivity.
         - replace j with (n + (j - n)) by lia. rewrite upn_ren_ge. unfold sb.
           replace (n + (Datatypes.S k + (j - n))) with (length xs + (length ([P] ++ ms) + (j - n)))
             by (rewrite length_app; cbn [length]; lia).
           rewrite tsub_app_ge. unfold pre. rewrite tsub_app_ge.
           replace (n + (j - n)) with (length xs + (j - n)) by lia. rewrite tsub_app_ge. reflexivity. }
    (* its type, the type of the redex up to conversion *)
    destruct (type_typed _ _ _ Ht) as [sT HT].
    exact (T_Conv _ _ _ _ _ _ _ Hu HT Hc).
  Qed.
End Iota.
