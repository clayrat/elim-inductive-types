(** * The history of results: [Below_D], [build_D], [recBelow_D]

    After "the Below way" of Sozeau's Equations (§3.1 of the 2010 paper),
    as a scheme of translation in the setting of Rocq: neither the
    mechanism of [Fixpoint] nor every compilation path of today's
    Equations.

    For [D Δ θ̄ : Type_i] and a motive [P θ̄ x : Type_j] the history lives
    in [Type_ℓ], [ℓ := max i j], since the domains of functional recursive
    fields have levels up to i ([within]).  A proposition bounds them by
    nothing: [BigP : Prop] with [mkBigP : (Type₀ → BigP) → BigP] has a
    history [Πy:Type₀. …] in [Type₁] for a motive in [Type₀].  For
    [D : Prop] the level is the largest of j and the levels of the
    domains, inferred by [history_level]; and the history needs the large
    instances its category may not allow.  On a constructor the history
    is the tuple of the components of its recursive fields; a field
    [r : Πȳ:B̄. D Δ v̄] gives [Πȳ:B̄. (P v̄ (r ȳ) × Below_D P v̄ (r ȳ))];
    the empty tuple is [Unit_ℓ], a single component is the component
    itself, and more are nested to the right.  For ℕ:

      Below P zero     = Unit_j
      Below P (succ n) = P n × Below P n

    - [Below_D] by large elimination through [elim_D[ℓ+1]] with the motive
      [λθ̄ x. Type_ℓ]: the hypothesis of a recursive field is the history
      of the field;
    - [build_D : Πθ̄ x. P θ̄ x × Below_D P θ̄ x] through [elim_D[ℓ]], for a
      fixed [step : Πθ̄ x. Below_D P θ̄ x → P θ̄ x]: the hypothesis of a
      recursive field has exactly the type of its component, so the
      history is the tuple of hypotheses, and on [c Δ ā] the result is
      [(step ū (c Δ ā) h, h)];
    - [recBelow_D step] projects the result out of [build_D].

    No new primitive of recursion appears.  All three are δ-constants,
    one triple per pair (D, j): ℓ alone does not determine the type of
    [P].  Without cumulativity [Unit : Type₀] does not stand for [Unit_ℓ]
    at ℓ > 0, which the history of [isEven] checks (Programs.Half).

    The binders of a method are those of the eliminator, laid out by
    [fold_slots] of MethodLayout: each field, a recursive one followed at
    once by its hypothesis; each method is built in the accumulator of
    that pass.  The method of [Below_D] lies after the parameters and P,
    as in the eliminator, and [transport] renames the fields of the
    description into its body; that of [build_D] lies after them and
    [step], and [transport_past 2] does. *)

From Stdlib Require Import List Arith.
From Stdlib Require String.
Import ListNotations.
Import (notations) String.StringSyntax.
Local Open Scope string_scope.
From DepTypes.Common Require Import Result Traced.
From DepTypes.PTS Require Import Syntax Spec Signature.
From IndTypes Require Import Registration Telescope MethodLayout.
From IndTypes.Elim Require Import Decl Generate Declare.

Local Notation string := String.string.

(** ** Names *)

Definition below_name (D : string) (j : nat) : string :=
  String.append "Below_" (String.append D (String.append "_" (show_nat j))).
Definition build_name (D : string) (j : nat) : string :=
  String.append "build_" (String.append D (String.append "_" (show_nat j))).
Definition recbelow_name (D : string) (j : nat) : string :=
  String.append "recBelow_" (String.append D (String.append "_" (show_nat j))).

(** ** Tuples at the level ℓ *)

Section Tuples.
  Variable l : nat.

  Fixpoint tuple_type (As : list term) : term :=
    match As with
    | [] => unit_at l
    | [A] => A
    | A :: As' => times A (tuple_type As')
    end.

  Fixpoint tuple (ts : list term) : term :=
    match ts with
    | [] => tt_at l
    | [t] => t
    | t :: ts' => Pair t (tuple ts')
    end.
End Tuples.

(** ** The three constructions

    For the motive level j at the history level ℓ, [history_level] below:
    the names and the type of P take j, the tuples and the instances ℓ. *)

Section Below.
  Variable d : ind_desc.
  Variable j : nat.
  Variable l : nat.

  Let D := ind_name d.
  Let p := length (ind_params d).
  Let q := length (ind_indices d).

  (** [Πθ̄:Θ̄. Πx:D Δ θ̄. F], with [e] binders between the parameters and
      θ̄. *)
  Definition over_family (e : nat) (F : term) : term :=
    pis (rename_tele (Nat.add e) (ind_indices d))
      (Pi (apps (Const (Ind D)) (vars (q + e) p ++ vars 0 q)) F).

  (** [P θ̄ x] and [Below_D Δ P θ̄ x], with θ̄ x at [base]. *)
  Definition motive_at (P base : nat) : term := apps (Var P) (vars base (S q)).
  Definition below_at (params P base : nat) : term :=
    apps (Const (Def (below_name D j))) (vars params p ++ [Var P] ++ vars base (S q)).

  (** [Π(Δ). ΠP:(Πθ̄. D Δ θ̄ → Type_j). Πθ̄. D Δ θ̄ → Type_ℓ]. *)
  Definition below_type : term :=
    pis (ind_params d) (Pi (motive_type d (Univ j)) (over_family 1 (Srt (Univ l)))).

  (** The component of a recursive field [r : Πȳ:B̄. D Δ v̄] at [bl],
      after the earlier fields at [rbs], with its hypothesis [ih], among
      [b] binders after the parameters and P: [Πȳ:B̄. P v̄ (r ȳ) × ih ȳ],
      where [ih ȳ] is the history of [r ȳ]. *)
  Definition component (b bl : nat) (rbs : list nat) (Bs vs : list term) : term :=
    let m := length Bs in
    let r := transport rbs b in
    pis (rename_tele r Bs)
      (times (apps (Var (b + m)) (map (rename (upn_ren m r)) vs ++ [apps (Var (b - 1 - bl + m)) (vars 0 m)]))
             (apps (Var (b - 2 - bl + m)) (vars 0 m))).

  (** The tuple of the components, built in the accumulator innermost
      first. *)
  Definition below_method (c : ctor_desc) : term :=
    let b := nbinders (ctor_fields c) in
    let '(Cs, _, _) := fold_slots (fun Cs fd _ _ bl rbs =>
                         match fd with
                         | FRec Bs vs => component b bl rbs Bs vs :: Cs
                         | FArg _ => Cs
                         end) [] (ctor_fields c) in
    lams b (tuple_type l (rev Cs)).

  (** [λΔ P. elim_D[ℓ+1] Δ (λθ̄ x. Type_ℓ) m̄]. *)
  Definition below_body : term :=
    lams p (Lam (apps (Const (Elim D (Univ (S l))))
      (vars 1 p ++ [lams (S q) (Srt (Univ l))] ++ map below_method (ind_ctors d)))).

  (** [step : Πθ̄. Πx:D Δ θ̄. Below_D Δ P θ̄ x → P θ̄ x], after P. *)
  Definition step_type : term :=
    over_family 1 (Pi (below_at (q + 2) (q + 1) 0) (motive_at (q + 2) 1)).

  (** [Π(Δ). ΠP. Πstep. Πθ̄. Πx:D Δ θ̄. P θ̄ x × Below_D Δ P θ̄ x]. *)
  Definition build_type : term :=
    pis (ind_params d) (Pi (motive_type d (Univ j)) (Pi step_type
      (over_family 2 (times (motive_at (q + 2) 0) (below_at (q + 3) (q + 2) 0))))).

  (** [Π(Δ). ΠP. Πstep. Πθ̄. Πx:D Δ θ̄. P θ̄ x]. *)
  Definition recbelow_type : term :=
    pis (ind_params d) (Pi (motive_type d (Univ j)) (Pi step_type (over_family 2 (motive_at (q + 2) 0)))).

  (** On [c Δ ā], with the tuple [h] of the hypotheses:
      [(step ū (c Δ ā) h, h)].  [step] lies right before the binders of
      the method. *)
  Definition build_method (c : ctor_desc) : term :=
    let b := nbinders (ctor_fields c) in
    let '(hs, rbs, _) := fold_slots (fun hs fd _ _ bl _ =>
                           match fd with
                           | FRec _ _ => Var (b - 2 - bl) :: hs
                           | FArg _ => hs
                           end) [] (ctor_fields c) in
    let h := tuple l (rev hs) in
    let obj := apps (Const (Ctor D (ctor_name c))) (vars (b + 2) p ++ field_vars rbs b) in
    lams b (Pair (apps (Var b) (map (rename (transport_past 2 rbs b)) (ctor_indices c) ++ [obj; h])) h).

  (** [λΔ P step. elim_D[ℓ] Δ (λθ̄ x. P θ̄ x × Below_D Δ P θ̄ x) m̄]. *)
  Definition build_body : term :=
    lams p (Lam (Lam (apps (Const (Elim D (Univ l)))
      (vars 2 p ++ [lams (S q) (times (motive_at (q + 2) 0) (below_at (q + 3) (q + 2) 0))] ++
       map build_method (ind_ctors d))))).

  (** [λΔ P step θ̄ x. fst (build_D Δ P step θ̄ x)]. *)
  Definition recbelow_body : term :=
    lams (p + 2 + S q) (Fst (apps (Const (Def (build_name D j)))
      (vars (q + 3) p ++ [Var (q + 2); Var (q + 1)] ++ vars 0 (S q)))).
End Below.

(** ** Registration *)

Section Register.
  Variable Sp : spec.
  Variable fuel : nat.

  (** ** The level

      The component [Πȳ:B̄. P v̄ (r ȳ) × ih ȳ] of a recursive field lies
      in [Type_ℓ] once ℓ is at least j and the levels of the domains B̄,
      a proof counting as 0: the level of [Πȳ:B̄. Unit].  For [D : Type_i]
      the registration of D bounded them by i ([within]), and ℓ is
      [max i j] as in the lecture.  A proposition does not bound them:
      their level is inferred, at the stage [AtDomain] of the field. *)

  (** The largest of [l] and the levels of the domains of the recursive
      fields among [fs] of the constructor [c], from position [k] on, in
      the context [G] of the parameters and the earlier fields. *)
  Fixpoint fields_level (sg : signature) (d : ind_desc) (c : string) (G : ctx) (k : nat)
      (fs : list field) (l : nat) : R nat :=
    match fs with
    | [] => tret l
    | fd :: fs' =>
        let! l' := match fd with
                   | FRec ((_ :: _) as Bs) _ =>
                       let! s := sort_of Sp fuel sg (AtDomain (ind_name d) c k) G (pis Bs Unit) in
                       tret (Nat.max (sort_level s) l)
                   | _ => tret l
                   end in
        fields_level sg d c (field_type (ind_name d) (length (ind_params d)) k fd :: G) (S k) fs' l'
    end.

  (** The level of the history of D for a motive in [Type_j]. *)
  Definition history_level (sg : signature) (d : ind_desc) (j : nat) : R nat :=
    match ind_sort d with
    | Prp => tfold (fun l c => fields_level sg d (ctor_name c) (rev (ind_params d)) 0 (ctor_fields c) l)
               j (ind_ctors d)
    | s => tret (Nat.max (sort_level s) j)
    end.

  (** [Below_D], [build_D] and [recBelow_D] for motives in [Type_j], with
      what they need: [Unit_ℓ], [elim_D[ℓ+1]] and [elim_D[ℓ]]; unless
      they are registered already.  Each is a δ-constant checked in the
      signature without it. *)
  Definition ensure_below (sg : signature) (D : string) (j : nat) : R signature :=
    match sig_def sg (recbelow_name D j) with
    | Some _ => tret sg
    | None =>
        let! d := match sig_ind sg D with Some d => tret d | None => refuse (RUndeclared D) end in
        let! l := history_level sg d j in
        let! sg := ensure_unit Sp fuel sg l in
        let! sg := ensure_elim Sp fuel sg D (Univ (S l)) in
        let! sg := ensure_elim Sp fuel sg D (Univ l) in
        let! sg := define Sp fuel sg (below_name D j) (below_type d j l) (below_body d l) in
        let! sg := define Sp fuel sg (build_name D j) (build_type d j) (build_body d j l) in
        define Sp fuel sg (recbelow_name D j) (recbelow_type d j) (recbelow_body d j)
    end.
End Register.

(** ** What a registration of the history guarantees

    Over [Unit_ℓ] and the two instances, which their own registrations
    guarantee (Elim.Declare), the three constructions are δ-constants
    [defined] as in Registration: each with a type that is a type and a
    body checked against it in the signature before it, in the judgments
    of the annotated kernel.  Their level is at least j and, for a
    proposition, bounds the domains of its recursive fields by the
    checks of [history_level]; for [D : Type_i] it is [max i j]. *)

Section Sound.
  Variable Sp : spec.
  Variable fuel : nat.

  (** ** The level *)

  (** ℓ bounds the domains of the recursive fields among [fs], from
      position [k] on, in the context [G]: [Πȳ:B̄. Unit] is a type of a
      level up to ℓ. *)
  Fixpoint domains_within (sg : signature) (d : ind_desc) (G : ctx) (k : nat) (fs : list field)
      (l : nat) : Prop :=
    match fs with
    | [] => True
    | fd :: fs' =>
        match fd with
        | FRec ((_ :: _) as Bs) _ => exists s, is_type_of Sp sg G (pis Bs Unit) s /\ sort_level s <= l
        | _ => True
        end /\
        domains_within sg d (field_type (ind_name d) (length (ind_params d)) k fd :: G) (S k) fs' l
    end.

  (** ℓ is a level of the history of D for a motive in [Type_j]. *)
  Definition history_bounds (sg : signature) (d : ind_desc) (j l : nat) : Prop :=
    j <= l /\ Forall (fun c => domains_within sg d (rev (ind_params d)) 0 (ctor_fields c) l) (ind_ctors d).

  (** The level [history_level] takes. *)
  Definition history_level_spec (sg : signature) (d : ind_desc) (j l : nat) : Prop :=
    match ind_sort d with
    | Prp => history_bounds sg d j l
    | s => l = Nat.max (sort_level s) j
    end.

  Lemma domains_within_mono : forall sg d fs G k l l',
    l <= l' -> domains_within sg d G k fs l -> domains_within sg d G k fs l'.
  Proof.
    intros sg d fs. induction fs as [|fd fs IH]; intros G k l l' Hl H; [exact I | ].
    destruct H as [H0 H]. split; [ | eapply IH; eassumption].
    destruct fd as [A|[|B Bs] vs]; try exact I.
    destruct H0 as (s & Hs & Hle). exists s. split; [exact Hs | eapply Nat.le_trans; eassumption].
  Qed.

  Lemma fields_level_ok : forall sg d c fs G k l log log' l',
    fields_level Sp fuel sg d c G k fs l log = (log', Ok l') -> l <= l' /\ domains_within sg d G k fs l'.
  Proof.
    intros sg d c fs. induction fs as [|fd fs IH]; intros G k l log log' l' H; cbn [fields_level] in H.
    - apply tret_ok in H. subst l'. split; [apply Nat.le_refl | exact I].
    - tbind_in H l1 H1. apply IH in H as [Hl H].
      destruct fd as [A|[|B Bs] vs].
      1, 2: apply tret_ok in H1; subst l1; split; [exact Hl | split; [exact I | exact H]].
      tbind_in H1 s Hs. apply sort_of_ok in Hs as [_ Hs]. apply tret_ok in H1. subst l1.
      split; [eapply Nat.le_trans; [apply Nat.le_max_r | exact Hl] | split; [ | exact H]].
      exists s. split; [exact Hs | eapply Nat.le_trans; [apply Nat.le_max_l | exact Hl]].
  Qed.

  Lemma history_level_ok : forall sg d j log log' l,
    history_level Sp fuel sg d j log = (log', Ok l) -> history_level_spec sg d j l.
  Proof.
    intros sg d j log log' l H. unfold history_level in H. unfold history_level_spec.
    destruct (ind_sort d); try (apply tret_ok in H; exact H).
    unfold history_bounds. revert j log H.
    induction (ind_ctors d) as [|c cs IH]; intros acc log H; cbn [tfold] in H.
    - apply tret_ok in H. subst acc. split; [apply Nat.le_refl | constructor].
    - tbind_in H l1 H1. apply fields_level_ok in H1 as [Hacc H1]. apply IH in H as [Hl H].
      split; [eapply Nat.le_trans; eassumption | constructor; [ | exact H]].
      eapply domains_within_mono; eassumption.
  Qed.

  (** ** The constructions *)

  Lemma ensure_unit_extends : forall sg l log log' sg',
    ensure_unit Sp fuel sg l log = (log', Ok sg') -> exists es, sig_entries sg' = es ++ sig_entries sg.
  Proof.
    intros sg l log log' sg' H. unfold ensure_unit in H.
    destruct l as [|l]; [apply tret_ok in H; subst; now exists [] | ].
    destruct (sig_ind sg (unit_name (S l))); [apply tret_ok in H; subst; now exists [] | ].
    tbind_in H r Hr. apply tret_ok in H. subst sg'. destruct r as [sg1 d].
    apply declare_ind_extends in Hr. now exists [EInd d].
  Qed.

  Lemma ensure_elim_extends : forall sg D s log log' sg',
    ensure_elim Sp fuel sg D s log = (log', Ok sg') -> exists es, sig_entries sg' = es ++ sig_entries sg.
  Proof.
    intros sg D s log log' sg' H. unfold ensure_elim in H.
    destruct (sig_elim sg D s) as [[T [|]]|]; [apply tret_ok in H; subst; now exists [] | | ].
    all: apply declare_elim_extends in H as (d & _ & E); now exists [EElim D s (elim_type d s) true].
  Qed.

  Theorem ensure_below_sound : forall sg D j log log' sg',
    ensure_below Sp fuel sg D j log = (log', Ok sg') ->
    sg' = sg \/
    exists d l sg3 sg4 sg5,
      sig_ind sg D = Some d /\ history_level_spec sg d j l /\
      (exists es, sig_entries sg3 = es ++ sig_entries sg) /\
      defined Sp sg3 (below_name D j) (below_type d j l) (below_body d l) sg4 /\
      defined Sp sg4 (build_name D j) (build_type d j) (build_body d j l) sg5 /\
      defined Sp sg5 (recbelow_name D j) (recbelow_type d j) (recbelow_body d j) sg'.
  Proof.
    intros sg D j log log' sg' H. unfold ensure_below in H.
    destruct (sig_def sg (recbelow_name D j)); [left; now apply tret_ok in H | right].
    tbind_in H d0 Hd.
    destruct (sig_ind sg D) as [d|] eqn:Ed; [ | discriminate Hd].
    apply tret_ok in Hd. subst d0.
    tbind_in H l Hl. apply history_level_ok in Hl.
    tbind_in H sg1 H1. apply ensure_unit_extends in H1 as [es1 E1].
    tbind_in H sg2 H2. apply ensure_elim_extends in H2 as [es2 E2].
    tbind_in H sg3 H3. apply ensure_elim_extends in H3 as [es3 E3].
    tbind_in H sg4 H4. apply define_sound in H4.
    tbind_in H sg5 H5. apply define_sound in H5.
    apply define_sound in H.
    exists d, l, sg3, sg4, sg5. split; [reflexivity | split; [exact Hl | split; [ | auto]]].
    exists (es3 ++ es2 ++ es1). now rewrite E3, E2, E1, !app_assoc.
  Qed.

  (** What the registration of a history adds, read off the theorem. *)
  Corollary ensure_below_extends : forall sg D j log log' sg',
    ensure_below Sp fuel sg D j log = (log', Ok sg') -> exists es, sig_entries sg' = es ++ sig_entries sg.
  Proof.
    intros sg D j log log' sg' H.
    destruct (ensure_below_sound _ _ _ _ _ _ H) as [-> | (d & l & sg3 & sg4 & sg5 & _ & _ & [es E3] & D4 & D5 & D6)];
      [now exists [] | ].
    destruct D4 as (_ & _ & _ & E4), D5 as (_ & _ & _ & E5), D6 as (_ & _ & _ & E6).
    eexists. rewrite E6, E5, E4, E3. now rewrite !app_comm_cons.
  Qed.
End Sound.
