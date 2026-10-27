(** * The history of results: [Below_D], [build_D], [recBelow_D]

    After "the Below way" of Sozeau's Equations (§3.1 of the 2010 paper),
    as a scheme of translation in the setting of Rocq: neither the
    mechanism of [Fixpoint] nor every compilation path of today's
    Equations.

    For [D Δ θ̄ : Type_i] and a motive [P θ̄ x : Type_j] the history lives
    in [Type_ℓ], [ℓ := max i j], since the domains of functional recursive
    fields have levels up to i.  On a constructor it is the tuple of the
    components of its recursive fields; a field [r : Πȳ:B̄. D Δ v̄] gives
    [Πȳ:B̄. (P v̄ (r ȳ) × Below_D P v̄ (r ȳ))]; the empty tuple is
    [Unit_ℓ], a single component is the component itself, and more are
    nested to the right.  For ℕ:

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

    The binders of a method are those of Elim.Generate: each field, a
    recursive one followed at once by its hypothesis.  The method of
    [Below_D] lies after the parameters and P, that of [build_D] after
    them and [step], and [transport_past] renames the fields of the
    description into its body. *)

From Stdlib Require Import List Arith.
From Stdlib Require String.
Import ListNotations.
Import (notations) String.StringSyntax.
Local Open Scope string_scope.
From DepTypes.Common Require Import Result Traced.
From DepTypes.PTS Require Import Syntax Spec Signature.
From IndTypes.Elim Require Import Decl Generate Declare.

Local Notation string := String.string.

(** ** Names and the level *)

Definition below_name (D : string) (j : nat) : string :=
  String.append "Below_" (String.append D (String.append "_" (show_nat j))).
Definition build_name (D : string) (j : nat) : string :=
  String.append "build_" (String.append D (String.append "_" (show_nat j))).
Definition recbelow_name (D : string) (j : nat) : string :=
  String.append "recBelow_" (String.append D (String.append "_" (show_nat j))).

(** The level of the history of D for a motive in [Type_j]. *)
Definition history_level (d : ind_desc) (j : nat) : nat := Nat.max (ind_level d) j.

(** ** The binders of a method *)

(** As [transport] of Elim.Generate, with [g] binders between the
    parameters and those of the method. *)
Definition transport_past (g : nat) (rbs : list nat) (b n : nat) : nat :=
  match nth_error rbs n with
  | Some bl => b - 1 - bl
  | None => n - length rbs + (b + g)
  end.

(** A recursive field among the binders of a method: the position of its
    binder, with its hypothesis right after it; the positions of the
    earlier fields, innermost first; its domains and indices. *)
Record rec_binder : Type := {
  rb_pos : nat;
  rb_before : list nat;
  rb_domains : list term;
  rb_indices : list term;
}.

(** The binders of a method from the fields [fs] on, after [b] binders
    with the earlier fields at [rbs]: the positions of all the fields, the
    number of binders, and the recursive fields. *)
Fixpoint method_binders (rbs : list nat) (b : nat) (fs : list field)
  : list nat * nat * list rec_binder :=
  match fs with
  | [] => (rbs, b, [])
  | FArg _ :: fs' => method_binders (b :: rbs) (S b) fs'
  | FRec Bs vs :: fs' =>
      let '(rbs', b', rs) := method_binders (b :: rbs) (S (S b)) fs' in
      (rbs', b', {| rb_pos := b; rb_before := rbs; rb_domains := Bs; rb_indices := vs |} :: rs)
  end.

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

(** ** The three constructions *)

Section Below.
  Variable d : ind_desc.
  Variable j : nat.

  Let D := ind_name d.
  Let p := length (ind_params d).
  Let q := length (ind_indices d).
  Let l := history_level d j.

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
    pis (ind_params d) (Pi (motive_type d j) (over_family 1 (Srt (Univ l)))).

  (** The component of a recursive field [r : Πȳ:B̄. D Δ v̄] with its
      hypothesis [ih], among [b] binders after the parameters and P:
      [Πȳ:B̄. P v̄ (r ȳ) × ih ȳ], where [ih ȳ] is the history of [r ȳ]. *)
  Definition component (b : nat) (rb : rec_binder) : term :=
    let m := length (rb_domains rb) in
    let r := transport_past 1 (rb_before rb) b in
    pis (rename_tele r (rb_domains rb))
      (times (apps (Var (b + m)) (map (rename (upn_ren m r)) (rb_indices rb) ++
                                  [apps (Var (b - 1 - rb_pos rb + m)) (vars 0 m)]))
             (apps (Var (b - 2 - rb_pos rb + m)) (vars 0 m))).

  Definition below_method (c : ctor_desc) : term :=
    let '(_, b, rs) := method_binders [] 0 (ctor_fields c) in
    lams b (tuple_type l (map (component b) rs)).

  (** [λΔ P. elim_D[ℓ+1] Δ (λθ̄ x. Type_ℓ) m̄]. *)
  Definition below_body : term :=
    lams p (Lam (apps (Const (Elim D (S l)))
      (vars 1 p ++ [lams (S q) (Srt (Univ l))] ++ map below_method (ind_ctors d)))).

  (** [step : Πθ̄. Πx:D Δ θ̄. Below_D Δ P θ̄ x → P θ̄ x], after P. *)
  Definition step_type : term :=
    over_family 1 (Pi (below_at (q + 2) (q + 1) 0) (motive_at (q + 2) 1)).

  (** [Π(Δ). ΠP. Πstep. Πθ̄. Πx:D Δ θ̄. P θ̄ x × Below_D Δ P θ̄ x]. *)
  Definition build_type : term :=
    pis (ind_params d) (Pi (motive_type d j) (Pi step_type
      (over_family 2 (times (motive_at (q + 2) 0) (below_at (q + 3) (q + 2) 0))))).

  (** [Π(Δ). ΠP. Πstep. Πθ̄. Πx:D Δ θ̄. P θ̄ x]. *)
  Definition recbelow_type : term :=
    pis (ind_params d) (Pi (motive_type d j) (Pi step_type (over_family 2 (motive_at (q + 2) 0)))).

  (** On [c Δ ā], with the tuple [h] of the hypotheses:
      [(step ū (c Δ ā) h, h)].  [step] lies right before the binders of
      the method. *)
  Definition build_method (c : ctor_desc) : term :=
    let '(rbs, b, rs) := method_binders [] 0 (ctor_fields c) in
    let h := tuple l (map (fun rb => Var (b - 2 - rb_pos rb)) rs) in
    let obj := apps (Const (Ctor D (ctor_name c)))
                 (vars (b + 2) p ++ map (fun bl => Var (b - 1 - bl)) (rev rbs)) in
    lams b (Pair (apps (Var b) (map (rename (transport_past 2 rbs b)) (ctor_indices c) ++ [obj; h])) h).

  (** [λΔ P step. elim_D[ℓ] Δ (λθ̄ x. P θ̄ x × Below_D Δ P θ̄ x) m̄]. *)
  Definition build_body : term :=
    lams p (Lam (Lam (apps (Const (Elim D l))
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

  (** [Below_D], [build_D] and [recBelow_D] for motives in [Type_j], with
      what they need: [Unit_ℓ], [elim_D[ℓ+1]] and [elim_D[ℓ]]; unless
      they are registered already.  Each is a δ-constant checked in the
      signature without it. *)
  Definition ensure_below (sg : signature) (D : string) (j : nat) : R signature :=
    match sig_def sg (recbelow_name D j) with
    | Some _ => tret sg
    | None =>
        let! d := match sig_ind sg D with Some d => tret d | None => refuse (RUndeclared D) end in
        let l := history_level d j in
        let! sg1 := ensure_unit Sp fuel sg l in
        let! sg2 := ensure_elim Sp fuel sg1 D (S l) in
        let! sg3 := ensure_elim Sp fuel sg2 D l in
        let! sg4 := define Sp fuel sg3 (below_name D j) (below_type d j) (below_body d j) in
        let! sg5 := define Sp fuel sg4 (build_name D j) (build_type d j) (build_body d j) in
        define Sp fuel sg5 (recbelow_name D j) (recbelow_type d j) (recbelow_body d j)
    end.
End Register.

(** ** What a registration of the history guarantees

    Over [Unit_ℓ] and the two instances, which their own registrations
    guarantee (Elim.Declare), the three constructions are δ-constants,
    each with a type that is a type and a body checked against it in the
    signature before it, in the judgments of the annotated kernel. *)

From DepTypes.PTS Require Import Bidir.

Section Sound.
  Variable Sp : spec.
  Variable fuel : nat.

  (** [sg'] is [sg] with the δ-constant [f : A := b], checked in [sg]. *)
  Definition defined (sg : signature) (f : string) (A b : term) (sg' : signature) : Prop :=
    sig_def sg f = None /\ (exists s, is_type_of Sp sg [] A s) /\ chk Sp sg [] b A /\
    sig_entries sg' = EDef f A b :: sig_entries sg.

  Lemma ensure_unit_extends : forall sg l log log' sg',
    ensure_unit Sp fuel sg l log = (log', Ok sg') -> exists es, sig_entries sg' = es ++ sig_entries sg.
  Proof.
    intros sg l log log' sg' H. unfold ensure_unit in H.
    destruct l as [|l]; [apply tret_ok in H; subst; now exists [] | ].
    destruct (sig_ind sg (unit_name (S l))); [apply tret_ok in H; subst; now exists [] | ].
    tbind_in H r Hr. apply tret_ok in H. subst sg'. destruct r as [sg1 d].
    apply declare_ind_sound in Hr as (_ & _ & E & _). now exists [EInd d].
  Qed.

  Lemma ensure_elim_extends : forall sg D j log log' sg',
    ensure_elim Sp fuel sg D j log = (log', Ok sg') -> exists es, sig_entries sg' = es ++ sig_entries sg.
  Proof.
    intros sg D j log log' sg' H. unfold ensure_elim in H.
    destruct (sig_elim sg D j) as [[T [|]]|]; [apply tret_ok in H; subst; now exists [] | | ].
    all: apply declare_elim_sound in H as (d & _ & _ & _ & _ & E); now exists [EElim D j (elim_type d j) true].
  Qed.

  Theorem ensure_below_sound : forall sg D j log log' sg',
    ensure_below Sp fuel sg D j log = (log', Ok sg') ->
    sg' = sg \/
    exists d sg3 sg4 sg5,
      sig_ind sg D = Some d /\ (exists es, sig_entries sg3 = es ++ sig_entries sg) /\
      defined sg3 (below_name D j) (below_type d j) (below_body d j) sg4 /\
      defined sg4 (build_name D j) (build_type d j) (build_body d j) sg5 /\
      defined sg5 (recbelow_name D j) (recbelow_type d j) (recbelow_body d j) sg'.
  Proof.
    intros sg D j log log' sg' H. unfold ensure_below in H.
    destruct (sig_def sg (recbelow_name D j)); [left; now apply tret_ok in H | right].
    tbind_in H d0 Hd.
    destruct (sig_ind sg D) as [d|] eqn:Ed; [ | discriminate Hd].
    apply tret_ok in Hd. subst d0.
    tbind_in H sg1 H1. apply ensure_unit_extends in H1 as [es1 E1].
    tbind_in H sg2 H2. apply ensure_elim_extends in H2 as [es2 E2].
    tbind_in H sg3 H3. apply ensure_elim_extends in H3 as [es3 E3].
    tbind_in H sg4 H4. apply define_sound in H4.
    tbind_in H sg5 H5. apply define_sound in H5.
    apply define_sound in H.
    exists d, sg3, sg4, sg5. split; [reflexivity | split; [ | auto]].
    exists (es3 ++ es2 ++ es1). now rewrite E3, E2, E1, !app_assoc.
  Qed.
End Sound.
