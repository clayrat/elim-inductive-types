(** * [declare_checked]: registering a declaration and its eliminators

    The checked entry point of algorithm 1, as [translate_checked] in
    lecture 6.  A raw declaration is classified (Elim.Decl) and
    registered with its constructors once
    - the name D is free in the signature;
    - the type of D and the type of every constructor, rebuilt from the
      description, are types in the signature extended by D;
    - every field has a level at most i, the level of D: otherwise a type
      in [Type₀] could have a field in [Type₀] itself, and Type-in-Type
      would come back.
    An instance [elim_D[j]] of its eliminator is then registered in
    stages:
    1. check the generated type of [elim_D[j]] in the signature with D and
       its constructors;
    2. add [elim_D[j]] with that type, without the flag of active
       ι-rules, to a temporary copy of the signature;
    3. there, check both sides of every generated ι-rule against
       [P ū (c_k Δ ā)] in the context of the parameters, motive, methods
       and fields: the eliminator is already a typed constant, but its
       unchecked rules take no part in evaluation and conversion;
    4. only when every check succeeds, register the instance in the main
       signature with the flag; on a rejection or running out of fuel the
       temporary extension is dropped.
    A δ-constant is registered once its type is a type and its body checks
    against it in the signature where the constant itself is not yet, so
    a body refers only to constants registered before it.

    These checks are the local form of [signature_typed] of the kernel's
    PTS.Typing: the types of constants are types, δ-bodies have them, and
    each ι-rule keeps the type of its redex.  The checker itself never
    creates entries: a constant missing from the signature it is given is
    rejected.  Each instance is checked this way when it is generated;
    the general theorem for all descriptions and levels is an obligation
    (Contracts.v).

    [Unit_0] is the primitive Unit; for ℓ > 0, [data Unit_ℓ : Type_ℓ where
    tt_ℓ : Unit_ℓ] is declared by algorithm 1, its result exactly
    [Type_ℓ]: without cumulativity [Unit : Type₀] cannot stand for it.

    Every run of the checker is logged with the stage it belongs to.  The
    compiler of algorithm 2 (Recursion.Compile) registers in the same way
    and logs in the same terms: the sorts of its motives, its δ-constants
    and its defining equations.  The diagnostics of both algorithms are in
    Diagnostics, which depends on neither. *)

From Stdlib Require Import List Bool Arith.
From Stdlib Require String.
From Stdlib Require Import DecimalString.
Import ListNotations.
Import (notations) String.StringSyntax.
Local Open Scope string_scope.
From DepTypes.Common Require Import Result Traced.
From DepTypes.PTS Require Import Syntax Spec Signature Eval Check.
From IndTypes.Elim Require Import Decl Generate.
From IndTypes Require Export Diagnostics.

Local Notation string := String.string.

(** ** The registration monad

    The stages, refusals and answers are those of Diagnostics, exported
    with this module. *)

Definition R (A : Type) : Type := traced (stage * list event) reg_failure A.

Definition refuse {A} (e : reg_error) : R A := tfail (Refuse e).

Definition run_registration (m : R signature) : list (stage * list event) * registration :=
  let (log, r) := run_traced m in
  (log, match r with
        | Ok sg => Registered sg
        | Err (Refuse e) => Refused e
        | Err (NoFuelAt st t) => OutOfFuelAt st t
        end).

Fixpoint titer {A} (f : A -> R unit) (l : list A) : R unit :=
  match l with
  | [] => tret tt
  | a :: l' => let! _ := f a in titer f l'
  end.

Fixpoint tfold {A} (f : signature -> A -> R signature) (sg : signature) (l : list A) : R signature :=
  match l with
  | [] => tret sg
  | a :: l' => let! sg' := f sg a in tfold f sg' l'
  end.

Definition add (sg : signature) (e : entry) : R signature :=
  match sig_add sg e with
  | Some sg' => tret sg'
  | None => refuse ROpen
  end.

(** ** Checks *)

Section Register.
  Variable Sp : spec.
  Variable fuel : nat.

  (** A run of the checker at a stage: its events go to the log, and its
      answer becomes the value, the refusal or the lack of fuel of the
      stage. *)
  Definition checked {A} (st : stage) (run : list event * answer A) : R A :=
    let! _ := temit (st, fst run) in
    match snd run with
    | Accepted a => tret a
    | Rejected e => refuse (RRejected st e)
    | Undecided t => tfail (NoFuelAt st t)
    end.

  (** [A] is a type in the context [G]: its type unfolds to a sort. *)
  Definition sort_of (sg : signature) (st : stage) (G : ctx) (A : term) : R sort :=
    let! T := checked st (run_infer Sp sg fuel G A) in
    match whnf sg fuel T with
    | HeadForm (Srt s) => tret s
    | HeadForm T' => refuse (RNotAType st T')
    | HeadOutOfFuel _ => tfail (NoFuelAt st A)
    end.

  Definition within (s : sort) (i : nat) : bool :=
    match s with
    | Univ k => Nat.leb k i
    | _ => false
    end.

  (** The fields of the constructor [c] of [d] from position [l] on, in
      the context [G] of the parameters and the earlier fields: each is a
      type of level at most that of D. *)
  Fixpoint check_fields (sg : signature) (d : ind_desc) (c : string) (G : ctx) (l : nat)
      (fs : list field) : R unit :=
    match fs with
    | [] => tret tt
    | fd :: fs' =>
        let A := field_type (ind_name d) (length (ind_params d)) l fd in
        let! s := sort_of sg (AtField (ind_name d) c l) G A in
        let! _ := trequire (within s (ind_level d)) (Refuse (RLevel c l s (ind_level d))) in
        check_fields sg d c (A :: G) (S l) fs'
    end.

  (** ** Registration *)

  (** The declaration with its constructors; [bypass] is the
      demonstration mode of Elim.Decl, outside the contract. *)
  Definition declare_ind_with (bypass : bool) (sg : signature) (raw : raw_decl)
    : R (signature * ind_desc) :=
    let D := rd_name raw in
    let! d := match classify_decl_with bypass raw with Ok d => tret d | Err e => refuse (RClassify e) end in
    let! _ := match sig_ind sg D with Some _ => refuse (RTaken (Ind D)) | None => tret tt end in
    let! sg1 := add sg (EInd d) in
    let! _ := sort_of sg1 (AtIndType D) [] (ind_type d) in
    let! _ := titer (fun c =>
                let! _ := sort_of sg1 (AtCtorType D (ctor_name c)) [] (ctor_type d c) in
                check_fields sg1 d (ctor_name c) (rev (ind_params d)) 0 (ctor_fields c))
              (ind_ctors d) in
    tret (sg1, d).

  Definition declare_ind : signature -> raw_decl -> R (signature * ind_desc) := declare_ind_with false.

  (** Both sides of a rule against its type, in its context. *)
  Definition check_rule (sg : signature) (D : string) (j : nat) (r : iota_rule) : R unit :=
    let! _ := checked (AtRuleLhs D j (rule_ctor r))
                (run_check Sp sg fuel (rule_ctx r) (rule_lhs r) (rule_type r)) in
    checked (AtRuleRhs D j (rule_ctor r)) (run_check Sp sg fuel (rule_ctx r) (rule_rhs r) (rule_type r)).

  (** The instance [elim_D[j]], in the four stages. *)
  Definition declare_elim (sg : signature) (D : string) (j : nat) : R signature :=
    let! d := match sig_ind sg D with Some d => tret d | None => refuse (RUndeclared D) end in
    let! _ := match sig_elim sg D j with Some _ => refuse (RTaken (Elim D j)) | None => tret tt end in
    let T := elim_type d j in
    let! _ := sort_of sg (AtElimType D j) [] T in
    let! tmp := add sg (EElim D j T false) in
    let! _ := titer (check_rule tmp D j) (iota_rules d j) in
    add sg (EElim D j T true).

  (** The declaration and the instances at the given levels. *)
  Definition declare_with (bypass : bool) (sg : signature) (raw : raw_decl) (levels : list nat)
    : R signature :=
    let! r := declare_ind_with bypass sg raw in
    tfold (fun sg j => declare_elim sg (rd_name raw) j) (fst r) levels.

  Definition declare : signature -> raw_decl -> list nat -> R signature := declare_with false.

  (** The instance, unless it is registered already. *)
  Definition ensure_elim (sg : signature) (D : string) (j : nat) : R signature :=
    match sig_elim sg D j with
    | Some (_, true) => tret sg
    | _ => declare_elim sg D j
    end.

  (** A δ-constant, checked in the signature without it. *)
  Definition define (sg : signature) (f : string) (A b : term) : R signature :=
    let! _ := match sig_def sg f with Some _ => refuse (RTaken (Def f)) | None => tret tt end in
    let! _ := sort_of sg (AtDefType f) [] A in
    let! _ := checked (AtDefBody f) (run_check Sp sg fuel [] b A) in
    add sg (EDef f A b).

  (** ** [Unit_ℓ] *)

  Definition show_nat (n : nat) : string := NilZero.string_of_uint (Nat.to_uint n).

  Definition unit_name (l : nat) : string := String.append "Unit_" (show_nat l).
  Definition tt_name (l : nat) : string := String.append "tt_" (show_nat l).

  Definition unit_decl (l : nat) : raw_decl := {|
    rd_name := unit_name l; rd_params := []; rd_indices := []; rd_level := l;
    rd_ctors := [mk_raw_ctor (tt_name l) (Const (Ind (unit_name l)))] |}.

  (** The one-element type at level ℓ and its element. *)
  Definition unit_at (l : nat) : term :=
    match l with 0 => Unit | _ => Const (Ind (unit_name l)) end.
  Definition tt_at (l : nat) : term :=
    match l with 0 => Tt | _ => Const (Ctor (unit_name l) (tt_name l)) end.

  (** [Unit_ℓ], unless it is the primitive one or registered already. *)
  Definition ensure_unit (sg : signature) (l : nat) : R signature :=
    match l with
    | 0 => tret sg
    | _ =>
        match sig_ind sg (unit_name l) with
        | Some _ => tret sg
        | None => let! r := declare_ind sg (unit_decl l) in tret (fst r)
        end
    end.
End Register.

(** ** Entry points *)

Definition registered (r : list (stage * list event) * registration) : option signature :=
  match snd r with Registered sg => Some sg | _ => None end.

Definition refusal (r : list (stage * list event) * registration) : option reg_error :=
  match snd r with Refused e => Some e | _ => None end.

Definition declare_checked (S : spec) (fuel : nat) (sg : signature) (raw : raw_decl) (levels : list nat)
  : list (stage * list event) * registration :=
  run_registration (declare S fuel sg raw levels).

(** The demonstration mode: strict positivity is not checked, the rest is. *)
Definition declare_bypassing (S : spec) (fuel : nat) (sg : signature) (raw : raw_decl) (levels : list nat)
  : list (stage * list event) * registration :=
  run_registration (declare_with S fuel true sg raw levels).

Definition define_checked (S : spec) (fuel : nat) (sg : signature) (f : string) (A b : term)
  : list (stage * list event) * registration :=
  run_registration (define S fuel sg f A b).

(** ** What a registration guarantees

    Whatever a registration returns has passed its checks, so by the
    soundness of the kernel's checker (PTS.CheckSound) it carries the
    judgments of the annotated kernel PTS.Bidir: the types of the new
    constants are types, every field has a level at most that of D, both
    sides of every ι-rule check against its type in the signature where the
    instance has no active rules, and a δ-body checks against its type in
    the signature without it.  The resulting signature is the old one with
    the new entries. *)

From Stdlib Require Import Relations.
From DepTypes.PTS Require Import Reduction NormalOrder Bidir CheckSound.

Lemma sig_add_entries : forall sg e sg', sig_add sg e = Some sg' -> sig_entries sg' = e :: sig_entries sg.
Proof.
  intros sg e sg' H. unfold sig_add in H.
  revert H. generalize (@eq_refl bool (entry_closed e)).
  generalize (entry_closed e) at 2 3. intros b Hb.
  destruct b; intros H; [injection H as <-; reflexivity | discriminate H].
Qed.

(** Splits a successful [let!] in [H] into the step that gives [x], as
    [Hx], and the rest, still [H]; the intermediate log stays anonymous.
    The counterpart of [bind_in] of Common.Result. *)
Ltac tbind_in H x Hx := apply tbind_ok in H as (? & x & Hx & H); cbv beta in H.

Section Sound.
  Variable Sp : spec.
  Variable fuel : nat.

  (** [A] is a type of the annotated kernel, of sort [s]. *)
  Definition is_type_of (sg : signature) (G : ctx) (A : term) (s : sort) : Prop :=
    exists T, synth Sp sg G A T /\ red sg T (Srt s).

  Lemma add_ok : forall sg e log log' sg',
    add sg e log = (log', Ok sg') -> sig_entries sg' = e :: sig_entries sg.
  Proof.
    intros sg e log log' sg' H. unfold add in H.
    destruct (sig_add sg e) as [s|] eqn:E; [ | discriminate H].
    apply tret_ok in H. subst. now apply sig_add_entries.
  Qed.

  Lemma checked_ok : forall {A} st (run : list event * answer A) log log' a,
    checked st run log = (log', Ok a) -> snd run = Accepted a.
  Proof.
    intros A st run log log' a H. unfold checked in H.
    tbind_in H u Hu.
    destruct (snd run) as [b| |]; [apply tret_ok in H; now subst | discriminate H | discriminate H].
  Qed.

  Lemma sort_of_ok : forall sg st G A log log' s,
    sort_of Sp fuel sg st G A log = (log', Ok s) -> bwf_ctx Sp sg G /\ is_type_of sg G A s.
  Proof.
    intros sg st G A log log' s H. unfold sort_of in H.
    tbind_in H T E. apply checked_ok in E.
    destruct (whnf sg fuel T) as [V|] eqn:W; [ | discriminate H].
    destruct V; try discriminate H. apply tret_ok in H. subst.
    apply run_infer_sound in E as [Hc Hs]. split; [exact Hc | ].
    exists T. split; [exact Hs | apply nsteps_red, (whnf_reduces fuel), W].
  Qed.

  Lemma titer_Forall : forall {A} (f : A -> R unit) l log log' u,
    titer f l log = (log', Ok u) -> Forall (fun a => exists log1 log2 v, f a log1 = (log2, Ok v)) l.
  Proof.
    intros A f l. induction l as [|a l IH]; intros log log' u H; [constructor | ].
    cbn in H. apply tbind_ok in H as (log1 & v & Ha & H).
    constructor; [now exists log, log1, v | eapply IH; exact H].
  Qed.

  (** ** Declarations *)

  (** Every field is a type of level at most that of D, in the context of
      the parameters and the earlier fields. *)
  Fixpoint fields_typed (sg : signature) (d : ind_desc) (G : ctx) (l : nat) (fs : list field) : Prop :=
    match fs with
    | [] => True
    | fd :: fs' =>
        let A := field_type (ind_name d) (length (ind_params d)) l fd in
        (exists s, is_type_of sg G A s /\ within s (ind_level d) = true) /\
        fields_typed sg d (A :: G) (S l) fs'
    end.

  Lemma check_fields_ok : forall sg d c fs G l log log' u,
    check_fields Sp fuel sg d c G l fs log = (log', Ok u) -> fields_typed sg d G l fs.
  Proof.
    intros sg d c fs. induction fs as [|fd fs IH]; intros G l log log' u H; [exact I | ].
    cbn [check_fields] in H. cbn [fields_typed].
    tbind_in H s Hs. apply sort_of_ok in Hs as [_ Hs].
    tbind_in H v Hw.
    split; [ | eapply IH; exact H].
    exists s. split; [exact Hs | ].
    destruct (within s (ind_level d)); [reflexivity | discriminate Hw].
  Qed.

  Theorem declare_ind_sound : forall bypass sg raw log log' sg' d,
    declare_ind_with Sp fuel bypass sg raw log = (log', Ok (sg', d)) ->
    classify_decl_with bypass raw = Ok d /\ sig_ind sg (rd_name raw) = None /\
    sig_entries sg' = EInd d :: sig_entries sg /\
    (exists s, is_type_of sg' [] (ind_type d) s) /\
    Forall (fun c => (exists s, is_type_of sg' [] (ctor_type d c) s) /\
                     fields_typed sg' d (rev (ind_params d)) 0 (ctor_fields c)) (ind_ctors d).
  Proof.
    intros bypass sg raw log log' sg' d H. unfold declare_ind_with in H.
    tbind_in H d0 Hd.
    destruct (classify_decl_with bypass raw) as [d1|e] eqn:Ec; [ | discriminate Hd].
    apply tret_ok in Hd. subst d0.
    tbind_in H v Hf.
    destruct (sig_ind sg (rd_name raw)) eqn:Ef; [discriminate Hf | ].
    tbind_in H sg1 Ha. apply add_ok in Ha.
    tbind_in H s Hs. apply sort_of_ok in Hs as [_ Hs].
    tbind_in H w Hcs. apply tret_ok in H.
    injection H as <- <-.
    repeat split; [exact Ha | now exists s | ].
    apply titer_Forall in Hcs. eapply Forall_impl; [ | exact Hcs].
    intros c (l1 & l2 & u & Hc). tbind_in Hc s' Hs'.
    apply sort_of_ok in Hs' as [_ Hs']. split; [now exists s' | eapply check_fields_ok; exact Hc].
  Qed.

  (** ** Instances *)

  Theorem declare_elim_sound : forall sg D j log log' sg',
    declare_elim Sp fuel sg D j log = (log', Ok sg') ->
    exists d,
      sig_ind sg D = Some d /\ sig_elim sg D j = None /\
      (exists s, is_type_of sg [] (elim_type d j) s) /\
      (exists tmp,
         sig_entries tmp = EElim D j (elim_type d j) false :: sig_entries sg /\
         forall r, In r (iota_rules d j) ->
           bwf_ctx Sp tmp (rule_ctx r) /\ btype Sp tmp (rule_ctx r) (rule_type r) /\
           chk Sp tmp (rule_ctx r) (rule_lhs r) (rule_type r) /\
           chk Sp tmp (rule_ctx r) (rule_rhs r) (rule_type r)) /\
      sig_entries sg' = EElim D j (elim_type d j) true :: sig_entries sg.
  Proof.
    intros sg D j log log' sg' H. unfold declare_elim in H.
    tbind_in H d Hd.
    destruct (sig_ind sg D) as [d0|] eqn:Ed; [ | discriminate Hd].
    apply tret_ok in Hd. subst d0. exists d.
    tbind_in H v Hf.
    destruct (sig_elim sg D j) eqn:Ef; [discriminate Hf | ].
    tbind_in H s Hs. apply sort_of_ok in Hs as [_ Hs].
    tbind_in H tmp Ht. apply add_ok in Ht.
    tbind_in H w Hr. apply add_ok in H.
    split; [reflexivity | split; [reflexivity | split; [now exists s | split; [ | exact H]]]].
    exists tmp. split; [exact Ht | ]. intros r Hin.
    apply titer_Forall in Hr. rewrite Forall_forall in Hr.
    destruct (Hr r Hin) as (l1 & l2 & u & Hc). unfold check_rule in Hc.
    tbind_in Hc u1 H1.
    apply checked_ok in H1. apply checked_ok in Hc.
    destruct (run_check_sound _ _ _ _ _ _ _ H1) as (Hctx & Hty & Hl).
    destruct (run_check_sound _ _ _ _ _ _ _ Hc) as (_ & _ & Hrhs).
    repeat split; assumption.
  Qed.

  (** ** δ-constants *)

  Theorem define_sound : forall sg f A b log log' sg',
    define Sp fuel sg f A b log = (log', Ok sg') ->
    sig_def sg f = None /\ (exists s, is_type_of sg [] A s) /\ chk Sp sg [] b A /\
    sig_entries sg' = EDef f A b :: sig_entries sg.
  Proof.
    intros sg f A b log log' sg' H. unfold define in H.
    tbind_in H v Hf.
    destruct (sig_def sg f) eqn:Ef; [discriminate Hf | ].
    tbind_in H s Hs. apply sort_of_ok in Hs as [_ Hs].
    tbind_in H u Hb. apply checked_ok in Hb. apply add_ok in H.
    destruct (run_check_sound _ _ _ _ _ _ _ Hb) as (_ & _ & Hchk).
    repeat split; [now exists s | exact Hchk | exact H].
  Qed.
End Sound.
