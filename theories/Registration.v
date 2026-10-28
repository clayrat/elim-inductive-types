(** * The registration monad

    Both algorithms register their entries through the kernel's checker:
    algorithm 1 its declarations and instances of eliminators
    (Elim.Declare), algorithm 2 the history and the compiled functions
    with their defining equations (Recursion); both register δ-constants
    through [define], which is here.  A registration
    is a computation in [R]: every run of the checker goes to its log with
    the stage it belongs to, and its answer becomes the value, the refusal
    or the lack of fuel of the stage.  The stages and refusals are those
    of Diagnostics, exported with this module; it lies below both
    algorithms and depends on neither. *)

From Stdlib Require Import List.
From Stdlib Require String.
Import ListNotations.
From DepTypes.Common Require Import Result Traced.
From DepTypes.PTS Require Import Syntax Spec Signature Eval Check.
From IndTypes Require Export Diagnostics.

Local Notation string := String.string.

Definition R (A : Type) : Type := traced (stage * list event) reg_failure A.

Definition refuse {A} (e : reg_error) : R A := tfail (Refuse e).

Definition run_registration (m : R signature) : list (stage * list event) * registration :=
  let (log, r) := run_traced m in
  (log, match r with
        | Ok sg => Registered sg
        | Err (Refuse e) => Refused e
        | Err (NoFuelAt st t) => OutOfFuelAt st t
        end).

Definition add (sg : signature) (e : entry) : R signature :=
  match sig_add sg e with
  | Some sg' => tret sg'
  | None => refuse ROpen
  end.

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

Section Checks.
  Variable Sp : spec.
  Variable fuel : nat.

  (** [A] is a type in the context [G]: its type unfolds to a sort. *)
  Definition sort_of (sg : signature) (st : stage) (G : ctx) (A : term) : R sort :=
    let! T := checked st (run_infer Sp sg fuel G A) in
    match whnf sg fuel T with
    | HeadForm (Srt s) => tret s
    | HeadForm T' => refuse (RNotAType st T')
    | HeadOutOfFuel _ => tfail (NoFuelAt st A)
    end.

  (** ** δ-constants *)

  (** A δ-constant is registered once its name is free, its type is a
      type and its body checks against it in the signature where the
      constant itself is not yet, so a body refers only to constants
      registered before it. *)
  Definition define (sg : signature) (f : string) (A b : term) : R signature :=
    let! _ := match sig_def sg f with Some _ => refuse (RTaken (Def f)) | None => tret tt end in
    let! _ := sort_of sg (AtDefType f) [] A in
    let! _ := checked (AtDefBody f) (run_check Sp sg fuel [] b A) in
    add sg (EDef f A b).
End Checks.

Definition define_checked (S : spec) (fuel : nat) (sg : signature) (f : string) (A b : term)
  : list (stage * list event) * registration :=
  run_registration (define S fuel sg f A b).

(** ** Answers *)

Definition registered (r : list (stage * list event) * registration) : option signature :=
  match snd r with Registered sg => Some sg | _ => None end.

Definition refusal (r : list (stage * list event) * registration) : option reg_error :=
  match snd r with Refused e => Some e | _ => None end.

(** ** What the checks guarantee

    A check that passes carries the judgment of the annotated kernel
    PTS.Bidir, by the soundness of the kernel's checker (PTS.CheckSound);
    an entry that is added extends the signature by exactly itself
    ([sig_add_entries] of PTS.Signature).  A δ-constant that is
    registered is [defined].  Successful runs are split with [tbind_in]
    and [titer_Forall] of Common.Traced. *)

From Stdlib Require Import Relations.
From DepTypes.PTS Require Import Reduction NormalOrder Bidir CheckSound.

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

  (** [sg'] is [sg] with the δ-constant [f : A := b], checked in [sg]. *)
  Definition defined (sg : signature) (f : string) (A b : term) (sg' : signature) : Prop :=
    sig_def sg f = None /\ (exists s, is_type_of sg [] A s) /\ chk Sp sg [] b A /\
    sig_entries sg' = EDef f A b :: sig_entries sg.

  Theorem define_sound : forall sg f A b log log' sg',
    define Sp fuel sg f A b log = (log', Ok sg') -> defined sg f A b sg'.
  Proof.
    intros sg f A b log log' sg' H. unfold define in H. unfold defined.
    tbind_in H v Hf.
    destruct (sig_def sg f) eqn:Ef; [discriminate Hf | ].
    tbind_in H s Hs. apply sort_of_ok in Hs as [_ Hs].
    tbind_in H u Hb. apply checked_ok in Hb. apply add_ok in H.
    destruct (run_check_sound _ _ _ _ _ _ _ Hb) as (_ & _ & Hchk).
    repeat split; [now exists s | exact Hchk | exact H].
  Qed.
End Sound.
