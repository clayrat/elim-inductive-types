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
    in the sense of the annotated kernel: declarations, with the sorts of
    their fields and the category of elimination these give, instances
    of eliminators into the sorts the category allows, with their
    ι-rules, δ-constants, and, for algorithm 2,
    the history [Below_D], [build_D], [recBelow_D] and every compiled
    function: a δ-constant checked against its declared type without
    itself, its defining equations holding by conversion.

    These are checked on every output, through [declare_checked] and
    [compile_checked], as [translate_checked] checks the outputs of the
    translator in lecture 6.  The annotated judgments become declarative
    ones by the kernel's soundness of the checker (its CheckSound, extended
    to Σ, δ-constants and the ι-rules of the signature), over a
    type-correct signature ([signature_typed] of PTS.Typing: a signature
    itself guarantees only closedness).

    Declarative typing does not give acceptance by the checker: the
    declarative rules type the unannotated redex [(λx. x) zero], which
    the checker refuses whatever the fuel, and the kernel states the
    completeness of its checker for the annotated kernel of PTS.Bidir.
    So every obligation that a registration succeeds with enough fuel
    rests on typing in the annotated kernel, stated alongside the
    declarative one.

    Open for algorithm 1, stated below: the classification is complete
    for the grammar; for every accepted declaration and every sort of the
    table the generated instance is typed and its ι-rules keep types,
    declaratively and in the annotated kernel; its registration succeeds
    with enough fuel when the category allows the sort; and the
    signatures that registrations build, compilations included, are
    type-correct, normalizing and consistent.  The obligations are stated
    for the predicative hierarchy with Prop, [predicative_prop], which
    contains the one without it: the declarations of lecture 7 are among
    its declarations.

    Open for algorithm 2, stated below: for every declaration and level
    the history is typed, declaratively and in the annotated kernel, and
    its registration succeeds with enough fuel; for every case tree the
    translation accepts, the compiled body has the declared type when the
    right sides have their goals whatever the body of the function, and
    checks against it when they check against them; the defining
    equations hold by definition whatever the right sides; the checks of
    the compilation pass with enough fuel when the right sides check; and
    compiled functions are total.

    Trusted beyond the Rocq kernel, as in lecture 6: the
    extraction to OCaml, the printer and the demos; the native reference
    in reference/ is covered only by differential tests. *)

From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Spec Signature Typing Bidir.
From DepTypes.Configs Require Import Predicative.
From IndTypes.Elim Require Import Decl Generate Declare.
From IndTypes.Recursion Require Import Below CaseTree Compile.
From DepTypes.PTS Require Import Reduction NormalOrder Eval.
From Stdlib Require Import List Relations.
From Stdlib Require String.
Import ListNotations.

Local Notation string := String.string.

(** The table of the obligations, the predicative hierarchy with Prop. *)
Local Notation Sp := predicative_prop.

(** ** Classification (algorithm 1) *)

(** The types of D and of its constructors rebuilt from the classified
    description are the declared ones, also in the bypass mode. *)
Definition classification_faithful : Prop :=
  forall mode d desc, classify_decl_with mode d = Ok desc ->
  ind_name desc = rd_name d /\
  ind_type desc = pis (rd_params d ++ rd_indices d) (Srt (rd_sort d)) /\
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
    exactly its entry.  In the signature where it was checked, with D at
    the category of its sort, the types of D and of its constructors are
    types of the annotated kernel, and every field has a sort allowed in
    D; the entry registered has the category of these sorts. *)
Definition declaration_sound : Prop :=
  forall S fuel mode sg raw log log' sg' d,
  declare_ind_with S fuel mode sg raw log = (log', Ok (sg', d)) ->
  exists d0 sg1 fss,
    classify_decl_with mode raw = Ok d0 /\ sig_ind sg (rd_name raw) = None /\
    sig_entries sg1 = EInd d0 :: sig_entries sg /\
    (exists s, is_type_of S sg1 [] (ind_type d0) s) /\
    Forall2 (fun c ss => (exists s, is_type_of S sg1 [] (ctor_type d0 c) s) /\
                         fields_typed S sg1 d0 (rev (ind_params d0)) 0 (ctor_fields c) ss)
      (ind_ctors d0) fss /\
    d = with_elim d0 (elim_class_of (ind_sort d0) fss) /\
    sig_entries sg' = EInd d :: sig_entries sg.

Theorem declaration_sound_holds : declaration_sound.
Proof. intros S fuel. apply declare_ind_sound. Qed.

(** A registered instance eliminates into a sort the category of D
    allows and has a type that is a type; both sides of every generated
    ι-rule check against its type, in its well-formed context, in the
    signature where the instance has no active rules; and only then is
    the instance added, with active rules. *)
Definition instance_sound : Prop :=
  forall S fuel sg D s log log' sg',
  declare_elim S fuel sg D s log = (log', Ok sg') ->
  exists d,
    sig_ind sg D = Some d /\ sig_elim sg D s = None /\
    allows_elimination S (ind_elim d) s = true /\
    (exists s', is_type_of S sg [] (elim_type d s) s') /\
    (exists tmp,
       sig_entries tmp = EElim D s (elim_type d s) false :: sig_entries sg /\
       forall r, In r (iota_rules d s) ->
         bwf_ctx S tmp (rule_ctx r) /\ btype S tmp (rule_ctx r) (rule_type r) /\
         chk S tmp (rule_ctx r) (rule_lhs r) (rule_type r) /\
         chk S tmp (rule_ctx r) (rule_rhs r) (rule_type r)) /\
    sig_entries sg' = EElim D s (elim_type d s) true :: sig_entries sg.

Theorem instance_sound_holds : instance_sound.
Proof. intros S fuel. apply declare_elim_sound. Qed.

(** ** δ-constants (both algorithms) *)

(** A registered δ-constant is [defined] (Registration): its name was
    free, its type is a type, and its body checks against it in the
    signature without the constant. *)
Definition definition_sound : Prop :=
  forall S fuel sg f A b log log' sg',
  define S fuel sg f A b log = (log', Ok sg') -> defined S sg f A b sg'.

Theorem definition_sound_holds : definition_sound.
Proof. intros S fuel. apply define_sound. Qed.

(** ** Open obligations of algorithm 1

    Stated, not proved.  Every registration checks its own output (the
    contracts above); these are the general theorems behind those checks,
    for all declarations, sorts and signatures built by registrations,
    and the metatheory the kernel's declarative obligations need from
    them.  The bypass modes are outside: without positivity, signatures
    pass every check, yet [δ (mk δ) : Void] holds there
    (Data.Positivity), so they are neither normalizing nor consistent;
    without the check of the sorts of elimination, a proof decides data
    (Data.Logic), which the erasure of proofs could not keep. *)

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
  rd_sort := ind_sort d;
  rd_ctors := map (fun c =>
    mk_raw_ctor (ctor_name c)
      (pis (field_types (ind_name d) (length (ind_params d)) 0 (ctor_fields c))
           (apps (Const (Ind (ind_name d)))
                 (vars (length (ctor_fields c)) (length (ind_params d)) ++ ctor_indices c))))
    (ind_ctors d) |}.

(** Classification gives D the category of its sort, which the
    registration refines. *)
Definition classification_complete : Prop :=
  forall d, desc_well_formed d -> classify_decl (raw_of d) = Ok (with_elim d (sort_class (ind_sort d))).

(** The general theorem behind the checks of [declare_elim], for every
    accepted declaration and every sort [s] of the table, allowed by the
    category of D or not: in the signature with D and the instance
    without active rules, the type of the instance is a type, every
    context of a rule is well formed, and both sides of every generated
    ι-rule have its type, in the declarative rules.  The category
    restricts elimination for erasure, not for typing. *)
Definition generated_instances_typed : Prop :=
  forall fuel sg raw log log' sg' d s tmp,
  signature_typed Sp sg ->
  declare_ind Sp fuel sg raw log = (log', Ok (sg', d)) ->
  spec_sort Sp s = true ->
  sig_entries tmp = EElim (ind_name d) s (elim_type d s) false :: sig_entries sg' ->
  (exists s', has_type Sp tmp [] (elim_type d s) (Srt s')) /\
  forall r, In r (iota_rules d s) ->
    wf_ctx Sp tmp (rule_ctx r) /\
    has_type Sp tmp (rule_ctx r) (rule_lhs r) (rule_type r) /\
    has_type Sp tmp (rule_ctx r) (rule_rhs r) (rule_type r).

(** The signatures that registrations build from the empty one.  A
    compilation registers its history, the instances it needs and the
    function through the other steps; it is listed so that the
    obligations on built signatures speak of compiled functions
    directly. *)
Inductive built : signature -> Prop :=
| BuiltEmpty : built ∅
| BuiltInd : forall fuel sg raw log log' sg' d,
    built sg -> declare_ind Sp fuel sg raw log = (log', Ok (sg', d)) -> built sg'
| BuiltElim : forall fuel sg D s log log' sg',
    built sg -> declare_elim Sp fuel sg D s log = (log', Ok sg') -> built sg'
| BuiltDef : forall fuel sg f A b log log' sg',
    built sg -> define Sp fuel sg f A b log = (log', Ok sg') -> built sg'
| BuiltCompile : forall fuel sg fn log log' sg',
    built sg -> compile Sp fuel sg fn log = (log', Ok sg') -> built sg'.

(** The same in the annotated kernel, for a declaration of a built
    signature: the judgments that [declare_elim] checks, those of
    [instance_sound], for every sort of the table, without a registration
    that succeeded.  The generator annotates what the checker cannot
    infer. *)
Definition generated_instances_checked : Prop :=
  forall fuel sg raw log log' sg' d s tmp,
  built sg ->
  declare_ind Sp fuel sg raw log = (log', Ok (sg', d)) ->
  spec_sort Sp s = true ->
  sig_entries tmp = EElim (ind_name d) s (elim_type d s) false :: sig_entries sg' ->
  (exists s', is_type_of Sp sg' [] (elim_type d s) s') /\
  forall r, In r (iota_rules d s) ->
    bwf_ctx Sp tmp (rule_ctx r) /\ btype Sp tmp (rule_ctx r) (rule_type r) /\
    chk Sp tmp (rule_ctx r) (rule_lhs r) (rule_type r) /\
    chk Sp tmp (rule_ctx r) (rule_rhs r) (rule_type r).

(** The checks of an instance pass: for a declaration in a built signature,
    with enough fuel the registration of its instance into any sort its
    category allows succeeds.  It rests on [generated_instances_checked],
    not on the declarative [generated_instances_typed], on the
    normalization below and on the completeness of the kernel's checker
    and conversion. *)
Definition instances_registrable : Prop :=
  forall sg D d s, built sg -> sig_ind sg D = Some d -> sig_elim sg D s = None ->
  allows_elimination Sp (ind_elim d) s = true ->
  exists n, forall m, n <= m -> exists log sg', declare_elim Sp m sg D s [] = (log, Ok sg').

(** Built signatures are type-correct: the premise of the kernel's
    [progress] and [bidir_declarative_sound]. *)
Definition registrations_typed : Prop :=
  forall sg, built sg -> signature_typed Sp sg.

(** Built signatures are normalizing: the extended theory of the lecture,
    MLTT with strictly positive inductive families and δ-constants. *)
Definition registrations_normalizing : Prop :=
  forall sg, built sg -> normalizing_types Sp sg.

(** And consistent: no closed term has type Void.  Strict positivity is
    what the bypass gives up. *)
Definition registrations_consistent : Prop :=
  forall sg t, built sg -> ~ has_type Sp sg [] t Void.

(** ** The history (algorithm 2) *)

(** Whatever the registration of the history returns: it was there
    already, or over a signature extending the given one (by [Unit_ℓ] and
    the instances it needs) [Below_D], [build_D] and [recBelow_D] are
    δ-constants, each checked in the signature before it, at a level ℓ
    that is [max i j] for [D : Type_i] and, for a proposition, bounds j
    and the domains of its recursive fields. *)
Definition history_sound : Prop :=
  forall S fuel sg D j log log' sg',
  ensure_below S fuel sg D j log = (log', Ok sg') ->
  sg' = sg \/
  exists d l sg3 sg4 sg5,
    sig_ind sg D = Some d /\ history_level_spec S sg d j l /\
    (exists es, sig_entries sg3 = es ++ sig_entries sg) /\
    defined S sg3 (below_name D j) (below_type d j l) (below_body d l) sg4 /\
    defined S sg4 (build_name D j) (build_type d j) (build_body d j l) sg5 /\
    defined S sg5 (recbelow_name D j) (recbelow_type d j) (recbelow_body d j) sg'.

Theorem history_sound_holds : history_sound.
Proof. intros S fuel. apply ensure_below_sound. Qed.

(** ** Compilation (algorithm 2) *)

(** Whatever [compile] registers: over a signature extending the given
    one by the history and the instances it needs, the function is a
    δ-constant whose type is a type and whose body checks against it
    there, without the function itself; and every defining equation the
    translation derived from the tree, one per leaf, holds by conversion
    in the signature with it. *)
Definition compilation_sound : Prop :=
  forall S fuel sg fn log log' sg',
  compile S fuel sg fn log = (log', Ok sg') ->
  exists sg0 A b eqs,
    (exists log1 log2, compile_term S fuel sg fn log1 = (log2, Ok (sg0, A, b, eqs))) /\
    (exists es, sig_entries sg0 = es ++ sig_entries sg) /\
    defined S sg0 (fn_name fn) A b sg' /\
    Forall (fun eq => exists c, convert sg' fuel (fst eq) (snd eq) = ConvEqual c) eqs.

Theorem compilation_sound_holds : compilation_sound.
Proof. intros S fuel. apply compile_sound. Qed.

(** ** Open obligations of algorithm 2

    Stated, not proved.  Each registration of a history and each
    compilation checks its own output (the two contracts above); these are
    the general theorems behind those checks.  Which case trees the
    translation accepts is decided by the translation itself, with its
    diagnostics; the obligations are about the trees it translates.  It
    does not check the right sides: their types are the part of the
    program, and the translation keeps them, if the right sides rely on
    the type of the function and not on its computation; declaratively
    for the types, in the annotated kernel for the checks to pass.

    A history is found by the name of [recBelow_D]: a δ-constant of that
    name defined by hand would be taken for it.  The obligations assume
    that the constants named as a history are the generated ones. *)

(** What the history at a level ℓ needs: D, ℓ at least j and the levels
    of the domains of the recursive fields of D ([history_bounds]),
    [Unit_ℓ] (the primitive Unit at 0), and [elim_D[ℓ+1]] and [elim_D[ℓ]]
    with active rules.  The level [history_level] takes is such an ℓ: for
    a proposition by its checks, for [D : Type_i] by [within]. *)
Definition history_ready (sg : signature) (d : ind_desc) (j l : nat) : Prop :=
  sig_ind sg (ind_name d) = Some d /\ history_bounds Sp sg d j l /\
  (l = 0 \/ exists u, classify_decl (unit_decl l) = Ok u /\ sig_ind sg (unit_name l) = Some u) /\
  sig_elim sg (ind_name d) (Univ (S l)) = Some (elim_type d (Univ (S l)), true) /\
  sig_elim sg (ind_name d) (Univ l) = Some (elim_type d (Univ l), true).

(** The names the history takes are free; every [Unit_ℓ] declared is the
    one the registration declares. *)
Definition history_names_free (sg : signature) (d : ind_desc) (j : nat) : Prop :=
  let D := ind_name d in
  sig_def sg (below_name D j) = None /\ sig_def sg (build_name D j) = None /\
  sig_def sg (recbelow_name D j) = None /\
  forall l, sig_ind sg (unit_name l) = None \/
            exists u, classify_decl (unit_decl l) = Ok u /\ sig_ind sg (unit_name l) = Some u.

(** The general theorem behind the checks of [ensure_below], for every
    declaration of a built signature, every motive level j and history
    level ℓ it is ready for, and free names: [Below_D], then [build_D]
    with it, then [recBelow_D] with both, have types that are types and
    bodies of those types, in the declarative rules.  The names are free
    so that [sg4] and [sg5] add the constructions rather than shadowing
    constants of [sg]: with [Below_D_0 : Type₀ := Unit] defined by hand
    and D indexed by it, the generated [Below_D_0] makes the domain of
    the index a function, and the type of [build_D_0] is no type
    (Tests.v, [shadow]).  ℓ bounds the domains: at [ℓ := max 0 j] the
    body of [Below_BigP_0] is refused (Tests.v, [bigp_history]). *)
Definition history_typed : Prop :=
  forall sg d j l sg4 sg5,
  built sg -> history_ready sg d j l -> history_names_free sg d j ->
  sig_entries sg4 = EDef (below_name (ind_name d) j) (below_type d j l) (below_body d l) :: sig_entries sg ->
  sig_entries sg5 = EDef (build_name (ind_name d) j) (build_type d j) (build_body d j l) :: sig_entries sg4 ->
  (exists s, has_type Sp sg [] (below_type d j l) (Srt s)) /\
  has_type Sp sg [] (below_body d l) (below_type d j l) /\
  (exists s, has_type Sp sg4 [] (build_type d j) (Srt s)) /\
  has_type Sp sg4 [] (build_body d j l) (build_type d j) /\
  (exists s, has_type Sp sg5 [] (recbelow_type d j) (Srt s)) /\
  has_type Sp sg5 [] (recbelow_body d j) (recbelow_type d j).

(** The same in the annotated kernel: the judgments that [ensure_below]
    checks, those of [history_sound]. *)
Definition history_checked : Prop :=
  forall sg d j l sg4 sg5,
  built sg -> history_ready sg d j l -> history_names_free sg d j ->
  sig_entries sg4 = EDef (below_name (ind_name d) j) (below_type d j l) (below_body d l) :: sig_entries sg ->
  sig_entries sg5 = EDef (build_name (ind_name d) j) (build_type d j) (build_body d j l) :: sig_entries sg4 ->
  (exists s, is_type_of Sp sg [] (below_type d j l) s) /\
  chk Sp sg [] (below_body d l) (below_type d j l) /\
  (exists s, is_type_of Sp sg4 [] (build_type d j) s) /\
  chk Sp sg4 [] (build_body d j l) (build_type d j) /\
  (exists s, is_type_of Sp sg5 [] (recbelow_type d j) s) /\
  chk Sp sg5 [] (recbelow_body d j) (recbelow_type d j).

(** The checks of the history pass: for a declaration of a built
    signature that eliminates into every sort, at any level, with enough
    fuel its registration succeeds.  A proposition eliminated into Prop
    only, such as [or], has no instances into Type, and its history is
    refused with [RElimSort].  It rests on [history_checked],
    [instances_registrable], the normalization of the extended theory and
    the completeness of the kernel's checker and conversion. *)
Definition history_registrable : Prop :=
  forall sg d j, built sg -> sig_ind sg (ind_name d) = Some d -> ind_elim d = AllSorts ->
  history_names_free sg d j ->
  exists n, forall m, n <= m -> exists log sg', ensure_below Sp m sg (ind_name d) j [] = (log, Ok sg').

(** The constants named as a history are the generated ones, at some
    level. *)
Definition histories_genuine (sg : signature) : Prop :=
  forall D j A b, sig_def sg (recbelow_name D j) = Some (A, b) ->
  exists d l, sig_ind sg D = Some d /\
    sig_def sg (below_name D j) = Some (below_type d j l, below_body d l) /\
    sig_def sg (build_name D j) = Some (build_type d j, build_body d j l) /\
    A = recbelow_type d j /\ b = recbelow_body d j.

(** The leaves of an elaborated tree: the scope, the goal and the right
    side of each, whose calls name the function. *)
Fixpoint leaves (e : elab) : list (scope * term * term) :=
  match e with
  | ELeaf G goal _ rhs => [(G, goal, rhs)]
  | ESplit _ _ _ brs => flat_map (fun '(_, e') => leaves e') brs
  end.

(** Every right side has its goal in its scope, in every signature [sgf]
    that extends [sg0] by the function [f] at its declared type [A],
    whatever its body [b']: a right side may rely on the type of [f], not
    on its computation.  The translation replaces each call by a
    hypothesis or an access to the history, which does not compute, so
    the body of [f] would not do as the only [b']: the right side of
    [peek] in Tests.v has its goal with the compiled body, through
    [peek Q w k ≡ elimNat (λ_. ℕ) zero (λ_ _. zero) k], and the
    compiled body, where the hypothesis stands for the call, is refused.
    Among the bodies is [f] itself, under which [f] does not compute. *)
Definition leaves_typed (sg0 : signature) (f : string) (A : term) (ls : list (scope * term * term)) : Prop :=
  forall sgf b', sig_entries sgf = EDef f A b' :: sig_entries sg0 ->
  Forall (fun l => let '(G, goal, rhs) := l in has_type Sp sgf (map b_type G) rhs goal) ls.

(** The same in the annotated kernel: every right side checks against
    its goal, whatever the body of [f].  The declarative rules type more:
    the right side [(λx. x) zero] of [beta] in Tests.v has its goal ℕ,
    yet the checker cannot infer the λ at the head of the application,
    and refuses the body with [ECannotInfer] whatever the fuel. *)
Definition leaves_checked (sg0 : signature) (f : string) (A : term) (ls : list (scope * term * term)) : Prop :=
  forall sgf b', sig_entries sgf = EDef f A b' :: sig_entries sg0 ->
  Forall (fun l => let '(G, goal, rhs) := l in chk Sp sgf (map b_type G) rhs goal) ls.

(** The translation keeps types: when the declared type is a type and
    every right side has its goal, the compiled body has the declared
    type.  The calls become accesses to the history, or hypotheses, of
    the types of the calls; the motives with the generalized tail give
    each branch its goal.  The name of the function is free in [sg0], so
    that [sgf] of the premise adds it rather than shadowing a constant of
    [sg0], as in [equations_definitional]. *)
Definition translation_typed : Prop :=
  forall fuel sg fn log log' sg0 A b ls,
  built sg -> histories_genuine sg ->
  compile_with Sp fuel leaves sg fn log = (log', Ok (sg0, A, b, ls)) ->
  sig_def sg0 (fn_name fn) = None ->
  (exists s, has_type Sp sg0 [] A (Srt s)) ->
  leaves_typed sg0 (fn_name fn) A ls ->
  has_type Sp sg0 [] b A.

(** And in the annotated kernel: when the declared type is a type there
    and every right side checks against its goal, the compiled body
    checks against the declared type.  The right sides stand in the
    bodies of the methods, checked against types that reduce to their
    goals; the hypotheses and the accesses synthesize types convertible
    to those of the calls they replace; the motives of the eliminators
    of Void, Unit and Bool are annotated. *)
Definition translation_checked : Prop :=
  forall fuel sg fn log log' sg0 A b ls,
  built sg -> histories_genuine sg ->
  compile_with Sp fuel leaves sg fn log = (log', Ok (sg0, A, b, ls)) ->
  sig_def sg0 (fn_name fn) = None ->
  (exists s, is_type_of Sp sg0 [] A s) ->
  leaves_checked sg0 (fn_name fn) A ls ->
  chk Sp sg0 [] b A.

(** The defining equations hold by definition, for every tree the
    translation accepts, whatever its right sides: the left side unfolds
    the function, ι computes the eliminators on the constructors of its
    patterns, and each access to the history or hypothesis reduces to
    the call it replaces.  [compile] finds each conversion with
    [convert]; this is the declarative conversion behind it.  The name of
    the function is free in [sg0], as [define] requires: the translation
    does not check it, and a function named [recBelow_Nat_0] by [History]
    would shadow the recursor its own history registers, its body then
    unfolding through itself (Tests.v, [clash]). *)
Definition equations_definitional : Prop :=
  forall S fuel sg fn log log' sg0 A b eqs sgf,
  built sg -> histories_genuine sg ->
  compile_term S fuel sg fn log = (log', Ok (sg0, A, b, eqs)) ->
  sig_def sg0 (fn_name fn) = None ->
  sig_entries sgf = EDef (fn_name fn) A b :: sig_entries sg0 ->
  Forall (fun eq => conv sgf (fst eq) (snd eq)) eqs.

(** The checks of a compilation pass: for a tree the translation accepts,
    whose declared type is a type and whose right sides check against
    their goals, in the annotated kernel, with enough fuel the
    compilation succeeds.  Declarative premises would not do: [beta] has
    them and is refused whatever the fuel.  It rests on
    [translation_checked], [equations_definitional], the normalization of
    the extended theory, for the types and for the sides of the
    equations, and the completeness of the kernel's checker and
    conversion. *)
Definition compilation_registrable : Prop :=
  forall fuel sg fn log log' sg0 A b ls,
  built sg -> histories_genuine sg -> sig_def sg0 (fn_name fn) = None ->
  compile_with Sp fuel leaves sg fn log = (log', Ok (sg0, A, b, ls)) ->
  (exists s, is_type_of Sp sg0 [] A s) ->
  leaves_checked sg0 (fn_name fn) A ls ->
  exists n, forall m, n <= m -> exists log'' sg', compile Sp m sg fn [] = (log'', Ok sg').

(** Totality: a compiled function is a δ-constant whose body does not
    mention it, so it adds no recursion, and a closed application of it
    that is typed normalizes.  It follows from the normalization of the
    extended theory for terms, beyond [registrations_normalizing] for
    types. *)
Definition compiled_total : Prop :=
  forall fuel sg fn log log' sg' args T,
  built sg -> compile Sp fuel sg fn log = (log', Ok sg') ->
  has_type Sp sg' [] (apps (Const (Def (fn_name fn))) args) T ->
  exists v, clos_refl_trans term (nstep sg') (apps (Const (Def (fn_name fn))) args) v /\ nf sg' v.
