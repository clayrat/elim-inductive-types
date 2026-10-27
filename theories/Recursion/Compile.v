(** * [compile_checked]: structural recursion through [Below]

    The translation of algorithm 2, from an annotated function
    (Recursion.CaseTree) to a term with eliminators and without the
    original recursive calls:
    1. the motive of the recursion [P θ̄ x := Π(Γ_P). T]: Γ_P holds the
       varying arguments and those whose types depend on θ̄ or x, whatever
       their mark, closed under dependency and built once in dependency
       order; the other constant arguments stay outside.  An argument in
       the parameters Δ must be constant: changing one, such as A in a
       recursion on [List A], is non-uniform recursion and is rejected.
       This is the generalization of a split (Recursion.CaseTree) with the
       varying arguments in its tail;
    2. through the history ([History]): with [j] the level of [P θ̄ x],
       the triple [Below_D], [build_D], [recBelow_D] of (D, j)
       (Recursion.Below), and
       [f := λ args. recBelow_D Δ P step θ̄ x Γ_P] with
       [step := λθ̄ x table. λΓ_P. ⟦tree⟧]; the scope of the tree binds θ̄
       and x again, the history [table] and Γ_P again;
       directly ([Direct]): the root of the tree is the split of x, by
       [elim_D[j]] with the motive P, and its hypotheses take the calls;
    3. the case splits: the split of [z : D Δ θ̄] is
       [elim_D[k] Δ M m̄ θ̄ z tail] with [M := λθ̄ z. Π(tail). T] and
       [m_c := λ fields hypotheses. λ tail. ⟦branch⟧], where [k] is the
       level of [Π(tail). T], found by the checker: without cumulativity
       the instance must have exactly that level.  A split of Void, Unit
       or Bool is their primitive eliminator, with the motive annotated
       [M ∷ (Bool → Type_k)] so that it can be inferred; the structural
       argument itself is of a declared family;
    4. the recursive calls: a call on a pattern variable with a path of
       length at least 1, applied to its positions, becomes the access to
       its result in the history (the hypothesis of its field, for
       [Direct]), applied to the arguments of Γ_P in the order of the
       motive.  With no such access the definition is rejected: this is
       the check of structural decrease, a syntactic one.  The indices of
       the call must be those of the subterm, and the constant arguments
       outside Γ_P those of the function.

    In the history, the component [k] of [n] of a tuple nested to the
    right is [fst (snd^k h)], or [snd^k h] for the last; a subterm two
    splits down is reached through [snd] of the component of the subterm
    split, and its result is [fst] of its component applied to the
    positions.  In the branch [half (succ (succ n))] the history has the
    type [P (succ n) × (P n × Below P n)], and [half n] becomes
    [fst (snd table)].

    The translation does not change the signature: it finds the levels of
    the motives and the instances [elim_D[k]] they need, which are then
    registered.  The output is registered as a δ-constant, checked
    against the declared type in the signature without it, without [fix]
    and without new primitives; its body does not mention it, so totality
    follows from the normalization of the kernel.  Every defining
    equation is then checked by conversion with open pattern variables,
    e.g. [half (succ (succ n)) ≡ succ (half n)]: the equations hold by
    definition, unlike with well-founded recursion.  For that every leaf
    is reached through a split of the structural argument: a leaf where
    it is still a variable leaves [recBelow] stuck on it. *)

From Stdlib Require Import List Bool Arith.
From Stdlib Require String.
Import ListNotations.
Import (notations) String.StringSyntax.
Local Open Scope string_scope.
Local Open Scope list_scope.
From DepTypes.Common Require Import Result Traced.
From DepTypes.PTS Require Import Syntax Spec Signature Eval Check.
From IndTypes.Elim Require Import Decl Generate Declare.
From IndTypes.Recursion Require Import Below CaseTree.

Local Notation string := String.string.

(** ** Recursive calls *)

(** What the translation of a call needs to know of the function: its
    name and arity, the position of the structural argument, the number of
    parameters of its type, the positions of its indices and of Γ_P among
    the arguments, their names, and the strategy. *)
Record recursion : Type := {
  rec_name : string;
  rec_arity : nat;
  rec_struct : nat;
  rec_params : nat;
  rec_indices : list nat;
  rec_tail : list nat;
  rec_names : list string;
  rec_strategy : strategy;
}.

(** The component [k] of a tuple of [n], nested to the right. *)
Definition component (k n : nat) (h : term) : term :=
  let h' := Nat.iter k Snd h in
  if Nat.eqb (S k) n then h' else Fst h'.

(** The result of the subterm at the path [p] from the history [h],
    applied to its positions [ys]. *)
Fixpoint access (h : term) (p : path) (ys : list term) : term :=
  match p with
  | [] => h
  | [(k, n)] => Fst (apps (component k n h) ys)
  | (k, n) :: p' => access (Snd (component k n h)) p' ys
  end.

Section Calls.
  Variable rc : recursion.
  Variable G : scope.               (** the scope of the leaf *)
  Variable env : list term.         (** the values of the arguments there *)

  (** The subterm of the structural argument of a call, [r ys], under [d]
      binders of the right side: the index of [r] in the scope, its path
      and its type. *)
  Definition subterm (d : nat) (s : term) : option (nat * path * term) :=
    match spine_head s with
    | Var w =>
        if Nat.leb d w then
          match nth_error G (w - d) with
          | Some {| b_tag := User _ (Some ((_ :: _) as p)); b_type := A |} => Some (w - d, p, A)
          | _ => None
          end
        else None
    | _ => None
    end.

  (** The indices of [r ys], where [r : Πȳ:B̄. D Δ v̄] lies at [u] in the
      scope: [v̄] with [ys] for ȳ, under [d] binders. *)
  Definition subterm_indices (d u : nat) (A : term) (ys : list term) : list term :=
    let '(Bs, body) := split_pis A in
    let m := length Bs in
    map (subst (fun i => if Nat.ltb i m then nth (m - 1 - i) ys (Var 0) else Var (i - m + S u + d)))
      (skipn (rec_params rc) (spine_args body)).

  (** A call [f args] under [d] binders of the right side, its arguments
      already translated; [t] is the call, for diagnostics. *)
  Definition call (d : nat) (t : term) (args : list term) : result case_error term :=
    let n := rec_arity rc in
    let* _ := require (Nat.leb n (length args)) (CCallArity t) in
    let cargs := firstn n args in
    let s := nth (rec_struct rc) cargs (Var 0) in
    let* r := match subterm d s with Some r => Ok r | None => Err (CNotStructural t) end in
    let '(u, p, A) := r in
    let ys := spine_args s in
    let* _ := require (Nat.eqb (length ys) (length (fst (split_pis A)))) (CNotStructural t) in
    let name i := nth i (rec_names rc) "" in
    let* _ := mapM (fun '(i, v) =>
                if term_eqb (nth i cargs (Var 0)) v then Ok tt else Err (CIndexChanged (name i) t))
                (combine (rec_indices rc) (subterm_indices d u A ys)) in
    let* _ := mapM (fun i =>
                if mem i (rec_tail rc) || mem i (rec_indices rc) || Nat.eqb i (rec_struct rc)
                   || term_eqb (nth i cargs (Var 0)) (lift d (nth i env (Var 0)))
                then Ok tt else Err (CConstantChanged (name i) t))
                (seq 0 n) in
    let* acc := match rec_strategy rc, p with
                | Direct, [(k, _)] =>
                    match find_aux (S k) G with
                    | Some h => Ok (apps (Var (h + d)) ys)
                    | None => Err (CNotStructural t)
                    end
                | Direct, _ => Err (CNotImmediate t)
                | History, _ =>
                    match find_aux 0 G with
                    | Some h => Ok (access (Var (h + d)) p ys)
                    | None => Err (CNotStructural t)
                    end
                end in
    Ok (apps acc (map (fun i => nth i cargs (Var 0)) (rec_tail rc) ++ skipn n args)).

  (** A term in translation: done, or the function with the arguments it
      has received so far. *)
  Inductive part : Type :=
  | Done : term -> part
  | Pending : list term -> part.

  Definition done (d : nat) (r : part) : result case_error term :=
    match r with
    | Done u => Ok u
    | Pending args => Err (CCallArity (apps (Const (Def (rec_name rc))) args))
    end.

  (** The calls of a right side, under [d] binders. *)
  Fixpoint calls_in (d : nat) (t : term) : result case_error part :=
    let sub d' u := let* r := calls_in d' u in done d' r in
    match t with
    | Const (Def g) => if String.eqb g (rec_name rc) then Ok (Pending []) else Ok (Done t)
    | App u a =>
        let* ru := calls_in d u in
        let* a' := sub d a in
        match ru with
        | Pending args =>
            let args' := args ++ [a'] in
            if Nat.eqb (length args') (rec_arity rc)
            then let* c := call d (apps (Const (Def (rec_name rc))) args') args' in Ok (Done c)
            else Ok (Pending args')
        | Done u' => Ok (Done (App u' a'))
        end
    | Pi A B => let* A' := sub d A in let* B' := sub (S d) B in Ok (Done (Pi A' B'))
    | Lam b => let* b' := sub (S d) b in Ok (Done (Lam b'))
    | Ann u A => let* u' := sub d u in let* A' := sub d A in Ok (Done (Ann u' A'))
    | ElimVoid C e => let* C' := sub d C in let* e' := sub d e in Ok (Done (ElimVoid C' e'))
    | ElimUnit C c u =>
        let* C' := sub d C in let* c' := sub d c in let* u' := sub d u in Ok (Done (ElimUnit C' c' u'))
    | ElimBool C x y b =>
        let* C' := sub d C in let* x' := sub d x in let* y' := sub d y in let* b' := sub d b in
        Ok (Done (ElimBool C' x' y' b'))
    | Sigma A B => let* A' := sub d A in let* B' := sub (S d) B in Ok (Done (Sigma A' B'))
    | Pair a b => let* a' := sub d a in let* b' := sub d b in Ok (Done (Pair a' b'))
    | Fst u => let* u' := sub d u in Ok (Done (Fst u'))
    | Snd u => let* u' := sub d u in Ok (Done (Snd u'))
    | _ => Ok (Done t)
    end.

  Definition calls (t : term) : result case_error term := let* r := calls_in 0 t in done 0 r.
End Calls.

(** ** Translation *)

Definition case {A} (r : result case_error A) : R A :=
  match r with
  | Ok a => tret a
  | Err e => refuse (RCase e)
  end.

Definition level_of (x : string) (s : sort) : R nat :=
  match s with
  | Univ k => tret k
  | _ => refuse (RCase (CMotiveSort x s))
  end.

(** The eliminator of a primitive type, its motive annotated so that it
    can be inferred. *)
Definition prim_elim (pr : prim) (C : term) (ms : list term) (z : term) : term :=
  match pr, ms with
  | PUnit, [m] => ElimUnit C m z
  | PBool, [mt; mf] => ElimBool C mt mf z
  | _, _ => ElimVoid C z
  end.

Section Translate.
  Variable Sp : spec.
  Variable fuel : nat.
  Variable sg : signature.
  Variable rc : recursion.

  (** The level of [Π(tail). T] after the scope and the seeds. *)
  Definition motive_level (G : scope) (x : string) (gn : generalized) : R nat :=
    let! s := sort_of Sp fuel sg (AtMotive (rec_name rc) x) (rev (gn_seed_types gn) ++ map b_type G)
                (pis (gn_tail_types gn) (gn_goal gn)) in
    level_of x s.

  (** The term of an elaborated tree in its scope, and the instances of
      eliminators it uses. *)
  Fixpoint translate (e : elab) : R (term * list (string * nat)) :=
    match e with
    | ELeaf G _ env rhs => let! t := case (calls rc G env rhs) in tret (t, [])
    | ESplit G _ si brs =>
        let sv := si_var si in
        let gn := si_gen si in
        let N := length G in
        let! k := motive_level G (sv_name sv) gn in
        let! ms := (fix go (brs : list (nat * elab)) : R (list term * list (string * nat)) :=
                      match brs with
                      | [] => tret ([], [])
                      | (b, e') :: brs' =>
                          let! r := translate e' in
                          let! rs := go brs' in
                          tret (lams b (lams (length (gn_tail gn)) (fst r)) :: fst rs, snd r ++ snd rs)
                      end) brs in
        let D := ind_name (sv_desc sv) in
        let seeds := map (var_at N) (gn_seeds gn) in
        let tail := map (var_at N) (gn_tail gn) in
        match sv_prim sv with
        | None =>
            tret (apps (Const (Elim D k)) (sv_params sv ++ [motive gn] ++ fst ms ++ seeds ++ tail),
                  (D, k) :: snd ms)
        | Some pr =>
            let C := Ann (motive gn) (Pi (prim_type pr) (Srt (Univ k))) in
            tret (apps (prim_elim pr C (fst ms) (var_at N (sv_level sv))) tail, snd ms)
        end
    end.
End Translate.

(** ** The defining equations *)

(** Every leaf is reached through a split of the structural argument: no
    binder there is the structural argument itself.  Otherwise its
    equation could not hold by definition, the recursion stuck on a
    variable. *)
Fixpoint splits_struct (e : elab) : bool :=
  match e with
  | ELeaf G _ _ _ => negb (existsb (fun b => match b_tag b with User _ (Some []) => true | _ => false end) G)
  | ESplit _ _ _ brs => forallb (fun '(_, e') => splits_struct e') brs
  end.

(** At every leaf, in the order of the tree: the function applied to the
    values of its arguments, and the right side. *)
Fixpoint equations (f : string) (e : elab) : list (term * term) :=
  match e with
  | ELeaf _ _ env rhs => [(apps (Const (Def f)) env, rhs)]
  | ESplit _ _ _ brs => flat_map (fun '(_, e') => equations f e') brs
  end.

Section Compile.
  Variable Sp : spec.
  Variable fuel : nat.

  Definition check_equation (sg : signature) (f : string) (ie : nat * (term * term)) : R unit :=
    let '(i, (lhs, rhs)) := ie in
    match convert sg fuel lhs rhs with
    | ConvEqual u => temit (AtEquation f i, [EvConv lhs rhs u])
    | ConvOutOfFuel => let! _ := temit (AtEquation f i, []) in tfail (NoFuelAt (AtEquation f i) lhs)
    | _ => let! _ := temit (AtEquation f i, []) in refuse (REquation f i lhs rhs)
    end.

  (** The translation: the signature with the history and the instances
      it needs, the type of the function, its body, and its equations. *)
  Definition compile_term (sg : signature) (fn : fun_decl)
    : R (signature * term * term * list (term * term)) :=
    let f := fn_name fn in
    let x := fn_struct fn in
    let! s0 := case (start fn) in
    let '(G0, goal0, env0) := s0 in
    let! si := case (prepare_split sg G0 goal0 x (varying fn)) in
    let sv := si_var si in
    let gn := si_gen si in
    let d := sv_desc sv in
    let params := sv_params sv in
    let θ := sv_indices sv in
    let! _ := match sv_prim sv with Some pr => refuse (RCase (CNotFamily x (prim_type pr))) | None => tret tt end in
    let N := length G0 in
    let rc := {| rec_name := f; rec_arity := N; rec_struct := sv_level sv;
                 rec_params := length (ind_params d); rec_indices := θ; rec_tail := gn_tail gn;
                 rec_names := map (fun '(y, _, _) => y) (fn_args fn); rec_strategy := fn_strategy fn |} in
    let D := ind_name d in
    let! r := match fn_strategy fn with
      | Direct =>
          let! _ := match fn_tree fn with
                    | Split y _ => if String.eqb y x then tret tt else refuse (RCase (CRoot x))
                    | Leaf _ => refuse (RCase (CRoot x))
                    end in
          let! e := case (elaborate_with sg (varying fn) (fun k => Aux (S k)) G0 goal0 env0 (fn_tree fn)) in
          let! t := translate Sp fuel sg rc e in
          tret (sg, fst t, snd t, e)
      | History =>
          let q := length θ in
          let! j := motive_level Sp fuel sg rc G0 x gn in
          let! sg1 := ensure_below Sp fuel sg D j in
          let P := motive gn in
          let seeds := map (fun '(l, A) => mk_binder (match at_level G0 l with Some b => b_tag b | None => Anon end) A)
                         (combine (gn_seeds gn) (gn_seed_types gn)) in
          let table := apps (Const (Def (below_name D j)))
                         (map (lift (S q)) params ++ [lift (S q) P] ++ vars 0 (S q)) in
          let '(G1, goal1, sb) := introduce G0 gn (seeds ++ [mk_binder (Aux 0) table]) (vars 1 (S q)) in
          let! e := case (elaborate sg1 G1 goal1 (map (subst sb) env0) (fn_tree fn)) in
          let! t := translate Sp fuel sg1 rc e in
          let step := lams (S q) (Lam (lams (length (gn_tail gn)) (fst t))) in
          tret (sg1,
                apps (Const (Def (recbelow_name D j)))
                  (params ++ [P; step] ++ map (var_at N) (gn_seeds gn ++ gn_tail gn)),
                snd t, e)
      end in
    let '(sg1, root, needed, e) := r in
    let! _ := if splits_struct e then tret tt else refuse (RCase (CUnsplit x)) in
    let! sg2 := tfold (fun sg '(D, k) => ensure_elim Sp fuel sg D k) sg1 needed in
    tret (sg2, pis (map b_type (rev G0)) goal0, lams N root, equations f e).

  (** The function, registered as a δ-constant, and its equations checked. *)
  Definition compile (sg : signature) (fn : fun_decl) : R signature :=
    let! r := compile_term sg fn in
    let '(sg0, A, b, eqs) := r in
    let! sg' := define Sp fuel sg0 (fn_name fn) A b in
    let! _ := titer (check_equation sg' (fn_name fn)) (combine (seq 0 (length eqs)) eqs) in
    tret sg'.
End Compile.

Definition compile_checked (S : spec) (fuel : nat) (sg : signature) (fn : fun_decl)
  : list (stage * list event) * registration :=
  run_registration (compile S fuel sg fn).

(** Several functions in turn, each in the signature of those before. *)
Definition compile_all (S : spec) (fuel : nat) (sg : signature) (fns : list fun_decl)
  : list (stage * list event) * registration :=
  run_registration (tfold (compile S fuel) sg fns).

(** ** What a compilation guarantees

    Whatever [compile] registers: the function is a δ-constant whose type
    is a type and whose body checks against it in a signature that
    extends the given one (by the history and the instances it needs) and
    does not contain the function, in the judgments of the annotated
    kernel; and every defining equation of the tree holds by conversion
    in the signature with it. *)

From DepTypes.PTS Require Import Bidir.

Section Sound.
  Variable Sp : spec.
  Variable fuel : nat.

  Lemma ensure_below_extends : forall sg D j log log' sg',
    ensure_below Sp fuel sg D j log = (log', Ok sg') -> exists es, sig_entries sg' = es ++ sig_entries sg.
  Proof.
    intros sg D j log log' sg' H.
    destruct (ensure_below_sound _ _ _ _ _ _ _ _ H) as [-> | (d & sg3 & sg4 & sg5 & _ & [es E3] & D4 & D5 & D6)];
      [now exists [] | ].
    destruct D4 as (_ & _ & _ & E4), D5 as (_ & _ & _ & E5), D6 as (_ & _ & _ & E6).
    eexists. rewrite E6, E5, E4, E3. now rewrite !app_comm_cons.
  Qed.

  Lemma instances_extend : forall needed sg log log' sg',
    tfold (fun sg '(D, k) => ensure_elim Sp fuel sg D k) sg needed log = (log', Ok sg') ->
    exists es, sig_entries sg' = es ++ sig_entries sg.
  Proof.
    induction needed as [|[D k] needed IH]; intros sg log log' sg' H; cbn in H.
    - apply tret_ok in H. subst. now exists [].
    - tbind_in H sg1 H1. apply ensure_elim_extends in H1 as [es1 E1].
      apply IH in H as [es E]. exists (es ++ es1). now rewrite E, E1, app_assoc.
  Qed.

  Lemma compile_term_extends : forall sg fn log log' sg0 A b eqs,
    compile_term Sp fuel sg fn log = (log', Ok (sg0, A, b, eqs)) ->
    exists es, sig_entries sg0 = es ++ sig_entries sg.
  Proof.
    intros sg fn log log' sg0 A b eqs H. unfold compile_term in H.
    tbind_in H s0 Hs. destruct s0 as [[G0 goal0] env0].
    tbind_in H si Hp.
    tbind_in H w Hw.
    tbind_in H r Hr. destruct r as [[[sg1 root] needed] e].
    tbind_in H w' Hw'.
    tbind_in H sg2 H2. apply tret_ok in H. injection H as <- _ _ _.
    apply instances_extend in H2 as [es2 E2].
    assert (exists es, sig_entries sg1 = es ++ sig_entries sg) as [es1 E1].
    { destruct (fn_strategy fn).
      - tbind_in Hr u Hu. tbind_in Hr e' He. tbind_in Hr t Ht.
        apply tret_ok in Hr. injection Hr as <- _ _ _. now exists [].
      - tbind_in Hr j Hj. tbind_in Hr sg1' H1. apply ensure_below_extends in H1 as [es1 E1].
        match type of Hr with context [introduce ?G ?gn ?B ?vs] => destruct (introduce G gn B vs) as [[G1 goal1] sb] end.
        tbind_in Hr e' He. tbind_in Hr t Ht.
        apply tret_ok in Hr. injection Hr as <- _ _ _. now exists es1. }
    exists (es2 ++ es1). now rewrite E2, E1, app_assoc.
  Qed.

  Lemma check_equation_ok : forall sg f ie log log' u,
    check_equation fuel sg f ie log = (log', Ok u) ->
    exists c, convert sg fuel (fst (snd ie)) (snd (snd ie)) = ConvEqual c.
  Proof.
    intros sg f [i [lhs rhs]] log log' u H. unfold check_equation in H. cbn.
    destruct (convert sg fuel lhs rhs) as [c| | |]; [now exists c | | | ].
    all: tbind_in H w Hw; discriminate H.
  Qed.

  Lemma numbered_Forall : forall {A} (Q : A -> Prop) k (l : list A),
    Forall (fun ia => Q (snd ia)) (combine (seq k (length l)) l) -> Forall Q l.
  Proof.
    intros A Q k l. revert k. induction l as [|a l IH]; intros k H; [constructor | ].
    cbn in H. inversion H as [|? ? Ha Hl]. constructor; [exact Ha | exact (IH _ Hl)].
  Qed.

  Theorem compile_sound : forall sg fn log log' sg',
    compile Sp fuel sg fn log = (log', Ok sg') ->
    exists sg0 A b eqs,
      (exists log1 log2, compile_term Sp fuel sg fn log1 = (log2, Ok (sg0, A, b, eqs))) /\
      (exists es, sig_entries sg0 = es ++ sig_entries sg) /\
      defined Sp sg0 (fn_name fn) A b sg' /\
      Forall (fun eq => exists c, convert sg' fuel (fst eq) (snd eq) = ConvEqual c) eqs.
  Proof.
    intros sg fn log log' sg' H. unfold compile in H.
    tbind_in H r Hr. destruct r as [[[sg0 A] b] eqs].
    tbind_in H sg1 H1. tbind_in H u Hu. apply tret_ok in H. subst sg1.
    exists sg0, A, b, eqs. split; [eauto | split; [eapply compile_term_extends; exact Hr | split]].
    - eapply define_sound. exact H1.
    - apply titer_Forall in Hu. apply (numbered_Forall _ 0).
      eapply Forall_impl; [ | exact Hu]. intros ie (l1 & l2 & w & Hc).
      exact (check_equation_ok _ _ _ _ _ _ Hc).
  Qed.
End Sound.
