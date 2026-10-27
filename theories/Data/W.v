(** * W-types

      data W (A : Type_i) (B : A → Type_i) : Type_i where
        sup : Π(a : A). (B a → W A B) → W A B

    A declaration with a functional recursive field, one more input of
    algorithm 1, declared at i = 0.  The label fixes the type of the
    positions of the children, and the function maps each position to a
    subtree.  The method of [elim_W[j]] gets [a : A], [f : B a → W] and
    [h : Πb:B a. P (f b)]: generalized structural induction.  The history
    has one component, [Below_P (sup a f) := Πb:B a. (P (f b) ×
    Below_P (f b))], itself a function rather than a finite table.

    ℕ_W: labels Bool, positions [B b := elimBool (λ_. Type₀) Unit Void b]
    ([IsTrue] of lecture 6); [zero_W := sup false (λv. elimVoid _
    v)], [succ_W n := sup true (λ_. n)]; one step of the eliminator on
    [succ_W n]; the recursor with a constant motive computes on canonical
    terms.

    The direct transfer of dependent induction to ℕ_W through the
    W-eliminator fails on conversion in this kernel.  In the branch
    [false] the method must give [P (sup false f)] for an arbitrary
    [f : Void → ℕ_W] but has only [P zero_W]; in the branch [true] it
    gives [P (sup true (λ_. f tt))] for [P (sup true f)], which η for Π
    and Unit would fix, though not the branch of zero.  The trace of this
    rejection is no proof that the principle is underivable.

    So far: the declaration, whose classification is the description of
    W written by hand in the kernel (MLTT/Families.v): the field [f] is
    recursive with one position, of the type [B a].

    Generated: its eliminator, the kernel's hand-written [elimW[0]].

    Registered by [declare_checked], as the kernel's hand-written entries.

    ℕ_W as δ-constants over it, each checked without itself:
    [IsTrue : Bool → Type₀], [Nat_W := W Bool IsTrue],
    [zero_W : Nat_W] and [succ_W : Nat_W → Nat_W].  The motives of the
    primitive eliminators are annotated, so that they can be inferred.
    The positions of [zero_W] are [IsTrue false ≡ Void], those of a
    successor [IsTrue true ≡ Unit].

    One step of [elim_W[0]] on [succ_W n] for open [P], [m] and [n]:
    δ, β and ι to the head form [m true (λ_. n) h], where [h tt] reduces
    to the eliminator on [n].  The ι-reduct checks only after one more β:
    the bidirectional checker cannot infer the redex [(λ_. n) b] it
    contains.

    The recursor [rec_W : Π(C : Type₀). C → (C → C) → ℕ_W → C], a
    δ-constant through [elim_W[0]] whose method carries the hypothesis
    through the match on the label; without it [h tt] is refused.  Its
    equations hold by conversion for an open [n], and it computes on
    canonical terms.

    The direct transfer of dependent induction, [ind_W] through
    [elim_W[0]], refused by conversion in the branch [true], and the
    branch [false] refused on its own; the conversions that η for Π and
    Unit would supply, and the one in the branch of zero they would not. *)

From Stdlib Require Import String List Bool.
Import ListNotations.
From DepTypes.Common Require Import Result Traced.
From DepTypes.PTS Require Import Syntax Named Signature Eval Check.
From DepTypes.Configs Require Import Predicative.
From DepTypes.SystemU Require Import Looping.
From DepTypes.MLTT Require Import Choose Families.
From IndTypes.Elim Require Import Decl Generate Declare.

Open Scope string_scope.
Open Scope nterm_scope.

Definition raw_w : raw_decl := {|
  rd_name := "W"; rd_params := [Srt (Univ 0); build ["A"] ("A" ~> Type@ 0)]; rd_indices := [];
  rd_level := 0;
  rd_ctors := [mk_raw_ctor "sup" (build ["B"; "A"] (Π "a" : "A", ("B" "a" ~> W "A" "B") ~> W "A" "B"))] |}.

Example w_classified : classify_decl raw_w = Ok w_desc.
Proof. vm_compute. reflexivity. Qed.

Example w_elim_generated : elim_type w_desc 0 = build [] elim_w_ty.
Proof. vm_compute. reflexivity. Qed.

Example w_registered :
  option_map sig_entries (registered (declare_checked predicative 300 ∅ raw_w [0]))
  = Some [EElim "W" 0 (build [] elim_w_ty) true; EInd w_desc].
Proof. vm_compute. reflexivity. Qed.

(** ** ℕ_W *)

Definition w_fuel : nat := 300.

Definition IsTrue : nterm := NConst (Def "IsTrue").
Definition Nat_W : nterm := NConst (Def "Nat_W").
Definition zero_W : nterm := NConst (Def "zero_W").
Definition succ_W : nterm := NConst (Def "succ_W").

(** [IsTrue b := elimBool (λ_. Type₀) Unit Void b]: the positions of the
    children of a node labelled [b]. *)
Definition is_true_body : nterm := λ "b", NElimBool ((λ "_", Type@ 0) ∷ (NBool ~> Type@ 1)) NUnit NVoid "b".

(** [zero_W := sup false (λv. elimVoid _ v)]: no children. *)
Definition no_child : nterm := λ "v", NElimVoid ((λ "_", Nat_W) ∷ (NVoid ~> Type@ 0)) "v".
Definition zero_w_body : nterm := sup NBool IsTrue NFalse no_child.

(** [succ_W n := sup true (λ_. n)]: one child. *)
Definition succ_w_body : nterm := λ "n", sup NBool IsTrue NTrue (λ "_", "n").

Definition nat_w_run : list (stage * list event) * registration :=
  run_registration (
    let! s1 := declare predicative w_fuel ∅ raw_w [0] in
    let! s2 := define predicative w_fuel s1 "IsTrue" (build [] (NBool ~> Type@ 0)) (build [] is_true_body) in
    let! s3 := define predicative w_fuel s2 "Nat_W" (build [] (Type@ 0)) (build [] (W NBool IsTrue)) in
    let! s4 := define predicative w_fuel s3 "zero_W" (build [] Nat_W) (build [] zero_w_body) in
    define predicative w_fuel s4 "succ_W" (build [] (Nat_W ~> Nat_W)) (build [] succ_w_body)).

Definition sg_nat_w : signature := match registered nat_w_run with Some sg => sg | None => ∅ end.

(** W with its eliminator, then the four constants, each its type and its
    body. *)
Example nat_w_stages :
  map fst (fst nat_w_run) =
  [AtIndType "W"; AtCtorType "W" "sup"; AtField "W" "sup" 0; AtField "W" "sup" 1;
   AtElimType "W" 0; AtRuleLhs "W" 0 "sup"; AtRuleRhs "W" 0 "sup";
   AtDefType "IsTrue"; AtDefBody "IsTrue"; AtDefType "Nat_W"; AtDefBody "Nat_W";
   AtDefType "zero_W"; AtDefBody "zero_W"; AtDefType "succ_W"; AtDefBody "succ_W"].
Proof. vm_compute. reflexivity. Qed.

Example nat_w_entries :
  option_map (fun sg => map (fun e => match e with EDef f _ _ => Some f | _ => None end) (sig_entries sg))
    (registered nat_w_run) = Some [Some "succ_W"; Some "zero_W"; Some "Nat_W"; Some "IsTrue"; None; None].
Proof. vm_compute. reflexivity. Qed.

Definition w_converts (names : list string) (t u : nterm) : bool :=
  match convert sg_nat_w w_fuel (build names t) (build names u) with ConvEqual _ => true | _ => false end.

(** The positions: Void below [false], Unit below [true]; ℕ_W unfolds to
    the W-type, and [succ_W] to a node labelled [true]. *)
Example nat_w_positions :
  w_converts [] (IsTrue NFalse) NVoid &&
  w_converts [] (IsTrue NTrue) NUnit &&
  w_converts [] Nat_W (W NBool IsTrue) &&
  w_converts ["n"] (succ_W "n") (sup NBool IsTrue NTrue (λ "_", "n")) &&
  negb (w_converts [] (IsTrue NFalse) NUnit) = true.
Proof. vm_compute. reflexivity. Qed.

(** [succ_W (succ_W zero_W)] is of type ℕ_W.  A node labelled [true] has
    the position [tt], one labelled [false] none.  Yet any function out of
    its positions makes a node [sup false f], not only the one of
    [zero_W]: the transfer of induction founders on this. *)
Example nat_w_typed :
  snd (run_check predicative sg_nat_w w_fuel [] (build [] (succ_W (succ_W zero_W))) (build [] Nat_W)) = Accepted tt /\
  snd (run_check predicative sg_nat_w w_fuel [] Tt (build [] (IsTrue NTrue))) = Accepted tt /\
  match snd (run_check predicative sg_nat_w w_fuel [] Tt (build [] (IsTrue NFalse))) with
  | Rejected _ => True
  | _ => False
  end /\
  snd (run_check predicative sg_nat_w w_fuel [] (build [] (sup NBool IsTrue NFalse (λ "_", zero_W))) (build [] Nat_W))
    = Accepted tt /\
  w_converts [] (sup NBool IsTrue NFalse (λ "_", zero_W)) zero_W = false.
Proof. split; [ | split; [ | split; [ | split]]]; vm_compute; trivial. Qed.

(** ** One step of the eliminator on [succ_W n]

    In the context [P : ℕ_W → Type₀], [m] the method, [n : ℕ_W], weak-head
    reduction takes three steps from [elim_W[0] Bool IsTrue P m (succ_W n)]:
    δ unfolds [succ_W] in the scrutinee, β exposes the node [sup true
    (λ_. n)], and ι contracts the spine to the method.  Its head [m] is a
    variable, so the head form is reached.  Normal order takes the same
    three steps, then contracts the β-redex under the binder of the
    hypothesis. *)

Definition elim_at (w : nterm) : nterm := elim_w NBool IsTrue "P" "m" w.

Definition nat_w_method : nterm :=
  Π "a" : NBool, Π "f" : (IsTrue "a" ~> Nat_W), (Π "b" : IsTrue "a", "P" ("f" "b")) ~>
  "P" (sup NBool IsTrue "a" "f").

Definition step_ctx : list (string * nterm) :=
  [("n", Nat_W); ("m", nat_w_method); ("P", Nat_W ~> Type@ 0)].

(** The terms before each weak-head step and the head form. *)
Fixpoint head_trace (fuel : nat) (t : term) : list term :=
  match fuel, head_step sg_nat_w t with
  | S fuel', Some u => t :: head_trace fuel' u
  | _, _ => [t]
  end.

(** The hypothesis of the node, for each of its positions, as ι gives it
    and after β. *)
Definition succ_hyp : nterm := λ "b", elim_at ((λ "_", "n") "b").
Definition succ_hyp' : nterm := λ "b", elim_at "n".

Definition succ_step : list nterm :=
  [elim_at (succ_W "n");
   elim_at ((λ "n", sup NBool IsTrue NTrue (λ "_", "n")) "n");
   elim_at (sup NBool IsTrue NTrue (λ "_", "n"));
   "m" NTrue (λ "_", "n") succ_hyp].

Example succ_w_step :
  head_trace w_fuel (term_in step_ctx (elim_at (succ_W "n"))) = map (term_in step_ctx) succ_step /\
  fst (normalize_trace sg_nat_w 4 (term_in step_ctx (elim_at (succ_W "n"))))
  = map (term_in step_ctx) (succ_step ++ ["m" NTrue (λ "_", "n") succ_hyp']).
Proof. split; vm_compute; reflexivity. Qed.

(** At the position [tt] of the node the hypothesis is the eliminator on
    [n], two β-steps away, where it stops: [n] is a variable. *)
Example succ_hyp_at_tt :
  head_trace w_fuel (term_in step_ctx (succ_hyp NTt)) =
  map (term_in step_ctx) [succ_hyp NTt; elim_at ((λ "_", "n") NTt); elim_at "n"].
Proof. vm_compute. reflexivity. Qed.

Definition w_check (g : list (string * nterm)) (t A : nterm) : answer unit :=
  snd (run_check predicative sg_nat_w w_fuel (in_ctx g) (term_in g t) (term_in g A)).

(** The left side checks against [P (succ_W n)].  The ι-reduct does not:
    its scrutinee [(λ_. n) b] is a β-redex whose λ is not annotated, and
    the bidirectional checker cannot infer it, although the declarative
    typing has the reduct.  After β the reduct checks against
    [P (succ_W n)], although the method gives [P (sup true (λ_. n))]; the
    hypothesis is a function from the positions Unit into [P n]. *)
Example succ_w_step_typed :
  w_check step_ctx (elim_at (succ_W "n")) ("P" (succ_W "n")) = Accepted tt /\
  w_check step_ctx ("m" NTrue (λ "_", "n") succ_hyp) ("P" (succ_W "n"))
  = Rejected (ECannotInfer (build ["b"; "n"; "m"; "P"] (λ "_", "n"))) /\
  w_check step_ctx ("m" NTrue (λ "_", "n") succ_hyp') ("P" (succ_W "n")) = Accepted tt /\
  w_check step_ctx succ_hyp' (NUnit ~> "P" "n") = Accepted tt.
Proof. split; [ | split; [ | split]]; vm_compute; reflexivity. Qed.

(** ** The recursor with a constant motive

      rec_W : Π(C : Type₀). C → (C → C) → ℕ_W → C
      rec_W C z s w := elim_W[0] Bool IsTrue (λ_. C) M w
      M := λa f h. elimBool (λc. (IsTrue c → C) → C) (λh. s (h tt)) (λ_. z) a h

    The hypothesis [h : IsTrue a → C] goes through the match on the label,
    so that it is [Unit → C] in the branch [true] and can be applied to
    [tt].  The motive ignores the tree: [P (sup false f) ≡ C ≡ P zero_W],
    so the branch [false] needs nothing about [f]. *)

Definition rec_W : nterm := NConst (Def "rec_W").

Definition rec_w_ty : nterm := Π "C" : Type@ 0, "C" ~> ("C" ~> "C") ~> Nat_W ~> "C".

Definition rec_w_method : nterm :=
  λ "a", λ "f", λ "h",
    NElimBool ((λ "c", (IsTrue "c" ~> "C") ~> "C") ∷ (NBool ~> Type@ 0))
      (λ "h", "s" ("h" NTt)) (λ "_", "z") "a" "h".

Definition rec_w_body : nterm :=
  λ "C", λ "z", λ "s", λ "w", elim_w NBool IsTrue (λ "_", "C") rec_w_method "w".

Definition rec_w_run : list (stage * list event) * registration :=
  define_checked predicative w_fuel sg_nat_w "rec_W" (build [] rec_w_ty) (build [] rec_w_body).

Definition sg_rec_w : signature := match registered rec_w_run with Some sg => sg | None => ∅ end.

Example rec_w_registered :
  map fst (fst rec_w_run) = [AtDefType "rec_W"; AtDefBody "rec_W"] /\
  option_map (fun sg => length (sig_entries sg)) (registered rec_w_run) = Some 7.
Proof. split; vm_compute; reflexivity. Qed.

(** Without the match carrying [h], [h tt] asks for [tt : IsTrue a] with
    the label [a] unknown. *)
Definition rec_w_direct : nterm :=
  λ "C", λ "z", λ "s", λ "w",
    elim_w NBool IsTrue (λ "_", "C")
      (λ "a", λ "f", λ "h", NElimBool ((λ "c", "C") ∷ (NBool ~> Type@ 0)) ("s" ("h" NTt)) "z" "a") "w".

Example rec_w_direct_refused :
  refusal (define_checked predicative w_fuel sg_nat_w "rec_W" (build [] rec_w_ty) (build [] rec_w_direct))
  = Some (RRejected (AtDefBody "rec_W")
            (EMismatch Tt (build ["h"; "f"; "a"; "w"; "s"; "z"; "C"] (IsTrue "a")) Unit)).
Proof. vm_compute. reflexivity. Qed.

(** *** Computation

    The equations of the recursor hold by conversion for an open [n]: the
    scrutinee [succ_W n] unfolds to a node, ι gives the method, the match
    on [true] passes the hypothesis to [s], and the hypothesis at [tt] is
    the recursor on [n]. *)

Definition rec_ctx : list (string * nterm) :=
  [("n", Nat_W); ("s", "C" ~> "C"); ("z", NVar "C"); ("C", Type@ 0)].

Definition rec_converts (g : list (string * nterm)) (t u : nterm) : bool :=
  match convert sg_rec_w w_fuel (term_in g t) (term_in g u) with ConvEqual _ => true | _ => false end.

Definition rec_checks (g : list (string * nterm)) (t A : nterm) : bool :=
  accepted (snd (run_check predicative sg_rec_w w_fuel (in_ctx g) (term_in g t) (term_in g A))).

Example rec_w_equations :
  rec_checks rec_ctx (rec_W "C" "z" "s" "n") "C" &&
  rec_converts rec_ctx (rec_W "C" "z" "s" zero_W) "z" &&
  rec_converts rec_ctx (rec_W "C" "z" "s" (succ_W "n")) ("s" (rec_W "C" "z" "s" "n")) &&
  negb (rec_converts rec_ctx (rec_W "C" "z" "s" (succ_W "n")) (rec_W "C" "z" "s" "n")) = true.
Proof. vm_compute. reflexivity. Qed.

(** On canonical terms: the parity of three is [true], twice one is two. *)
Definition three_W : nterm := succ_W (succ_W (succ_W zero_W)).
Definition parity_W (w : nterm) : nterm := rec_W NBool NFalse (λ "x", bnot "x") w.
Definition double_W (w : nterm) : nterm := rec_W Nat_W zero_W (λ "m", succ_W (succ_W "m")) w.

Example rec_w_computes :
  rec_checks [] (parity_W three_W) NBool &&
  rec_checks [] (double_W (succ_W zero_W)) Nat_W &&
  rec_converts [] (double_W (succ_W zero_W)) (succ_W (succ_W zero_W)) &&
  negb (rec_converts [] (double_W (succ_W zero_W)) (succ_W zero_W)) = true /\
  normalize sg_rec_w w_fuel (build [] (parity_W three_W)) = NormalForm BTrue.
Proof. split; vm_compute; reflexivity. Qed.

(** ** The rejected transfer of dependent induction

      ind_W : Π(P : ℕ_W → Type₀). P zero_W → (Πn:ℕ_W. P n → P (succ_W n)) → Πw:ℕ_W. P w
      ind_W P z s w := elim_W[0] Bool IsTrue P M w
      M := λa f h. elimBool (λc. Πf:IsTrue c → ℕ_W. (Πb:IsTrue c. P (f b)) → P (sup c f))
                     (λf h. s (f tt) (h tt)) (λf h. z) a f h

    The method matches on the label as that of [rec_W] does, now carrying
    the field [f] along with the hypothesis, since the motive mentions it.
    The definition is refused by conversion.  [elimBool] checks the branch
    [true] first: [s (f tt) (h tt)] has the type [P (succ_W (f tt))],
    that is [P (sup true (λ_. f tt))], against [P (sup true f)]; η for Π
    and Unit would identify [f] with [λ_. f tt], but this kernel has
    neither.  The branch [false], which the attempt does not reach, is
    refused on its own: [z : P zero_W] against [P (sup false f)] for an
    arbitrary [f : Void → ℕ_W].  There [f] and [λv. elimVoid _ v] differ,
    and η for Π leaves [f v] against [elimVoid _ v], two neutral terms of
    the type ℕ_W, to which η for Unit does not apply.

    This is the trace of one attempt, not a proof that the principle is
    underivable. *)

Definition ind_W : nterm := NConst (Def "ind_W").

Definition ind_w_ty : nterm :=
  Π "P" : (Nat_W ~> Type@ 0), "P" zero_W ~> (Π "n" : Nat_W, "P" "n" ~> "P" (succ_W "n")) ~>
  Π "w" : Nat_W, "P" "w".

(** The motive of the match on the label [c]. *)
Definition ind_motive (c : nterm) : nterm :=
  Π "f" : (IsTrue c ~> Nat_W), (Π "b" : IsTrue c, "P" ("f" "b")) ~> "P" (sup NBool IsTrue c "f").

Definition ind_true : nterm := λ "f", λ "h", "s" ("f" NTt) ("h" NTt).
Definition ind_false : nterm := λ "f", λ "h", "z".

Definition ind_w_method : nterm :=
  λ "a", λ "f", λ "h",
    NElimBool ((λ "c", ind_motive "c") ∷ (NBool ~> Type@ 0)) ind_true ind_false "a" "f" "h".

Definition ind_w_body : nterm :=
  λ "P", λ "z", λ "s", λ "w", elim_w NBool IsTrue "P" ind_w_method "w".

Definition ind_w_run : list (stage * list event) * registration :=
  define_checked predicative w_fuel sg_nat_w "ind_W" (build [] ind_w_ty) (build [] ind_w_body).

(** The names at the match, and inside a branch. *)
Definition match_names : list string := ["h"; "f"; "a"; "w"; "s"; "z"; "P"].
Definition branch_names : list string := "h" :: "f" :: match_names.

Definition ind_body_events : list event := nth 1 (map snd (fst ind_w_run)) [].

Definition unfolds (t : term) (ev : event) : bool :=
  match ev with EvUnfoldPi u _ _ _ => term_eqb u t | _ => false end.

(** The type checks, the body is refused in the branch [true].  Its trace
    ends with the type [P (succ_W (f tt))] of [s (f tt) (h tt)]; the
    failed conversion is the refusal, and the branch [false] is never
    unfolded. *)
Example ind_w_refused :
  map fst (fst ind_w_run) = [AtDefType "ind_W"; AtDefBody "ind_W"] /\
  refusal ind_w_run =
  Some (RRejected (AtDefBody "ind_W")
          (EMismatch (build branch_names ("s" ("f" NTt) ("h" NTt)))
             (build branch_names ("P" (sup NBool IsTrue NTrue "f")))
             (build branch_names ("P" (succ_W ("f" NTt)))))) /\
  match rev ind_body_events with
  | EvSubst _ u B :: _ =>
      term_eqb u (build branch_names ("h" NTt)) && term_eqb B (build branch_names ("P" (succ_W ("f" NTt))))
  | _ => false
  end &&
  existsb (unfolds (build match_names ind_true)) ind_body_events &&
  negb (existsb (unfolds (build match_names ind_false)) ind_body_events) = true.
Proof. split; [ | split]; vm_compute; reflexivity. Qed.

(** The branch [false] on its own, in the context of the method. *)
Definition method_ctx : list (string * nterm) :=
  [("s", Π "n" : Nat_W, "P" "n" ~> "P" (succ_W "n")); ("z", "P" zero_W); ("P", Nat_W ~> Type@ 0)].

Definition ind_false_run : list event * answer unit :=
  run_check predicative sg_nat_w w_fuel (in_ctx method_ctx)
    (term_in method_ctx ind_false) (term_in method_ctx (ind_motive NFalse)).

Example ind_false_refused :
  snd ind_false_run =
  Rejected (EMismatch (build (["h"; "f"] ++ map fst method_ctx) "z")
              (build (["h"; "f"] ++ map fst method_ctx) ("P" (sup NBool IsTrue NFalse "f")))
              (build (["h"; "f"] ++ map fst method_ctx) ("P" zero_W))).
Proof. vm_compute. reflexivity. Qed.

(** What conversion would need.  In the branch [true]: [succ_W (f tt)]
    is the node [sup true (λ_. f tt)], and [f ≡ λx. f x ≡ λ_. f tt] would
    take η for Π, then η for Unit at [x : Unit]; neither holds here. *)
Example ind_true_gap :
  w_converts branch_names (succ_W ("f" NTt)) (sup NBool IsTrue NTrue (λ "_", "f" NTt)) &&
  negb (w_converts branch_names (sup NBool IsTrue NTrue "f") (sup NBool IsTrue NTrue (λ "_", "f" NTt))) &&
  negb (w_converts branch_names "f" (λ "x", "f" "x")) &&
  negb (w_converts branch_names (λ "x", "f" "x") (λ "_", "f" NTt)) = true.
Proof. vm_compute. reflexivity. Qed.

(** In the branch [false]: [zero_W] is the node [sup false (λv. elimVoid _
    v)], and after η for Π the children [f v] and [elimVoid _ v] for
    [v : Void] remain apart, two neutral terms of the type ℕ_W. *)
Example ind_false_gap :
  w_converts branch_names zero_W (sup NBool IsTrue NFalse no_child) &&
  negb (w_converts branch_names "f" no_child) &&
  negb (w_converts ("v" :: branch_names) ("f" "v") (no_child "v")) = true.
Proof. vm_compute. reflexivity. Qed.
