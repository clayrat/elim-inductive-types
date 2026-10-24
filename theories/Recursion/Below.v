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
    [Unit_ℓ], a single component is the component itself.  For ℕ:

      Below P zero     = Unit_j
      Below P (succ n) = P n × Below P n

    - [Below_D] by large elimination through [elim_D[ℓ+1]];
    - [build_D : Πθ̄ x. P θ̄ x × Below_D P θ̄ x] through [elim_D[ℓ]]: the
      hypothesis of a recursive field has exactly the type of its
      component, so the history is the tuple of hypotheses;
    - [recBelow_D step] projects the result out of [build_D].

    No new primitive of recursion appears.  All three are δ-constants,
    one triple per pair (D, j): ℓ alone does not determine the type of
    [P].  Without cumulativity [Unit : Type₀] does not stand for [Unit_ℓ]
    at ℓ > 0, which the history of [isEven] checks (Programs.Half).

    Planned: the three constructions from a classified description, and
    the instances [Unit_ℓ], [elim_D[ℓ+1]] and [elim_D[ℓ]] they need. *)

From DepTypes.PTS Require Import Syntax.
From IndTypes.Elim Require Import Decl Generate Declare.
