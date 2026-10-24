(** * [compile_checked]: structural recursion through [Below]

    The translation of algorithm 2, from an annotated function
    (Recursion.CaseTree) to a term with eliminators and without the
    original recursive calls:
    1. the history [Below_D] of the structural argument's type, at the
       level of the motive's result (Recursion.Below);
    2. the motive [P θ̄ x := Π(Γ_P). T]: Γ_P holds the varying arguments
       and those whose types depend on θ̄ or x, whatever their mark,
       closed under dependency and built once in dependency order; the
       other constant arguments stay outside.  An argument in the
       parameters Δ must be constant: changing one, such as A in a
       recursion on [List A], is non-uniform recursion and is rejected;
    3. the case splits: the motive of a split on [z : D Δ θ̄] abstracts
       the indices, z itself and under Π the dependent tail of the
       context (the history, the arguments and hypotheses depending on
       the indices or on z, constant ones included), which the branches
       reintroduce after substituting the constructor and its indices;
    4. the recursive calls: a call on a variable with a path of length at
       least 1 becomes the access to its result in the history, applied
       to the arguments of Γ_P in the order of the motive.  With no such
       access the definition is rejected: this is the check of structural
       decrease, a syntactic one.

    The direct translation, where every call is on an immediate subterm
    and becomes the induction hypothesis, is the special case.

    The checked entry point returns an output only if the checker accepts
    it against the declared type, without [fix] and without new
    primitives; it is registered as a δ-constant whose body does not
    mention it, so totality follows from the normalization of the kernel.
    Every defining equation is then checked by conversion with open
    pattern variables, e.g. [half (succ (succ n)) ≡ succ (half n)]: the
    equations hold by definition, unlike with well-founded recursion.

    Planned: Γ_P, the translation of splits and calls, [compile_checked]. *)

From DepTypes.PTS Require Import Syntax Check.
From IndTypes.Elim Require Import Decl Declare.
From IndTypes.Recursion Require Import Below CaseTree.
