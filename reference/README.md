# Native OCaml reference

Hand-written, readable OCaml versions of the lecture's algorithms, as in the
kernel's `reference/`, compared with the Rocq extract by differential tests
on complete answers and logs. They run on the kernel's native reference,
`vendor/pts-dependent-types/reference/pts_native.ml`, with its signatures,
δ and ι by the scheme of descriptions.

`elim_native.ml` is algorithm 1, in three parts following `Elim/Decl.v`,
`Elim/Generate.v` and `Elim/Declare.v`:

- the classification of raw declarations: the closedness of parameters,
  indices and constructors, D outside its own parameters and indices,
  non-recursive and recursive fields with uniform parameters and indices
  free of D, a diagnostic by where D occurs (negative, nested, not strictly
  positive), duplicate constructors, and the bypass mode of the negative
  demonstration;
- the motive, the methods with the hypothesis right after each recursive
  field, the eliminator type of `elim_D[j]`, and the ι-rules as data, their
  right sides built by the native kernel's own `method_args`;
- registration: a declaration with the types of D and its constructors and
  the levels of the fields, each instance in the four stages of the plan
  with its rules checked where it has no active rules, δ-constants checked
  without themselves, `Unit_ℓ`, and the bypass mode. Every checker run goes
  to the log with its stage, as the native checker keeps its events in a
  queue; `run` returns the log with the answer.

`recursion_native.ml` is algorithm 2, in three parts following
`Recursion/Below.v`, `Recursion/CaseTree.v` and `Recursion/Compile.v`:

- the history: `Below_D`, `build_D` and `recBelow_D` of a description for
  motives in `Type_j` at the level ℓ = max i j, with the binders of a
  method as the generator lays them out, tuples nested to the right with
  `Unit_ℓ` when empty, and their registration with `Unit_ℓ` and the two
  instances they need;
- the elaboration of case trees: scopes with named, replaced and
  compiler binders, the generalization of a split over the indices, the
  variable and the dependent tail, the branches with their fields,
  hypotheses and the tail bound again, the paths of pattern variables,
  splits of Void, Unit and Bool, and every diagnostic;
- the compiler: the motive of the recursion with the varying arguments in
  its tail, the direct translation and the one through the history, the
  calls on subterms as hypotheses or accesses to the history, the
  diagnostics of calls, the instances the motives need, and the
  registration of the function with its equations checked by conversion.

It runs on the native algorithm 1, whose registrar it shares: one log
holds the stages of both. The stages, diagnostics and answers of both
algorithms are in `diagnostics_native.ml`, as in `theories/Diagnostics.v`,
and `elim_native` re-exports them. Natural-number subtraction is written
`-!`: as in Rocq, it stops at 0.

`elim_native.mli` and `recursion_native.mli` are the interfaces.
`data.ml` assembles the declarations of
`theories/Data` and `theories/Tests.v` independently with the kernel's
named builder: ℕ, lists, vectors over ℕ, binary trees, W-types, the family
`Tr`, Void/Unit/Bool, the declarations outside the grammar with the
diagonal of the bypass mode, and one declaration for every diagnostic.
`programs.ml` assembles the programs of `theories/Programs` and the case
trees of `theories/Tests.v` the same way: `+`, `pow`, `f`, `half`,
`isEven`, `append`, `plus2`, `sumv`, `g`, Ackermann's function in both
forms, `len`, `copy`, the trees of every diagnostic of elaboration and the
splits of the primitive types; and, beyond those tests, a field named like
an argument, varying arguments that the tail takes through one another,
and a family `Two` with two indices.

`diff.ml` compares the native version with the extract:

- the declarations of `data.ml` with the extracted ones, where those exist;
- the answers of classification in both modes, and for every description
  its motives, methods, eliminator types and ι-rules at levels 0, 1 and 2;
- registrations as scripts of steps (declarations, instances, `ensure_elim`,
  δ-constants, `Unit_ℓ`) run by both sides from the same signature: the
  complete log, every stage with its checker events, and the answer. The
  scripts cover the families and their refusals, the diagonal in the
  bypass mode and what checks in its signature, every diagnostic, the five
  specifications of the kernel, and fuel from 0 up, with a vector indexed
  by a β-redex and constants whose types are redexes so that every
  `NoFuelAt` and `RNotAType` path is reached;
- `check_rule` on the rule of `succ` and on the rule with its hypothesis
  dropped, in the signature where the instance has no active rules;
- 2778 declarations of a family `E (A : Type₀) : Nat → Type₀` with one
  enumerated constructor: up to two fields drawn from a pool across the
  grammar and outside it, and a result from another pool; each is
  classified, generated and registered over ℕ.

`diff_recursion.ml` compares algorithm 2, with the conversions of
`diff.ml`:

- the programs of `programs.ml` with the extracted ones;
- for every description of `data.ml`, `Unit_1` and a family of level 1,
  at levels 0, 1 and 2: the level of the history, its names, and the
  types and bodies of `Below`, `build` and `recBelow`; their
  registration from several signatures, again and at several levels, an
  undeclared family, the five specifications and fuel from 0 up;
- `start` and the elaboration of every tree of `programs.ml`, the whole
  elaborated tree with its scopes, goals, values of the arguments,
  splits and generalizations, with the tail and the tags of the root
  where the compiler sets them, and every diagnostic;
- the translation with its elaborated tree, and compilations as runs of
  several functions from the same signature: the complete log, every
  stage with its checker events and every equation with its common
  normal form, and the answer. They cover the programs of the lecture and
  their refusals, a history reused, the specifications and fuel from 0
  up;
- programs enumerated across the grammar of case trees over ℕ, vectors,
  binary trees and W-types: one split or two, with leaves drawn from a
  pool for each branch (calls on fields and deeper subterms, on the
  structural argument, on terms that are no subterms, with an index or a
  constant changed, partial calls, names out of scope, ill-typed sides),
  each strategy and the extra argument constant or varying. Each is
  elaborated and compiled; about a third register, the others are refused
  by every diagnostic of calls, by the checker or at the root.

The native side also meets the kernel's hand-written terms: the
descriptions of ℕ, `Vec`, `W` and `Tr`, their eliminator types, the kernel's
contraction of every generated rule to its right side, and the signatures
of ℕ, `double` and the families, which registration rebuilds entry by entry.

From the repository root:

```sh
make -C reference test
# or: make test   (also runs the extraction's printer regressions)
```

The Makefile copies the extract and the kernel's `pts_native`, the named
builder, the hand-written signatures and `extracted.ml` (the conversions of
the kernel's syntax to the extract's) into `_build`, and compiles them with
the files here into one test, which prints a line for each algorithm.

The differential test was checked against mutants of `elim_native.ml`: it
catches 52 of 53 single changes to classification, generation and
registration. The one it misses, making the rules active in the temporary
signature of an instance, is not observable: a rule is checked by
conversions on syntactically equal types or on ones that already arise in
the types of the constructors and of the eliminator, which are checked
before the instance exists.

The test of algorithm 2 was checked the same way, against 60 single
changes to the history, the elaboration and the compiler in
`recursion_native.ml`: it catches 59. Four were missed at first and led
to the programs of `programs.ml` beyond the tests of Rocq: a field named
like an argument, a varying type with an argument of it, so that the tail
grows through a binder of the tail and the goal mentions it, and a family
with two indices. The one it misses, refusing a call whose structural
argument is the innermost binder of its leaf, is not observable: a
subterm is a recursive field or lies below one, the hypothesis of a
recursive field is bound right after it, and the tail after the fields,
so no subterm is ever the innermost binder.

Rocq's proofs do not apply to this hand-written code; the differential tests
detect discrepancies on the exercised inputs only.
