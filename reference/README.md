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

`elim_native.mli` is its interface. `data.ml` assembles the declarations of
`theories/Data` and `theories/Tests.v` independently with the kernel's
named builder: ℕ, lists, vectors over ℕ, binary trees, W-types, the family
`Tr`, Void/Unit/Bool, the declarations outside the grammar with the
diagonal of the bypass mode, and one declaration for every diagnostic.

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
the files here.

The differential test was checked against mutants of `elim_native.ml`: it
catches 52 of 53 single changes to classification, generation and
registration. The one it misses, making the rules active in the temporary
signature of an instance, is not observable: a rule is checked by
conversions on syntactically equal types or on ones that already arise in
the types of the constructors and of the eliminator, which are checked
before the instance exists.

Rocq's proofs do not apply to this hand-written code; the differential tests
detect discrepancies on the exercised inputs only. `Below`, `build` and
`recBelow`, case trees and the compiler of structural recursion will follow
with algorithm 2.
