# Inductive types, families and W-types over the PTS kernel

The executable companion to the lecture on inductive types, the sequel of
lecture 6 on pure type systems. It extends the checker of lecture 6 with Σ,
global constants and a signature, and builds two algorithms on top of it:

1. **Generation of dependent eliminators with a strict positivity check.**
   A declaration of an inductive family after Dybjer's schema is classified
   field by field; for each requested level of the motive the generator
   produces the type of the eliminator and its ι-rules, and
   `declare_checked` registers the instance only after the checker accepts
   the type and both sides of every ι-rule.
2. **Compilation of structural recursion through `Below`.** A recursive
   function with an explicit structural argument and a case tree is
   translated into a term with eliminators only; recursive calls become
   accesses to the history of results. `compile_checked` checks the output
   against the declared type and every defining equation by conversion.

The kernel checks no termination itself: it sees only eliminators. Strict
positivity is checked on the declaration, structural decrease on the
program. The lecture plan is [plan-inductive-types.md](plan-inductive-types.md);
the plan of the next lecture, on CoC, CIC, PCUIC and Prop, is
[plan-coc-cic-pcuic.md](plan-coc-cic-pcuic.md).

## The kernel and this repository

The kernel is [pts-dependent-types](https://github.com/clayrat/pts-dependent-types),
a git submodule at `vendor/pts-dependent-types`; the next lecture, on CoC,
CIC and PCUIC, builds on it too. Its tag `lecture-6` (`7e6282d`) is the
state the notes of lecture 6 cite: their traces and counts (2339 and 161
checker events for L₀,
about 35 thousand steps of `fact 3`).

The kernel's `term` is closed, and every function and proof matches on its
constructors, so Σ and constants cannot be added from outside. Unlike
strictness-pcf inside the kernel, this submodule is therefore edited: the
kernel changes are committed to pts-dependent-types after `lecture-6`, and
the pin here moves with them. With Σ and declarations switched off, the
kernel's `make demo` must print the same traces as at the tag.

| Kernel change (in the submodule) | Where |
|---|---|
| Σ: `Sigma A B`, `Pair a b`, `Fst p`, `Snd p`; formation by its own rule (`max` in the predicative table), pairs checked against Σ, projections synthesized; ι for projections, no η | `PTS/Syntax`, `Named`, `Reduction`, `NormalOrder`, `Eval`, `Typing`, `Bidir`, `Check` |
| `Const g` for types, constructors, eliminator instances `Elim D j` and δ-constants `Def f`; applications are ordinary `App` spines | `PTS/Syntax` and everything matching on `term`, `SubstLaws` |
| the signature: accepted declarations with their classified descriptions, eliminator instances with the flag of active ι-rules, δ-constants with checked types and bodies; a parameter of the checker, evaluator and conversion; a constant missing from it is rejected | new `PTS/Signature.v` |
| δ: a constant in head position unfolds by a normal-order step; conversion compares equal constants before unfolding; traces print constant names and show unfolding as a separate step | `Eval`, `NormalOrder`, `Check` |
| ι by one scheme for flagged instances, arguments built by the generator's pass; the scrutinee is evaluated first; partial spines and neutral scrutinees stay neutral | `Eval` (`contract`) |
| Σ and declarations switched by fields of the table, like `spec_prim`: on in the predicative table, off in U⁻; the λC and CIC tables of the next lecture set them on the same checker | `PTS/Spec`, `Configs/Predicative` |
| soundness of the extended checker and conversion | `PTS/CheckSound` |
| printing and the native kernel | `extraction/pretty.ml`, `reference/pts_native.ml` |

Void, Unit and Bool stay primitive, and there is no cumulativity and no
universe polymorphism: an instance's level is part of its name.

## Status

The skeleton is in place, and the kernel extension of stage 1 is done on the
kernel's branch `inductive-types` (from `lecture-6`), committed as `821b16b`,
the recorded pin: Σ, constants, signatures with classified descriptions, δ
and ι by scheme, with soundness of the checker proved for every signature,
and the lecture-6 output unchanged against the tag. `.gitmodules` names the
branch, so `git submodule update --remote` follows it. The modules of this
repository hold their plan only.

| Component | Status |
|---|---|
| kernel built from the submodule; extraction with the kernel's printer | linked, smoke-tested |
| Σ, constants, signature, δ, ι by scheme, extended soundness (in the kernel) | done on the kernel's branch `inductive-types` (`821b16b`); tested in its `MLTT/Pairs.v`, `MLTT/Constants.v` and `MLTT/Families.v` |
| Σ and constants in the kernel's native reference | done on the same branch; compared with the extract by the kernel's differential test |
| declarations and classification of fields (strict positivity) | implemented in `Elim/Decl.v`; faithfulness and strict positivity proved; reproduces the kernel's hand-written descriptions of ℕ, `Vec`, `W` and `Tr`, classifies lists, binary trees and Void/Unit/Bool, rejects the two inadmissible declarations and gives every diagnostic |
| generator of eliminators | implemented in `Elim/Generate.v`: motive, methods, eliminator types and ι-rules as data; reproduces the kernel's hand-written `elimNat`, `elimVec`, `elimW`, `elimTr`; every generated rule is the kernel's contraction and both sides check against its type; read with the primitives, the types and rules of Void, Unit and Bool are those of lecture 6 |
| `declare_checked`, `define_checked`, `Unit_ℓ` | implemented in `Elim/Declare.v`: classification, freshness, the types of D and its constructors, levels of fields, then each instance in the four stages of the plan, its rules checked in the signature without active rules; a δ-constant checked without itself; every run of the checker logged with its stage. Soundness of all three registrations proved from the checker's. Declaring ℕ, `Vec`, `W` and `Tr` gives the kernel's hand-written signature, `double` the kernel's entry; in the bypass mode `δ (mk δ) : Void` is accepted and the Bool diagonal ends `Undecided` |
| `Below_D`, `build_D`, `recBelow_D` and `Unit_ℓ` | planned |
| case trees and `compile_checked` | planned |
| ℕ, lists, vectors, binary trees, W, ℕ_W; Void/Unit/Bool against the primitives | planned |
| lecture programs and rejections | planned |
| contracts, demonstrations, native reference and differential tests | planned |

## Building

Tested with Rocq 9.1.1, OCaml 4.14.2 and dune 3.

```sh
git submodule update --init   # the kernel at its pin; its own strictness-pcf is not needed
make                          # builds the needed kernel modules, then IndTypes
make demo                     # extracts and runs the lecture demos
make test                     # extraction regressions
make assumptions              # every proved contract is axiom-free
make check                    # the Rocq build, the axiom check and the OCaml tests
make clean
```

`_CoqProject` maps `vendor/pts-dependent-types/theories` to `DepTypes` and
`theories/` to `IndTypes`. Only the kernel modules the lecture needs are
built (`Common`, `PTS`, `Configs`, and `SystemU/Looping`, `SystemU/Encodings`
for the observations the kernel's printer prints), so the kernel's PCF
translation and its strictness-pcf dependency are not required.

`extraction/Extract.v` writes `extraction/generated/deptypes.ml`, and make
copies the kernel's `pretty.ml` next to it; both are rebuilt and never
edited by hand. The extract keeps the kernel's module name `Deptypes`, so the
printer compiles against it unchanged. `main.ml` runs the demonstrations and
`regress.ml` the tests.

## Stages

0. Skeleton: the submodule at `lecture-6`, the build, extraction, smoke tests.
   Done.
1. Kernel: Σ, constants, the signature, δ and ι by scheme, the extended
   `CheckSound`; the traces of lecture 6 unchanged against the tag; Σ and
   constants in the native reference. Done.
2. Algorithm 1: classification, generation, `declare_checked`; ℕ, lists,
   vectors, binary trees and Void/Unit/Bool, the two rejected declarations.
   Done: classification, generation and registration.
3. Algorithm 2: `Below`, case trees, `compile_checked`; `+`, `pow`, `f`,
   `half`, `isEven`, `append` and the rejections.
4. W-types: the declaration, ℕ_W, the rejected transfer of induction.
5. Contracts, demonstrations, native reference and differential tests.

## Files

| File | What goes in it |
|------|-----------------|
| `Elim/Decl.v` | Raw declarations after Dybjer's schema and their classification into non-recursive and recursive fields: the strict positivity check, uniform parameters, levels of fields; the bypass mode for the negative demo. |
| `Elim/Generate.v` | The motive, method and eliminator types of `elim_D[j]` and its ι-rules, from one left-to-right pass over the fields shared with the kernel's ι-scheme. |
| `Elim/Declare.v` | `declare_checked`: a declaration (classified, fresh, its types and the levels of its fields checked) and its instances, each in four stages through a temporary signature where its rules are not active; `define_checked` for δ-constants; `ensure_elim`, `ensure_unit` and `Unit_ℓ` for ℓ > 0; the bypass mode `declare_bypassing`; a log of every checker run by stage. `declare_ind_sound`, `declare_elim_sound`, `define_sound`: what a successful registration guarantees, in the judgments of the annotated kernel. |
| `Recursion/Below.v` | `Below_D`, `build_D`, `recBelow_D` from a description, at the history level ℓ = max(i, j), one triple per pair (D, j). |
| `Recursion/CaseTree.v` | Annotated functions: the structural argument, constant and varying arguments, case trees, paths of pattern variables. |
| `Recursion/Compile.v` | The motive Γ_P, the translation of splits and recursive calls, `compile_checked` with the defining equations by conversion. |
| `Data/Sigma.v` | Σ: formation, the dependent `snd`, `A × B`, `Σn:ℕ. Vec A n`. |
| `Data/Primitives.v` | Void, Unit and Bool as declarations, against the primitives of lecture 6. |
| `Data/Nat.v` | ℕ as the first declaration; instances at several levels. |
| `Data/Lists.v` | Lists and vectors: parameters against indices. |
| `Data/Tree.v` | Binary trees: the order `left, ih_left, right, ih_right`. |
| `Data/Positivity.v` | The negative and the non-strictly positive field; `δ (mk δ) : Void` in the bypass mode, `Undecided` for the Bool variant. |
| `Data/W.v` | W-types, ℕ_W, the rejected transfer of dependent induction. |
| `Programs/Direct.v` | `+`, `pow` and `f` by the direct translation. |
| `Programs/Half.v` | `half` and `isEven` through the history; `Unit_1` against `Unit : Type₀`. |
| `Programs/Append.v` | `append`; the branch `nil` rejected with addition on the second argument; generalization in a dependent split of a vector. |
| `Programs/Rejected.v` | `g (succ n) = g (pred n)`, Ackermann's function, non-uniform recursion. |
| `Contracts.v` | The guarantees of the lecture: proved (classification faithful and strictly positive; registrations of declarations, instances and δ-constants sound), checked on every output, and open: for algorithm 1 the completeness of the classification, the generated instances typed declaratively for every declaration and level, their registration succeeding with enough fuel, and the signatures built by registrations type-correct, normalizing and consistent. |
| `Tests.v` | Tests of every algorithm; for now, that the kernel is linked. |

[`reference/`](reference/README.md) will hold native versions of the
lecture's algorithms. Ports from sibling projects are recorded in
[PORTING.md](PORTING.md).
