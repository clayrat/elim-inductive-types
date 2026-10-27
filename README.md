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
kernel's branch `inductive-types` (from `lecture-6`), committed as `821b16b`:
Σ, constants, signatures with classified descriptions, δ and ι by scheme,
with soundness of the checker proved for every signature, and the lecture-6
output unchanged against the tag. The recorded pin is `f8aa23c`, which adds
the shared conversions of the native reference (`reference/extracted.ml`) and
the interface the native algorithm 1 builds on. `.gitmodules` names the
branch, so `git submodule update --remote` follows it. The modules of this
repository hold their plan only.

| Component | Status |
|---|---|
| kernel built from the submodule; extraction with the kernel's printer | linked, smoke-tested |
| extraction and demos of algorithm 1 | `make demo` shows, in the order of the lecture, the descriptions, generated eliminators, methods and ι-rules of ℕ, lists, vectors, binary trees and W, the registration logs by stage with one ι-rule traced, the two refused declarations, `δ (mk δ) : Void` and the `Undecided` Bool diagonal in the bypass mode, Void/Unit/Bool against the primitives, `Unit_1` without cumulativity, and `double` under normal order; `make test` checks these outputs |
| extraction and demos of algorithm 2 | `make demo` goes on with the programs: each with its type, strategy, body and equations, its pattern variables named; the equations by conversion, as the redexes of the normal-order trace of each side, δ with the name of the constant (in full, with the terms, for `pow` and `f`); the history of ℕ (`Below`, `build`, `recBelow`) and of vectors; `half` refused directly and compiled through the history; `isEven` with `Unit_1`, `elimNat[2]` and `elimNat[1]`, `tt : isEven 4`, and the history with `Unit : Type₀` refused; `append`, the branch `nil` refused with addition on the second argument, in the names of its scope; the motive of `sumv`; the refusals of `g (pred n)`, Ackermann's equations and `len`, and Ackermann's function of higher order. Then W-types: `copy` in both strategies, `copy zero_W ≢ zero_W`, and the refused transfer of induction to ℕ_W with the trace of its body from the match on the label. `make test` checks these outputs, and that every step of these traces is a redex the printer names |
| Σ, constants, signature, δ, ι by scheme, extended soundness (in the kernel) | done on the kernel's branch `inductive-types` (`821b16b`); tested in its `MLTT/Pairs.v`, `MLTT/Constants.v` and `MLTT/Families.v` |
| Σ and constants in the kernel's native reference | done on the same branch; compared with the extract by the kernel's differential test |
| native algorithm 1 | `reference/elim_native.ml`: classification, generation and registration on the kernel's native reference; compared with the extract on classification answers, generated types and rules, and complete registration logs, over the lecture's declarations, every diagnostic, five specifications, fuel from 0 up, and 2778 enumerated constructors; `make test` runs it |
| declarations and classification of fields (strict positivity) | implemented in `Elim/Decl.v`; faithfulness and strict positivity proved; reproduces the kernel's hand-written descriptions of ℕ, `Vec`, `W` and `Tr`, classifies lists, binary trees and Void/Unit/Bool, rejects the two inadmissible declarations and gives every diagnostic |
| generator of eliminators | implemented in `Elim/Generate.v`: motive, methods, eliminator types and ι-rules as data; reproduces the kernel's hand-written `elimNat`, `elimVec`, `elimW`, `elimTr`; every generated rule is the kernel's contraction and both sides check against its type; read with the primitives, the types and rules of Void, Unit and Bool are those of lecture 6 |
| `declare_checked`, `define_checked`, `Unit_ℓ` | implemented in `Elim/Declare.v`: classification, freshness, the types of D and its constructors, levels of fields, then each instance in the four stages of the plan, its rules checked in the signature without active rules; a δ-constant checked without itself; every run of the checker logged with its stage. Soundness of all three registrations proved from the checker's. Declaring ℕ, `Vec`, `W` and `Tr` gives the kernel's hand-written signature, `double` the kernel's entry; in the bypass mode `δ (mk δ) : Void` is accepted and the Bool diagonal ends `Undecided` |
| `Below_D`, `build_D`, `recBelow_D` and `Unit_ℓ` | implemented in `Recursion/Below.v`: from a classified description and the level j of the motive, at the history level ℓ = max(i, j), the three δ-constants per pair (D, j), registered with `Unit_ℓ`, `elim_D[ℓ+1]` and `elim_D[ℓ]` by `ensure_below`; soundness proved from that of `define`. On open terms they compute to the formulas of the lecture for ℕ (at levels 0 and 1), `Vec`, binary trees, `W`, `Tr` and a family in `Type₁`; the primitive `Unit` in place of `Unit_1` is refused |
| case trees | implemented in `Recursion/CaseTree.v`: annotated functions with named case trees, and their elaboration into scopes and goals. A split of `z : D Δ θ̄`, or of a variable of the primitive Void, Unit or Bool, generalizes the indices, `z` and the dependent tail of the scope, and binds in each branch the fields with their hypotheses and the tail again, refined (splitting a constant `b : Bool` refines a constant `c : IsTrue b`); the values of the arguments (the left sides of the equations) and the paths of pattern variables follow. On `half`, `append`, a hypothesis on the length of a vector, W, binary trees and `Tr` every scope is a context the checker accepts and every right side without recursion checks against its goal; every diagnostic arises |
| `compile_checked` | implemented in `Recursion/Compile.v`: the motive of the recursion with Γ_P, through the history (`recBelow_D` with a step over the history) or directly (the root split by `elim_D[j]`, calls becoming hypotheses); every split by the instance at exactly the level of its motive, found by the checker, a split of Void, Unit or Bool by its primitive eliminator; every leaf reached through a split of the structural argument, so that its equation can hold by definition; calls replaced by accesses to the history, with the check of structural decrease; the output registered as a δ-constant checked without itself, and every defining equation checked by conversion. Soundness proved from that of `define` and of the conversion check |
| ℕ, lists, vectors, binary trees, W, ℕ_W; Void/Unit/Bool against the primitives | in `Data/`; ℕ_W as the δ-constants `IsTrue`, `Nat_W`, `zero_W`, `succ_W` over W in `Data/W.v`, with the positions `IsTrue false ≡ Void` and `IsTrue true ≡ Unit`, and one step of `elim_W[0]` on `succ_W n` (δ, β, ι to the head form; the ι-reduct checks only after one more β); the recursor `rec_W` with a constant motive, its equations on open `n` and computations on canonical terms; the transfer of dependent induction `ind_W`, refused by conversion in the branch `true` (`P (succ_W (f tt))` against `P (sup true f)`), the branch `false` refused on its own, and the conversions η for Π and Unit would supply, but not in the branch of zero |
| lecture programs and rejections | in `Programs/`: `+`, `pow` and `f` directly, their bodies the terms written by hand; `half` (with `half k` as `fst (snd t)`) and `isEven` (with `Unit_1`, `elimNat[2]`, `elimNat[1]`) through the history, `tt : isEven 4` accepted; `append` and `sumv`, whose hypothesis on the length enters the motive; refused: `half` without the history, the branch `nil` with addition on the second argument, `g (pred n)`, Ackermann's equations for either argument, a varying parameter, a changed parameter; Ackermann's function by higher-order structural recursion compiled; `copy` on W in both strategies, its call on the functional field `f b` as `h b` or `fst (t b)`, the identity only extensionally (`copy zero_W ≢ zero_W`, its child stuck on `elimVoid _ b`) |
| contracts | `Contracts.v`: 7 proved, axiom-free; open obligations stated for algorithm 1 and for algorithm 2 (the instances and the history typed declaratively and in the annotated kernel, and registrable, for every declaration and level whose names are free; for every tree the translation accepts, the body typed when the right sides have their goals and checked when they check, whatever the body of the function, the equations by definition, the checks passing with enough fuel when the right sides check; compiled functions total). Registrability rests on the annotated kernel, whose checker is complete, not on declarative typing. `Tests.v` checks the premise on the right sides of `half` and `append`, its failure on the branch `nil` of `append2`, and three trees against weaker premises: `beta`, typed declaratively and refused by the checker whatever the fuel, `peek`, typed only through the computation of its own call, and `clash`, named as the recursor of its own history, which the translation accepts and whose equations fail once the function shadows it; and `shadow`, a family indexed by a `Below_D_0` defined by hand, which its generated history would shadow, refused with the name taken |
| native algorithm 2 | `reference/recursion_native.ml`: the history, the elaboration of case trees and the compiler on the native algorithm 1, with the diagnostics of both in `reference/diagnostics_native.ml`; compared with the extract on the history of every description at three levels and its registration, whole elaborated trees with every diagnostic, translations, and complete compilation logs, over the lecture's programs and refusals, five specifications, fuel from 0 up, and 644 programs enumerated across the grammar of case trees; `make test` runs it |

## Building

Tested with Rocq 9.1.1, OCaml 4.14.2 and dune 3.

```sh
git submodule update --init   # the kernel at its pin; its own strictness-pcf is not needed
make                          # builds the needed kernel modules, then IndTypes
make demo                     # extracts and runs the lecture demos
make test                     # extraction regressions and the native differential test
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
printer compiles against it unchanged. `pretty_ind.ml` prints what
algorithms 1 and 2 add: descriptions, eliminator types with the motive named
P, ι-rules with the methods named after their constructors, the diagnostics,
stages and answers of classification, registration and compilation, the
equations of compiled functions with the names of their scopes
(`named_equations` of `Compile.v` reads both off one run of the translation), and
the redex each step of a normal-order trace contracts. `main.ml` runs the
demonstrations and `regress.ml` the tests.

## Stages

0. Skeleton: the submodule at `lecture-6`, the build, extraction, smoke tests.
   Done.
1. Kernel: Σ, constants, the signature, δ and ι by scheme, the extended
   `CheckSound`; the traces of lecture 6 unchanged against the tag; Σ and
   constants in the native reference. Done.
2. Algorithm 1: classification, generation, `declare_checked`; ℕ, lists,
   vectors, binary trees and Void/Unit/Bool, the two rejected declarations.
   Done: classification, generation and registration, with contracts,
   extraction and demos, and the native version with its differential
   test.
3. Algorithm 2: `Below`, case trees, `compile_checked`; `+`, `pow`, `f`,
   `half`, `isEven`, `append` and the rejections. Done: the history, the
   elaboration of case trees, `compile_checked` and the programs.
4. W-types: the declaration, ℕ_W, the rejected transfer of induction.
   Done: the declaration and its history, ℕ_W as δ-constants, one step of
   the eliminator, the recursor, the refused transfer with its trace, and
   `copy` compiled in both strategies.
5. Contracts, demonstrations, native reference and differential tests.
   Done: the extraction and demos of algorithm 2, its open obligations, and
   its native version with the differential test.

## Files

| File | What goes in it |
|------|-----------------|
| `Elim/Decl.v` | Raw declarations after Dybjer's schema and their classification into non-recursive and recursive fields: the strict positivity check, uniform parameters, levels of fields; the bypass mode for the negative demo. |
| `Diagnostics.v` | The stages of registration logs, the diagnostics of both algorithms (classification and registration, case trees and recursive calls) and the answers of a registration, below both algorithms, so that algorithm 2 depends on algorithm 1 and not the converse. |
| `Elim/Generate.v` | The motive, method and eliminator types of `elim_D[j]` and its ι-rules, from one left-to-right pass over the fields shared with the kernel's ι-scheme. |
| `Elim/Declare.v` | `declare_checked`: a declaration (classified, fresh, its types and the levels of its fields checked) and its instances, each in four stages through a temporary signature where its rules are not active; `define_checked` for δ-constants; `ensure_elim`, `ensure_unit` and `Unit_ℓ` for ℓ > 0; the bypass mode `declare_bypassing`; a log of every checker run by stage. `declare_ind_sound`, `declare_elim_sound`, `define_sound`: what a successful registration guarantees, in the judgments of the annotated kernel. |
| `Recursion/Below.v` | `Below_D`, `build_D`, `recBelow_D` from a description, at the history level ℓ = max(i, j), one triple per pair (D, j). |
| `Recursion/CaseTree.v` | Annotated functions: the structural argument, constant and varying arguments, the strategy (direct or through the history), named case trees; scopes, the generalization of a goal over a split, branches with fields, hypotheses and the refined tail, the paths of pattern variables, and the elaboration of a tree. |
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
| `Programs/Copy.v` | `copy` on W, a call on a functional recursive field, directly and through the history; on ℕ_W. |
| `Contracts.v` | The guarantees of the lecture: proved (classification faithful and strictly positive; registrations of declarations, instances, δ-constants and histories sound; compilations sound), checked on every output, and open: for algorithm 1 the completeness of the classification, the generated instances typed declaratively for every declaration and level, their registration succeeding with enough fuel, and the signatures built by registrations, compilations included, type-correct, normalizing and consistent; for algorithm 2 the history typed declaratively and registrable, the translation keeping the types of the right sides, the equations holding by definition, the checks of a compilation passing with enough fuel, and compiled functions total. |
| `Tests.v` | Tests of every algorithm: classification diagnostics, generated rules, registrations and their refusals, the history of every family. |

[`reference/`](reference/README.md) holds native versions of the lecture's
algorithms, both of them, compared with the extract. Ports from
sibling projects are recorded in [PORTING.md](PORTING.md).
