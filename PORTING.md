# Porting log

Every definition or proof taken from another project is recorded here: source
repository, commit, paths, license and the changes made. Ported proofs are
re-checked by this project's build.

## Dependencies

| Dependency | Where | Pinned commit | Use |
|---|---|---|---|
| [pts-dependent-types](https://github.com/clayrat/pts-dependent-types) | `vendor/pts-dependent-types` (git submodule) | On the branch `cic` for lecture 8, after `lecture-7` = `fd7f98a` on the branch `inductive-types` (the extension `821b16b`, the shared conversions of `reference/` `f8aa23c`, then the traced combinators, `sig_add_entries` and `lams` of the native interface), itself after `lecture-6` = `7e6282d`. On `cic`: `0abeedf`, the kernel's contracts split into `PTS/Contracts.v`; `1e61d9c`, the sort Prop with `predicative_prop` and the table `coc`; `9cf06af`, instances `Elim D s` named by the sort of their motive, the sort and the category of elimination of a description, `allows_elimination`; `1cf0fa3`, `match` and `fix` in every layer of the kernel with `eval_src`, call-by-value evaluation; `07268dd`, the guard of fix | The kernel of lecture 6, extended for this lecture: `Common`, `PTS` and `Configs`, built under the prefix `DepTypes`, and `SystemU/Looping`, `SystemU/Encodings` only for the observation type its printer prints; its PCF translation, MLTT examples and its own strictness-pcf submodule are not built. Unlike strictness-pcf in the kernel, this submodule is edited: Σ, constants and the signature extend the kernel's closed `term`, so they are committed to pts-dependent-types and the pin moves with them (see the README). |

## Ported files

None yet.

## Adapted proofs and code

| Here | Source | Commit | Changes |
|---|---|---|---|
| `Makefile`, `_CoqProject`, `.gitignore` | pts-dependent-types, the same files | `7e6282d` | the kernel's modules listed from the submodule, as the kernel lists those of strictness-pcf |
| `extraction/` (Makefile, dune, the shape of `main.ml` and `regress.ml`) | pts-dependent-types, `extraction/` | `7e6282d` | the same scheme of extraction and demos; the kernel's `pretty.ml` is copied unchanged into `generated/` at build time, and the extract keeps the module name `Deptypes` it expects; `pretty_ind.ml` is new and builds on it |
| `reference/` (Makefile, the shape of `diff.ml`) | pts-dependent-types, `reference/` | `f8aa23c` | the kernel's `pts_native`, named builder, hand-written signatures and `extracted.ml` are copied unchanged into `_build` at test time; `telescope_native.ml`, `method_layout_native.ml`, `diagnostics_native.ml`, `common_native.ml`, `registration_native.ml`, `elim_native.ml`, `recursion_native.ml`, `data.ml`, `programs.ml`, the conversions of both algorithms in `conversions.ml`, the shared comparisons and runs of `test_support.ml`, the suites of `diff.ml` and `diff_recursion.ml` and `main.ml` are new |
