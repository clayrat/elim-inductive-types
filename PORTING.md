# Porting log

Every definition or proof taken from another project is recorded here: source
repository, commit, paths, license and the changes made. Ported proofs are
re-checked by this project's build.

## Dependencies

| Dependency | Where | Pinned commit | Use |
|---|---|---|---|
| [pts-dependent-types](https://github.com/clayrat/pts-dependent-types) | `vendor/pts-dependent-types` (git submodule) | `821b16b` on the branch `inductive-types`, after `lecture-6` = `7e6282d` | The kernel of lecture 6, extended for this lecture: `Common`, `PTS` and `Configs`, built under the prefix `DepTypes`, and `SystemU/Looping`, `SystemU/Encodings` only for the observation type its printer prints; its PCF translation, MLTT examples and its own strictness-pcf submodule are not built. Unlike strictness-pcf in the kernel, this submodule is edited: Σ, constants and the signature extend the kernel's closed `term`, so they are committed to pts-dependent-types and the pin moves with them (see the README). |

## Ported files

None yet.

## Adapted proofs and code

| Here | Source | Commit | Changes |
|---|---|---|---|
| `Makefile`, `_CoqProject`, `.gitignore` | pts-dependent-types, the same files | `7e6282d` | the kernel's modules listed from the submodule, as the kernel lists those of strictness-pcf |
| `extraction/` (Makefile, dune, the shape of `main.ml` and `regress.ml`) | pts-dependent-types, `extraction/` | `7e6282d` | the same scheme of extraction and demos; the kernel's `pretty.ml` is copied unchanged into `generated/` at build time, and the extract keeps the module name `Deptypes` it expects |
