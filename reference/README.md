# Native OCaml reference

Planned, as in the kernel's `reference/`: hand-written, readable OCaml
versions of the lecture's algorithms, compared with the extract by
differential tests on complete answers and traces:

- the classification of fields and the generator of eliminators;
- `Below`, `build` and `recBelow` by description;
- case trees and the compiler of structural recursion.

They run on the kernel's native reference,
`vendor/pts-dependent-types/reference/pts_native.ml`, once it is extended
with Σ, constants and the signature on the kernel side. Rocq's proofs do not
apply to this hand-written code; the differential tests detect discrepancies
on the exercised inputs only.
