# Lean proofs of optimal packings

Machine-checked **optimality** results for catalogue records: the record's container is proven to be the
smallest possible, not only feasible. (The feasibility of 532 records is verified separately in
`docs/research-2026-10-16-generalization/formal`.) Same Lean toolchain and Mathlib revision as that project.

```
lake exe cache get && lake build && lake env lean Axioms.lean
```

| Module | Content |
|---|---|
| `PackingOptimality/Basic.lean` | Packings of congruent convex bodies (any rigid motion, disjoint interiors) in any finite-dimensional Euclidean space; affine isometries preserve volume; the **volume bound** `n · vol K ≤ |s|^d · vol C`; the self-packing corollary `n ≤ |s|^d`; restriction `s(m) ≤ s(n)` for `m ≤ n`; the **common-point lemma** (if every copy inside `s • C` contains a fixed point in its interior, no two copies fit). |
| `PackingOptimality/Cubes.lean` | **Cubes in a cube**, every dimension `d ≥ 1` and every `k ≥ 1`: `k^d` unit cubes need side exactly `k` (`cubes_in_cube_optimal`; grid upper bound, volume lower bound). Catalogue instances `cubincub_n08`, `cubincub_n27`, `cubincub_n64`, `c8inc8_n16`, `hc5inhc5_n32`. The plateau `s(n) = 2` for `2 ≤ n ≤ 2^d`, conditional on the cube centre lemma (`cube_plateau_of_centre_lemma`). |

`Axioms.lean` prints the axioms of every main theorem; CI (`.github/workflows/lean-optimality.yml`)
fails unless all of them depend only on `propext`, `Classical.choice` and `Quot.sound`.

Status of every low-n record: [`docs/OPTIMALITY.md`](../docs/OPTIMALITY.md).
