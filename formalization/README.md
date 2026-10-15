# Formalizing *Integer Cantor Sets: Arithmetic Combinatorial Properties*

A Lean 4 / Mathlib formalization of the paper in the parent directory, with a
[leanblueprint](https://github.com/PatrickMassot/leanblueprint)-style blueprint.

## Status

The project **builds and contains no `sorry`**. Chapters 2 and 3 — everything
the blueprint lists as in scope so far — are complete.

- **Chapter 2 is complete**: `Structure.lean` proves **Proposition 2.5**,
  the enumeration theorem (`thm:enum-bij`, `lem:enum-block`), so `enum` is the
  increasing enumeration of `C(b,D)`, together with the initial-segment,
  growth and divisibility lemmas that Chapters 4–7 rest on.
- **Chapter 3 is complete**: `VanDerCorput.lean` proves **Proposition 3.3**
  (`thm:logSavings`), `τ(C,N) ≤ log b / log N` for `N ≥ 2`, and its
  intersective counterpart `thm:logSavings-intersective`,
  `I(C,N) ≤ 2 log b / log N` for `N ≥ b`.

The remaining blueprint chapters (4–9) have no Lean statements yet; four of
their results are blocked on material absent from Mathlib (see below).

| | |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.35.0` |
| Mathlib | pinned at tag `v4.35.0` |
| Lean declarations | 14 definitions/structures, 56 theorem statements |
| Proved | 56 (all of them) |
| Blueprint items | 65 (20 definitions, 45 results), 8 marked blocked |
| `sorry` | 0 |

Every theorem in the project depends only on `propext`, `Classical.choice`
and `Quot.sound`; in particular `IntegerCantorSet.range_enum`,
`IntegerCantorSet.enum_block`, `IntegerCantorSet.vdcConst_cantorSet_le`,
`IntegerCantorSet.intersectiveConst_cantorSet_le`,
`IntegerCantorSet.isIntersective_cantorSet` and
`IntegerCantorSet.exists_dvd_of_isIntersective`.

Proved so far:

- Chapter 2, the digit substitution: `zero_mem_cantorSet`, `digitOf_zero`,
  `digitOf_mem`, `digitOf_lt`, `digitOf_strictMonoOn`, `digitOf_ne_zero`,
  `exists_digitOf_eq`.
- Chapter 2, the recursion for `enum`: `enum_zero`, `enum_of_lt_card`,
  `enum_mul_add`, `enum_div_mod`.
- Chapter 2, the enumeration theorem (Proposition 2.5): `digits_enum`,
  `enum_mem_cantorSet`, `enum_strictMono`, `range_enum`, `enum_block`,
  `enum_lt_pow`, `pow_le_enum`, `enum_image_Iio`, `sumDigits_mul_add`,
  `sumDigits_pow_mul_add`, `sumDigits_enum_block`.
- Chapter 2, divisibility: `dvd_ofDigits`, `stepSize_dvd`,
  `stepSize_dvd_sumDigits`, `modEq_sumDigits`.
- Chapter 3, intersectivity: `le_maxAvoiding`, `maxAvoiding_le`,
  `maxAvoiding_subadditive`.
- Chapter 3, the van der Corput constant: `admissible_one`,
  `integral_cos_two_pi_mul`, `integral_cosPoly`, `coeff_nonneg`,
  `vdcConst_nonneg`, `vdcConst_le`, `vdcConst_le_one`, `cosPoly_truncate`,
  `vdcConst_antitone`.
- Chapter 3, the two elementary principles: `card_le_of_differences_mem`
  (translate packing), `sum_sum_cos_sub`, `vdcConst_le_of_differences_mem`
  (Fejér kernel).
- Chapter 3, the tower: `tower_zero`, `tower_add`, `tower_succ`, `tower_pos`,
  `tower_lt_tower`, `ofDigits_replicate`, `ofDigits_replicate_zero`,
  `digits_pow_mul_tower`, `tower_sub_mem`, `tower_lt`.
- Chapter 3, Proposition 3.3 and its intersective counterpart:
  `vdcConst_cantorSet_le`, `isVdC_cantorSet`,
  `intersectiveConst_cantorSet_le`, `isIntersective_cantorSet`,
  `exists_dvd_of_isIntersective`.

## Layout

```
lakefile.toml, lean-toolchain     Lean project
IntegerCantorSets/Defs.lean       Chapter 2 definitions
IntegerCantorSets/Structure.lean  Chapter 2: the enumeration theorem
IntegerCantorSets/VanDerCorput.lean  Chapter 3: intersective / vdC
blueprint/src/content.tex         The blueprint (all 8 chapters)
blueprint/print/print.pdf         Readable PDF, builds with plain pdflatex
```

## Building

```bash
lake exe cache get && lake build
```

The blueprint PDF:

```bash
cd blueprint/src && pdflatex -output-directory=../print print.tex
```

This uses `blueprint-fallback.sty`, a stand-in that renders the `\lean`,
`\uses` and `\notready` annotations inline so the document reads without extra
tooling. For the real dependency graph and web version, install the tooling and
switch `print.tex` to `\usepackage[showmore, dep_graph]{blueprint}`:

```bash
pip install leanblueprint && leanblueprint web
```

## Where to start

The blueprint's Chapter 1 argues for this order.

1. ~~**`thm:logSavings`**~~ — done. `τ(C,N) ≤ log b / log N`, Proposition 3.3
   of the paper, with its Fejér kernel (`lem:fejer`), the tower lemmas, and
   `vdcConst_antitone`.
2. ~~**`lem:packing` and `thm:logSavings-intersective`**~~ — done. The
   intersectivity half of Chapter 3, by translate packing, together with
   `lem:intersective-converges` (Fekete) and `lem:zero-necessary`. Chapter 3
   now has no `sorry` left.
3. ~~**`thm:enum-bij` and `lem:enum-block`**~~ — done. Proposition 2.5, on
   which everything in Chapters 4–7 rests. `digits_enum` is the
   `Nat.digits_ofDigits` application whose non-zero-leading-digit hypothesis
   is exactly where `0 ∈ D` enters; the order and block statements are then
   derived from the single-digit recursion `enum_mul_add`
   (`lem:enum-recursion`), which keeps the inductions free of any reasoning
   about digit lists.
4. **`lem:noCarry`** — additive energy is multiplicative over digits. Finitary
   and independent of everything else, so it parallelizes. This is now the
   natural next target: Chapter 2 no longer blocks anything.

## Known obstructions

Four results in the paper are blocked on material absent from Mathlib, and are
marked `\notready` in the blueprint:

- **Furstenberg correspondence principle** and upper Banach density
  (Chapter 7). A prerequisite project in its own right.
- **Joint spectral measure for commuting unitaries** on `𝕋²` (Chapter 8).
  Mathlib has the continuous functional calculus but not the
  projection-valued measure. The scalar shadow of the theorem — convergence of
  the exponential sums — is `thm:irrational` and *is* in scope.
- **Aistleitner–Larcher–Lewko** (Chapter 9). Recorded as a hypothesis; the
  reduction to it is formalizable, the theorem itself is not a realistic
  target.
- **Ruzsa's `I(H,N) ≪ τ(H,N)`**. Avoided entirely: `thm:logSavings-intersective`
  proves the intersectivity bound directly by translate packing.
