# Formalizing *Integer Cantor Sets: Arithmetic Combinatorial Properties*

A Lean 4 / Mathlib formalization of the paper in the parent directory, with a
[leanblueprint](https://github.com/PatrickMassot/leanblueprint)-style blueprint.

## Status

The project **builds**. Chapters 2, 3 and 4 are complete and sorry-free;
Chapter 5 is complete apart from its induction step. There is exactly
**one `sorry`** in the project, `UD_succ` in `PUDU.lean`.

- **Chapter 2 is complete**: `Structure.lean` proves **Proposition 2.5**,
  the enumeration theorem (`thm:enum-bij`, `lem:enum-block`), so `enum` is the
  increasing enumeration of `C(b,D)`, together with the initial-segment,
  growth and divisibility lemmas that Chapters 4–7 rest on.
- **Chapter 3 is complete**: `VanDerCorput.lean` proves **Proposition 3.3**
  (`thm:logSavings`), `τ(C,N) ≤ log b / log N` for `N ≥ 2`, and its
  intersective counterpart `thm:logSavings-intersective`,
  `I(C,N) ≤ 2 log b / log N` for `N ≥ b`.
- **Chapter 4 is complete**: `ExpSum.lean` proves **Lemma 4.7**
  (`thm:irrational`), the convergence of the key exponential sum
  `N⁻¹ ∑_{n<N} e(κ(n)α + s_b(κ(n))β)`, together with the three lemmas it
  rests on — `abs_Lhat_eq_one_iff`, `blockProduct` and `window_split` — and
  the escape lemma `exceptional_of_tendsto`. This is the result on which
  Chapters 5, 6 and 8 of the blueprint all depend.
- **Chapter 5 is complete except for the induction step**: `PUDU.lean` sets up
  polynomial uniform distribution for `MvPolynomial (Fin 2) ℝ` and proves
  **the base case** `UD_one` (`thm:UD1`), the first consumer of
  `tendsto_expSum`, together with `badDirections` (`lem:badDirections`) and
  the whole finite-Fourier apparatus it needs. `UD_succ` (`thm:UDstep`) is
  **stated but proved by `sorry`**; `UD_le` and `isPUDU` (`thm:polyUniform`,
  Theorem 4.3) reduce the theorem to it, so they are proved *modulo*
  `UD_succ` and carry `sorryAx`.

The remaining blueprint chapters (6–9) have no Lean statements yet; four of
their results are blocked on material absent from Mathlib (see below).

| | |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.35.0` |
| Mathlib | pinned at tag `v4.35.0` |
| Lean declarations | 30 definitions/structures, 137 theorem statements |
| Proved | 134; three (`UD_succ`, `UD_le`, `isPUDU`) depend on the one `sorry` |
| Blueprint items | 65 (20 definitions, 45 results), 8 marked blocked |
| `sorry` | 1 (`UD_succ`) |

Every theorem in the project except `UD_succ`, `UD_le` and `isPUDU` depends
only on `propext`, `Classical.choice` and `Quot.sound`; those three also
depend on `sorryAx`. In particular `IntegerCantorSet.range_enum`,
`IntegerCantorSet.enum_block`, `IntegerCantorSet.vdcConst_cantorSet_le`,
`IntegerCantorSet.intersectiveConst_cantorSet_le`,
`IntegerCantorSet.isIntersective_cantorSet`,
`IntegerCantorSet.exists_dvd_of_isIntersective` and
`IntegerCantorSet.tendsto_expSum`.

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
- Chapter 4, the character `e(x)` and the distance to `ℤ`: `expc_zero`,
  `expc_add`, `norm_expc`, `expc_ne_zero`, `expc_eq_one_iff`, `expc_zpow`,
  `distInt_nonneg`, `distInt_le_half`, `round_eq_of_abs_sub_lt`,
  `distInt_eq_of_abs_sub_lt`, `distInt_le`, `distInt_eq_zero_iff`,
  `distInt_add_le`, `distInt_neg`, `distInt_add_int`, `distInt_int_mul`,
  `distInt_sum_le`, `distInt_nat_mul`, `tendsto_zero_of_sq`,
  `norm_one_sub_expc`, `four_mul_distInt_le`.
- Chapter 4, the single-digit sum `L̂`: `exists_gcd_eq_sum` (Bézout for a
  finite set), `norm_Lhat_le_one`, `norm_prod_Lhat_le_one`, `norm_Lhat_le`
  (the quantitative defect estimate), `Lhat_eq_one`, `abs_Lhat_eq_one_iff`.
- Chapter 4, the block product: `norm_expPhi`, `norm_expPsi`, `expPsi_zero`,
  `sum_range_mul`, `sum_Ico_mul`, `sum_range_card_digitOf`, `expPhi_mul_add`,
  `blockProduct`, `sum_range_pow_eq`.
- Chapter 4, window splitting: `enum_block'`, `sumDigits_enum_block'`,
  `sum_block`, `ceil_div_bounds`, `floor_div_bounds`, `window_split`,
  `block_count_le`, `norm_window_le`.
- Chapter 4, Lemma 4.7: `escape_core`, `exceptional_of_tendsto`,
  `exists_int_of_mem_cantorSet`, `tendsto_expSum`.
- Chapter 5, two-variable monomials and irrational polynomials: `mono2`,
  `mono2_apply_zero`, `mono2_apply_one`, `finsupp_fin2_ext`, `mono2_self`,
  `mono2_eq_zero_iff`, `mono2_one_zero`, `mono2_zero_one`, `sum_support_eq`,
  `IsIrrationalPoly`, `IrrDegLE`, `IrrDegLE.mono`, `irrDegLE_totalDegree`,
  `irrational_coeff_of_irrDegLE_one`.
- Chapter 5, PUDU and bad directions: `polyEval`, `IsPUDU`, `UniformAvg`,
  `cantorSeq`, `dirDeriv`, `coeff_dirDeriv`, `exists_bad_direction`,
  `badDirections`.
- Chapter 5, non-exceptional pairs: `stepSize_pos`,
  `not_exceptional_of_irrational` (an exceptional pair has both coordinates
  rational).
- Chapter 5, finite Fourier analysis mod `q`: `expc_intCast`,
  `expc_eq_of_sub_int`, `expc_natCast_mul`, `sum_expc_orthogonality`,
  `sum_comm4`, `sum_sum_mul_mul`, `dvd_sub_natCast_iff`, `fourierCoeff`,
  `fourier_expansion`.
- Chapter 5, the rational part: `exists_common_denom`,
  `polyEval_sub_int_of_dvd`, `ratPart`, `coeff_ratPart`, `ratPart_coeff_rat`,
  `polyEval_eq_add_ratPart`.
- Chapter 5, the base case (Theorem 4.3 for irrational degree 1): `UD_one`.

Stated but **not proved**: `UD_succ` (`sorry`). `UD_le` and `isPUDU` are
proved from `UD_one` and `UD_succ`, hence hold modulo that one `sorry`.

## Layout

```
lakefile.toml, lean-toolchain     Lean project
IntegerCantorSets/Defs.lean       Chapter 2 definitions
IntegerCantorSets/Structure.lean  Chapter 2: the enumeration theorem
IntegerCantorSets/VanDerCorput.lean  Chapter 3: intersective / vdC
IntegerCantorSets/ExpSum.lean     Chapter 4: the key exponential sum
IntegerCantorSets/PUDU.lean       Chapter 5: polynomial uniform distribution
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
4. ~~**`thm:irrational`**~~ — done. Lemma 4.7, the key exponential sum, with
   `lem:Lhat-abs-one`, `lem:blockProduct`, `lem:windowSplit` and
   `lem:escape`. Chapters 5, 6 and 8 are no longer blocked on Chapter 4.
5. ~~**`thm:UD1`**~~ — done. The base case of Chapter 5, the first consumer of
   `thm:irrational`, together with `lem:badDirections` and the finite Fourier
   apparatus (orthogonality mod `q`, common denominators, the rational part of
   a polynomial of irrational degree 1).
6. **`thm:UDstep`** — the one `sorry` in the project, and now the single thing
   standing between the project and Theorem 4.3. Block decomposition by
   `enum_block'`, Cauchy–Schwarz in the block index, `badDirections` applied
   to the difference polynomial, and three counts of bad pairs, the last of
   which needs `∫₀¹ |L̂(θ)|^{2ρ} dθ → 0` from `abs_Lhat_eq_one_iff` by
   dominated convergence.
7. **`lem:noCarry`** — additive energy is multiplicative over digits. Finitary
   and independent of everything else, so it parallelizes.

## Known obstructions

Four results in the paper are blocked on material absent from Mathlib, and are
marked `\notready` in the blueprint:

- **Furstenberg correspondence principle** and upper Banach density
  (Chapter 7). A prerequisite project in its own right.
- **Joint spectral measure for commuting unitaries** on `𝕋²` (Chapter 8).
  Mathlib has the continuous functional calculus but not the
  projection-valued measure. The scalar shadow of the theorem — convergence of
  the exponential sums — is `thm:irrational`, which is now proved.
- **Aistleitner–Larcher–Lewko** (Chapter 9). Recorded as a hypothesis; the
  reduction to it is formalizable, the theorem itself is not a realistic
  target.
- **Ruzsa's `I(H,N) ≪ τ(H,N)`**. Avoided entirely: `thm:logSavings-intersective`
  proves the intersectivity bound directly by translate packing.
