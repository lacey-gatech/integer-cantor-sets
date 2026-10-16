# Formalizing *Integer Cantor Sets: Arithmetic Combinatorial Properties*

A Lean 4 / Mathlib formalization of the paper in the parent directory, with a
[leanblueprint](https://github.com/PatrickMassot/leanblueprint)-style blueprint.

## Status

The project **builds and contains no `sorry`**. Chapters 2, 3, 4, 5 and 6 are
complete.

- **Chapter 2 is complete**: `Structure.lean` proves **Proposition 2.5**,
  the enumeration theorem (`thm:enum-bij`, `lem:enum-block`), so `enum` is the
  increasing enumeration of `C(b,D)`, together with the initial-segment,
  growth and divisibility lemmas that Chapters 4–7 rest on.
- **Chapter 3 is complete**: `VanDerCorput.lean` proves **Proposition 3.3**
  (`thm:logSavings`), `τ(C,N) ≤ log b / log N` for `N ≥ 2`, and its
  intersective counterpart `thm:logSavings-intersective`,
  `I(C,N) ≤ 2 log b / log N` for `N ≥ b`. `Signed.lean` adds §3.1,
  **Proposition 3.7** (`thm:powerSavings`, `vdcConst_signed_le`): for a signed
  digit set `D` inside a complete residue system `R_b ⊆ (-b,b)` and a finite
  `S ⊆ ℤ` with `S - S ⊆ D` and `σ = |S| > 1`,
  `τ(C,N) ≤ σ N^{-log σ / log b}` for `N ≥ b` — a power saving. The signed
  Cantor set is a `Set ℤ`; `τ` is the constant of `VanDerCorput.lean` applied
  to `H = natAbs '' C \ {0} ⊆ ℕ`, which is legitimate because frequencies
  enter the cosine polynomial only through `cos(2π n x)`.
- **Chapter 4 is complete**: `ExpSum.lean` proves **Lemma 4.7**
  (`thm:irrational`), the convergence of the key exponential sum
  `N⁻¹ ∑_{n<N} e(κ(n)α + s_b(κ(n))β)`, together with the three lemmas it
  rests on — `abs_Lhat_eq_one_iff`, `blockProduct` and `window_split` — and
  the escape lemma `exceptional_of_tendsto`. This is the result on which
  Chapters 5, 6 and 8 of the blueprint all depend.
- **Chapter 5 is complete**: `PUDU.lean` proves **Theorem 4.3**
  (`thm:polyUniform`), that `n ↦ (κ(n), s_b(κ(n)))` is polynomially uniformly
  distributed (`isPUDU`). The base case `UD_one` (`thm:UD1`) is the first
  consumer of `tendsto_expSum`; the induction step `UD_succ` (`thm:UDstep`)
  is block decomposition plus Cauchy–Schwarz, with `badDirections`
  (`lem:badDirections`) controlling the difference polynomials and three
  counts of bad pairs, the last of which is
  `∫₀¹ |L̂(θ)|^{2ρ} dθ → 0` by `abs_Lhat_eq_one_iff` and dominated
  convergence.
- **Chapter 6 is complete**: `Residue.lean` proves **Proposition 5.1**
  (`prop:sumDigits`, `sumDigits_equidistributed`), **Lemma 5.3**
  (`lem:Allq`, `limitDistribution` and its three parts
  `limitDistribution_coprime`, `limitDistribution_dvd_pow`,
  `limitDistribution_mul`), **Lemma 5.5** (`lem:positiveDensity`,
  `positive_density`) and **Theorem 5.7** (`thm:modularJoint`,
  `joint_limitDistribution`, `joint_uniform` and the three non-uniformity
  cases). It is finite Fourier analysis on `ℤ_q` over `tendsto_expSum`;
  Chapter 5 is not used.

The remaining blueprint chapters (7–9) have no Lean statements yet; four of
their results are blocked on material absent from Mathlib (see below). One
unblocked item remains outside them: `lem:noCarry`.

| | |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.35.0` |
| Mathlib | pinned at tag `v4.35.0` |
| Lean declarations | 45 definitions/structures, 263 theorem statements |
| Proved | 263 (all of them) |
| Blueprint items | 66 (20 definitions, 46 results), 8 marked blocked |
| `sorry` | 0 |

Every theorem in the project depends only on `propext`, `Classical.choice`
and `Quot.sound`; in particular `IntegerCantorSet.range_enum`,
`IntegerCantorSet.enum_block`, `IntegerCantorSet.vdcConst_cantorSet_le`,
`IntegerCantorSet.intersectiveConst_cantorSet_le`,
`IntegerCantorSet.isIntersective_cantorSet`,
`IntegerCantorSet.exists_dvd_of_isIntersective`,
`IntegerCantorSet.vdcConst_signed_le`,
`IntegerCantorSet.tendsto_expSum`, `IntegerCantorSet.isPUDU`,
`IntegerCantorSet.sumDigits_equidistributed`,
`IntegerCantorSet.limitDistribution`, `IntegerCantorSet.positive_density`
and `IntegerCantorSet.joint_limitDistribution`.

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
- Chapter 3, §3.1, signed digits (`Signed.lean`): `SignedStanding` with
  `base_pos`, `abs_digit_lt`, `eq_zero_of_dvd`; `signed_digits_unique` and
  `signed_digits_eq_zero` (uniqueness of the signed digit representation);
  `zero_mem_signedCantorSet`, `mem_signedCantorSet_cons`; the block set
  `signedBlock` with `mem_signedBlock_succ`, `signedBlock_nonempty`,
  `card_signedBlock`, `sub_mem_signedCantorSet`, `abs_sub_signedBlock_lt`;
  `vdcConst_signed_pow_le` (the bound at `N = b^K`),
  **`vdcConst_signed_le`** (Proposition 3.7) and
  `vdcConst_signed_le_example` (the case `b = 5`, `D = {-1,0,1}`).
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
- Chapter 5, rational reals: `IsRat` with `isRat_iff` and its closure lemmas
  (`IsRat.add`, `.sub`, `.mul`, `.pow`, `.sum`, `.of_mul_left`,
  `isRat_intCast`, `isRat_natCast`), `irrational_of_isRat_sub`.
- Chapter 5, differencing: `conj_expc`, `normSq_sum_expc` (the expansion of
  `|∑ e(tⱼ)|²`), `norm_sum_sq_le_card_mul` (Cauchy–Schwarz),
  `le_of_sq_le_sq`, `norm_ofReal_of_nonneg`, `window_block_split`,
  `block_range_bounds`.
- Chapter 5, affine substitution: `substAffine`, `eval_substAffine`,
  `substAffine_add`, `C_mul_X_add_C_pow`, `substAffine_monomial`,
  `coeff_substAffine_monomial`, `substWeight` with
  `substWeight_eq_zero`/`_self`/`_add_zero`/`_add_one`,
  `isRat_substWeight`, `coeff_substAffine`.
- Chapter 5, the degree drop: `add_e0_apply_zero` and friends,
  `eq_of_le_of_deg_le`, `diffPoly`, `coeff_diffPoly`, `isRat_weight_diff`,
  `isRat_diffPoly_term`, **`irrDegLE_diffPoly`** (the difference polynomial
  loses a degree) and **`coeff_diffPoly_sub_isRat`** (its degree-`l`
  coefficients are those of `A^{m₀} ∂_w p`).
- Chapter 5, counting bad pairs: `sumDigits_le_of_lt_pow`,
  `card_filter_product`, `exists_linear_le_pow`, `badPairs`, `mem_badPairs`,
  `card_badPairs_le_of_fst_ne`, `badPairs_fst_zero`,
  `card_badPairs_fst_zero` (the Parseval identity
  `#bad = δ^{2ρ} ∫₀¹ |L̂|^{2ρ}`), `tendsto_integral_Lhat_pow` (dominated
  convergence), `exists_rho_card_badPairs_le`.
- Chapter 5, characters and integrals: `continuous_expc`,
  `continuous_expc_mul`, `continuous_Lhat`, `integrableOn_expc_mul`,
  `integral_expc_intCast_mul`, `sum_expc_sumDigits_eq`.
- Chapter 5, the induction step and Theorem 4.3: `blockDiff`,
  `irrDegLE_blockDiff`, `polyEval_cantorSeq`,
  `polyEval_substAffine_cantorSeq`, `polyEval_diffPoly_cantorSeq`,
  `polyEval_blockDiff_cantorSeq`, `mem_badPairs_of_not_irrationalPoly`,
  **`UD_succ`**, `UD_le`, **`isPUDU`**.
- Chapter 6, counting in residue classes: `countMod`, `densityMod`,
  `countMod_eq_sum`, `countMod_le`, `countMod_mono`, `countMod_zero`,
  `countMod_le_add`, `countMod2`, `densityMod2`, `countMod2_eq_sum`.
- Chapter 6, finite Fourier inversion: `expc_indicator`, `countMod_fourier`,
  `tendsto_of_tendsto_ofReal`, `tendsto_densityMod_complex`,
  `tendsto_densityMod`, `tendsto_densityMod_re`, and the two-dimensional
  `countMod2_fourier`, `tendsto_densityMod2_complex`,
  `tendsto_densityMod2_re`, `tendsto_densityMod2`.
- Chapter 6, the arithmetic of the step size: `stepSize_dvd_enum`,
  `stepSize_dvd_sumDigits_enum`, `div_gcd_dvd_of_dvd_mul`,
  `expc_eq_one_of_dvd`, `dvd_of_eq_intCast`, `sub_one_dvd_of_eq_zero`,
  `isInt_of_coprime`, `coprime_div_gcd_pow` (the `b`-free part of `q`).
- Chapter 6, the exceptional pairs that do not arise:
  `not_exceptional_sumDigits`, `not_exceptional_enum`,
  `not_exceptional_joint`.
- Chapter 6, uniform distribution on a subgroup: `sum_filter_dvd`,
  `fourier_subgroup`, `tendsto_densityMod_subgroup`,
  **`sumDigits_equidistributed`** (Proposition 5.1), `sumDigits_uniform_iff`.
- Chapter 6, the limiting distribution of `κ(n) mod q` (Lemma 5.3):
  `expPhi_enum`, `expPhi_sumDigits`, **`limitDistribution`**,
  `limitDistribution_coprime`, `limitDistribution_uniform_iff`,
  `countMod_block`, `limitDistribution_dvd_pow`, `linSol`, `linSol_lt`,
  `lin_cond_iff`, `limitDistribution_mul` (the product structure).
- Chapter 6, positive density and the joint distribution:
  **`positive_density`** (Lemma 5.5), `expPhi_joint`,
  **`joint_limitDistribution`** (Theorem 5.7), `JointUniform`,
  `joint_uniform`, `not_jointUniform_of_countMod2_eq_zero`,
  `not_jointUniform_of_gcd_enum`, `not_jointUniform_of_gcd_sumDigits`,
  `not_jointUniform_of_gcd_sub_one`.

## Layout

```
lakefile.toml, lean-toolchain     Lean project
IntegerCantorSets/Defs.lean       Chapter 2 definitions
IntegerCantorSets/Structure.lean  Chapter 2: the enumeration theorem
IntegerCantorSets/VanDerCorput.lean  Chapter 3: intersective / vdC
IntegerCantorSets/Signed.lean     Chapter 3, §3.1: signed digits, power savings
IntegerCantorSets/ExpSum.lean     Chapter 4: the key exponential sum
IntegerCantorSets/PUDU.lean       Chapter 5: polynomial uniform distribution
IntegerCantorSets/Residue.lean    Chapter 6: distribution in residue classes
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
6. ~~**`thm:UDstep` and `thm:polyUniform`**~~ — done. Theorem 4.3 is
   unconditional. Block decomposition by `enum_block'`, Cauchy–Schwarz in the
   block index, `badDirections` applied to the difference polynomial, and
   three counts of bad pairs, the last of which needs
   `∫₀¹ |L̂(θ)|^{2ρ} dθ → 0` from `abs_Lhat_eq_one_iff` by dominated
   convergence. Chapter 6 (`chap:residue`) is no longer blocked.
7. ~~**Chapter 6 (`chap:residue`)**~~ — done. Distribution in residue classes:
   finite Fourier inversion on `ℤ_q` over `thm:irrational`, which supplies
   every Fourier coefficient. Chapter 5 turned out not to be needed.
8. **`lem:noCarry`** — additive energy is multiplicative over digits. Finitary
   and independent of everything else, so it parallelizes.
9. **The signed-digit section of Chapter 3** (`def:signedCantorSet`,
   `thm:powerSavings`): the only other unblocked piece left.

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
