# Integer Cantor Sets: Arithmetic Combinatorial Properties

The paper of Burgin, Fragkos, Lacey, Mena and Reguera, together with a Lean 4
/ Mathlib formalization of its elementary and quantitative half.

An *integer Cantor set* `C = C(b,D)` is the set of non-negative integers all of
whose base `b` digits lie in a fixed digit set `D`. Throughout, the standing
assumption is `b ≥ 3`, `D ⊆ {0,…,b-1}`, `0 ∈ D` and `2 ≤ |D| < b`.

| | |
|---|---|
| Paper | [`main.tex`](main.tex), with `sarkozy.tex`, `jointUniform.tex`, `ConvergenceErgodic.tex`, `Poisson.tex`, `historical.tex` |
| Formalization | [`formalization/`](formalization/) — Lean 4.35.0, Mathlib pinned at `v4.35.0` |
| Blueprint | [`formalization/blueprint/src/content.tex`](formalization/blueprint/src/content.tex) — 66 items, 59 with complete Lean proofs |
| Status | 274 theorems, **no `sorry`**, every one reducible to `propext`, `Classical.choice`, `Quot.sound` |

## What is formalized

Six of the blueprint's chapters are complete. Every result below is proved in
Lean with no `sorry` and no axiom beyond the three Lean itself uses.

| Paper result | Statement | Lean | File |
|---|---|---|---|
| Prop. 2.5(i) | `enum` is the increasing enumeration of `C` | `range_enum` | `Structure.lean` |
| Prop. 2.5(ii) | block structure of the enumeration | `enum_block` | `Structure.lean` |
| Prop. 3.3 | `τ(C,N) ≤ log b / log N`, so `C` is van der Corput | `vdcConst_cantorSet_le` | `VanDerCorput.lean` |
| — | `I(C,N) ≤ 2 log b / log N`, so `C` is intersective | `intersectiveConst_cantorSet_le` | `VanDerCorput.lean` |
| Prop. 3.7 | power savings for signed digit sets | `vdcConst_signed_le` | `Signed.lean` |
| Lem. 4.7 | the key exponential sum converges, and vanishes off the exceptional set | `tendsto_expSum` | `ExpSum.lean` |
| Thm. 4.3 | `(κ(n), s_b(κ(n)))` is polynomially uniformly distributed | `isPUDU` | `PUDU.lean` |
| Prop. 5.1 | equidistribution of `s_b(κ(n))` in residue classes | `sumDigits_equidistributed` | `Residue.lean` |
| Lem. 5.3 | the limiting distribution of `κ(n) mod q` exists | `limitDistribution` | `Residue.lean` |
| Lem. 5.5 | positive density on each attained class | `positive_density` | `Residue.lean` |
| Thm. 5.7 | the joint distribution mod `(a,a')`, with its uniformity criterion | `joint_limitDistribution` | `Residue.lean` |
| §7, a step in Prop. 7.3 | no carries: `E(C ∩ [0,bˡ)) = E(D)ˡ` | `additiveEnergy_pow` | `PairCorrelation.lean` |

Supporting machinery proved along the way, usable on its own: the Fejér-kernel
bound `vdcConst_le_of_differences_mem` and the translate-packing lemma
`card_le_of_differences_mem`; `e(x)` and distance-to-the-nearest-integer
infrastructure (`expc`, `distInt`) with the defect estimate
`abs_Lhat_eq_one_iff`; and the digit-level lemmas `digits_enum`,
`enum_mul_add`, `enum_image_Iio`, `stepSize_dvd`, `modEq_sumDigits`.

## What is used but not formalized

Nothing in the Lean development depends on an unproved statement — there are
no `sorry`s and no custom axioms. What follows is therefore a list of results
of the *paper* that the formalization does not cover, not of gaps beneath the
results it does.

### Deep inputs the paper uses, absent from Mathlib

Each of these is marked `\notready` in the blueprint and is a prerequisite
project in its own right. The paper's conclusions that rest on them are
correspondingly absent here.

- **The Furstenberg correspondence principle**, and upper Banach density
  (`def:banach`, `thm:furstenberg`). Needed to pass from the dynamical
  recurrence statement to intersectivity of the polynomial sets `H_p`
  (Thm. 3.14). The blueprint records the dynamical form, which is what the
  paper's proof actually establishes.
- **The joint spectral measure of a pair of commuting unitaries** on `𝕋²`
  (Thms. 6.1 and 6.4). Mathlib has the continuous functional calculus but not
  the projection-valued measure. Note the *scalar* shadow of Thm. 6.1 — that
  the exponential averages converge — is `tendsto_expSum` above, and **is**
  formalized; only the passage to operators is missing.
- **Aistleitner–Larcher–Lewko** (`thm:ALL`), and with it the metric pair
  correlation result (Prop. 7.3). It is recorded as a hypothesis so that the
  reduction to it can be stated. Both of its inputs are formalized:
  `additiveEnergy_pow` above, and the growth bound `enum_lt_pow`.

### A result the paper uses that this development avoids

- **Ruzsa's `I(H,N) ≪ τ(H,N)`.** The paper deduces intersectivity of `C` from
  its van der Corput property through this theorem. Formalizing it would be a
  substantial separate project, so `intersectiveConst_cantorSet_le` is instead
  proved directly by translate packing (`card_le_of_differences_mem`), giving
  the same bound up to the constant. This is an avoided dependency rather than
  an assumed one: the Lean proof does not use Ruzsa's theorem at all.

### Clauses deliberately left out

Each is a remark the paper makes in passing that nothing below it needs. They
are flagged at their blueprint entries.

- That distinct pairs `i < j` give distinct tower differences (`lem:tower-diff`)
  — the Fejér-kernel lemma does not need it.
- That `0 ∉ D` makes `C` non-intersective (`lem:zero-necessary`) — the standing
  assumption includes `0 ∈ D` throughout.
- That the set of exceptional pairs is countable (`def:exceptional`) — clear
  from the definition, unused below.
- That the sufficient condition for joint uniformity is not necessary
  (`thm:modularJoint`) — a worked counterexample in the paper, `b = 4`,
  `D = {0,1}`.
- The real-exponent growth form `κ(n) ≤ b n^d` (`lem:growth`) — only the
  blocked pair-correlation chapter uses it; the integer form `enum_lt_pow` is
  proved.

### The trusted base

Lean's kernel, Mathlib at the pinned revision, and the three standard axioms
`propext`, `Classical.choice`, `Quot.sound`. Every theorem claimed above has
been checked with `#print axioms` to depend on nothing else. The definitions
themselves are of course taken on trust in the usual way: that `cantorSet`,
`vdcConst` and the rest say what the paper means is a matter of reading them,
and they are stated in [`Defs.lean`](formalization/IntegerCantorSets/Defs.lean)
and at the head of each file for that purpose.

## Building

The formalization:

```bash
cd formalization && lake exe cache get && lake build
```

The blueprint PDF:

```bash
cd formalization/blueprint/src && pdflatex -output-directory=../print print.tex
```

CI runs the Lean build on every push and fails if any declaration uses
`sorry`: [`.github/workflows/ci.yml`](.github/workflows/ci.yml).

## Layout

```
main.tex, sarkozy.tex, …        the paper
bibliography.bib                references
ChangeLogFirstCantorPaper/      change log
formalization/                  Lean project (see its own README)
  IntegerCantorSets/*.lean      8 files, ~6100 lines
  blueprint/src/content.tex     the blueprint, all 9 chapters
```

`formalization/README.md` has the per-file breakdown, the full list of proved
declarations, and notes on where to start.
