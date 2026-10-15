/-
Intersective and van der Corput properties.

Blueprint: `blueprint/src/content.tex`, Chapter 3.

The targets of this file are the two quantitative bounds of Chapter 3:
`vdcConst_cantorSet_le`, Proposition 3.3 of the paper, `τ(C, N) ≤ log b /
log N`; and `intersectiveConst_cantorSet_le`, `I(C, N) ≤ 2 log b / log N`.
Both are self-contained and need nothing beyond finite sums and elementary
real analysis.  The intersective bound is proved directly by translate packing
(`card_le_of_differences_mem`), deliberately avoiding Ruzsa's `I ≪ τ`.

This file contains no `sorry`.
-/
import IntegerCantorSets.Structure

namespace IntegerCantorSet

open Finset Filter

/-! ### Intersectivity -/

open scoped Classical in
/-- `maxAvoiding H N` is `Λ(H,N)`, the largest cardinality of a subset of
`{1,...,N}` no two of whose elements differ by a member of `H`.

`H` is understood to already exclude `0`.

Blueprint: `def:maxAvoiding`. -/
noncomputable def maxAvoiding (H : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.Icc 1 N).powerset.filter
    (fun A => ∀ x ∈ A, ∀ y ∈ A, y < x → (x - y) ∉ H)).sup Finset.card

/-- `I(H,N) = Λ(H,N)/N`.

Blueprint: `def:intersectiveConst`. -/
noncomputable def intersectiveConst (H : Set ℕ) (N : ℕ) : ℝ :=
  (maxAvoiding H N : ℝ) / N

/-- Blueprint: `def:isIntersective`. -/
def IsIntersective (H : Set ℕ) : Prop :=
  Tendsto (intersectiveConst H) atTop (nhds 0)

/-- Any avoiding subset of `{1,…,N}` bounds `Λ(H,N)` from below. -/
theorem le_maxAvoiding (H : Set ℕ) (N : ℕ) (B : Finset ℕ) (hsub : B ⊆ Finset.Icc 1 N)
    (havoid : ∀ x ∈ B, ∀ y ∈ B, y < x → (x - y) ∉ H) : B.card ≤ maxAvoiding H N := by
  classical
  rw [maxAvoiding]
  refine Finset.le_sup (f := Finset.card) ?_
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hsub, havoid⟩

/-- A bound valid for every avoiding subset of `{1,…,N}` bounds `Λ(H,N)`. -/
theorem maxAvoiding_le {H : Set ℕ} {N c : ℕ}
    (hc : ∀ B : Finset ℕ, B ⊆ Finset.Icc 1 N →
      (∀ x ∈ B, ∀ y ∈ B, y < x → (x - y) ∉ H) → B.card ≤ c) :
    maxAvoiding H N ≤ c := by
  classical
  rw [maxAvoiding]
  refine Finset.sup_le fun B hB => ?_
  simp only [Finset.mem_filter, Finset.mem_powerset] at hB
  exact hc B hB.1 hB.2

/-- `Λ` is subadditive, so by Fekete `I(H,N)` converges.

An avoiding subset of `{1,…,M+N}` splits into its part in `{1,…,M}` and its
part above `M`; translating the latter down by `M` preserves differences and
lands it in `{1,…,N}`.

Blueprint: `lem:intersective-converges`. -/
theorem maxAvoiding_subadditive (H : Set ℕ) (M N : ℕ) :
    maxAvoiding H (M + N) ≤ maxAvoiding H M + maxAvoiding H N := by
  classical
  refine maxAvoiding_le fun A hA hAavoid => ?_
  have hsplit : (A.filter (fun x => x ≤ M)).card + (A.filter (fun x => ¬ x ≤ M)).card = A.card :=
    Finset.card_filter_add_card_filter_not _
  have h1 : (A.filter (fun x => x ≤ M)).card ≤ maxAvoiding H M := by
    refine le_maxAvoiding H M _ ?_ ?_
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
      have := Finset.mem_Icc.1 (hA hx1)
      rw [Finset.mem_Icc]; omega
    · intro x hx y hy hyx
      exact hAavoid x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1 hyx
  have h2 : (A.filter (fun x => ¬ x ≤ M)).card ≤ maxAvoiding H N := by
    have hinj : Set.InjOn (fun x => x - M) (A.filter (fun x => ¬ x ≤ M)) := by
      intro x hx y hy hxy
      have hxy' : x - M = y - M := hxy
      obtain ⟨-, hx2⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hx)
      obtain ⟨-, hy2⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hy)
      omega
    rw [← Finset.card_image_of_injOn hinj]
    refine le_maxAvoiding H N _ ?_ ?_
    · intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
      have := Finset.mem_Icc.1 (hA hx1)
      rw [Finset.mem_Icc]; omega
    · intro z hz w hw hwz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hw
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.1 hx
      obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 hy
      have hwz' : y - M < x - M := hwz
      have hyx : y < x := by omega
      have hsub : x - M - (y - M) = x - y := by omega
      rw [hsub]
      exact hAavoid x hx1 y hy1 hyx
  omega

/-! ### The van der Corput constant -/

/-- The cosine polynomial `Ψ(x) = a 0 + ∑_{1 ≤ n < N} a n cos(2π n x)`. -/
noncomputable def cosPoly (a : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  a 0 + ∑ n ∈ Finset.Ico 1 N, a n * Real.cos (2 * Real.pi * n * x)

/-- A coefficient function is admissible for `(H, N)` when the associated
cosine polynomial is non-negative, takes the value `1` at `0`, and is
supported on `H`. -/
structure IsAdmissible (H : Set ℕ) (N : ℕ) (a : ℕ → ℝ) : Prop where
  support : ∀ n, 1 ≤ n → n < N → a n ≠ 0 → n ∈ H
  nonneg : ∀ x : ℝ, 0 ≤ cosPoly a N x
  normalized : cosPoly a N 0 = 1

/-- `τ(H,N)`, the van der Corput constant.

Blueprint: `def:vdcConst`. -/
noncomputable def vdcConst (H : Set ℕ) (N : ℕ) : ℝ :=
  sInf {c : ℝ | ∃ a : ℕ → ℝ, IsAdmissible H N a ∧ a 0 = c}

/-- Blueprint: `def:isVdC`. -/
def IsVdC (H : Set ℕ) : Prop :=
  Tendsto (vdcConst H) atTop (nhds 0)

/-- The constant polynomial `Ψ ≡ 1` is admissible, so the infimum defining
`τ` is over a non-empty set. -/
theorem admissible_one (H : Set ℕ) (N : ℕ) :
    IsAdmissible H N (fun n => if n = 0 then 1 else 0) := by
  have key : ∀ x : ℝ, cosPoly (fun n => if n = 0 then 1 else 0) N x = 1 := by
    intro x
    rw [cosPoly]
    have hz : ∀ n ∈ Finset.Ico 1 N,
        (if n = 0 then (1 : ℝ) else 0) * Real.cos (2 * Real.pi * n * x) = 0 := by
      intro n hn
      rw [Finset.mem_Ico] at hn
      have : n ≠ 0 := by omega
      simp [this]
    rw [Finset.sum_eq_zero hz]
    simp
  refine ⟨?_, fun x => by rw [key]; norm_num, key 0⟩
  intro n hn _ hne
  have hn0 : n ≠ 0 := by omega
  simp [hn0] at hne

/-- The integral of `cos(2π n x)` over a period vanishes for `n ≥ 1`. -/
theorem integral_cos_two_pi_mul {n : ℕ} (hn : n ≠ 0) :
    ∫ x in (0:ℝ)..1, Real.cos (2 * Real.pi * n * x) = 0 := by
  have hn' : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hc : (0:ℝ) < 2 * Real.pi * n := by
    have := Real.pi_pos; positivity
  have h2 : (2 * Real.pi * n) = ((2 * n : ℕ) : ℝ) * Real.pi := by push_cast; ring
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc.ne', integral_cos]
  simp only [mul_zero, mul_one, Real.sin_zero, sub_zero]
  rw [h2, Real.sin_nat_mul_pi, smul_zero]

/-- `∫₀¹ Ψ = a 0`: the constant term of a cosine polynomial is its mean. -/
theorem integral_cosPoly (a : ℕ → ℝ) (N : ℕ) :
    ∫ x in (0:ℝ)..1, cosPoly a N x = a 0 := by
  have hint : ∀ n ∈ Finset.Ico 1 N, IntervalIntegrable
      (fun x => a n * Real.cos (2 * Real.pi * n * x)) MeasureTheory.volume 0 1 :=
    fun n _ => Continuous.intervalIntegrable (by fun_prop) _ _
  have hg : IntervalIntegrable
      (fun x : ℝ => ∑ n ∈ Finset.Ico 1 N, a n * Real.cos (2 * Real.pi * n * x))
      MeasureTheory.volume 0 1 := Continuous.intervalIntegrable (by fun_prop) _ _
  simp only [cosPoly]
  rw [intervalIntegral.integral_add intervalIntegrable_const hg,
    intervalIntegral.integral_finsetSum hint]
  have h0 : ∀ n ∈ Finset.Ico 1 N,
      (∫ x in (0:ℝ)..1, a n * Real.cos (2 * Real.pi * n * x)) = 0 := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    rw [intervalIntegral.integral_const_mul, integral_cos_two_pi_mul (by omega), mul_zero]
  rw [Finset.sum_congr rfl h0]
  simp

/-- The constant term of an admissible polynomial is non-negative, being
`∫₀¹ Ψ` with `Ψ ≥ 0`. -/
theorem coeff_nonneg {H : Set ℕ} {N : ℕ} {a : ℕ → ℝ} (ha : IsAdmissible H N a) : 0 ≤ a 0 := by
  rw [← integral_cosPoly a N]
  exact intervalIntegral.integral_nonneg (by norm_num) (fun u _ => ha.nonneg u)

theorem vdcConst_nonneg (H : Set ℕ) (N : ℕ) : 0 ≤ vdcConst H N := by
  have hne : Set.Nonempty {c : ℝ | ∃ a : ℕ → ℝ, IsAdmissible H N a ∧ a 0 = c} :=
    ⟨1, _, admissible_one H N, by simp⟩
  refine le_csInf hne ?_
  rintro c ⟨a, ha, rfl⟩
  exact coeff_nonneg ha

/-- Any admissible coefficient function bounds `τ(H,N)` from above. -/
theorem vdcConst_le {H : Set ℕ} {N : ℕ} {a : ℕ → ℝ} (ha : IsAdmissible H N a) :
    vdcConst H N ≤ a 0 := by
  refine csInf_le ⟨0, ?_⟩ ⟨a, ha, rfl⟩
  rintro c ⟨a', ha', rfl⟩
  exact coeff_nonneg ha'

theorem vdcConst_le_one (H : Set ℕ) (N : ℕ) : vdcConst H N ≤ 1 := by
  simpa using vdcConst_le (admissible_one H N)

open scoped Classical in
/-- Truncating a coefficient function above `M` does not change the associated
cosine polynomial, so an `(H,M)`-admissible function is `(H,N)`-admissible for
`N ≥ M`. -/
theorem cosPoly_truncate (a : ℕ → ℝ) {M N : ℕ} (hMN : M ≤ N) (x : ℝ) :
    cosPoly (fun k => if 0 < k ∧ M ≤ k then 0 else a k) N x = cosPoly a M x := by
  have hsum : ∑ k ∈ Finset.Ico 1 N,
        (if 0 < k ∧ M ≤ k then (0:ℝ) else a k) * Real.cos (2 * Real.pi * k * x)
      = ∑ k ∈ Finset.Ico 1 M, a k * Real.cos (2 * Real.pi * k * x) := by
    rw [← Finset.sum_subset (Finset.Ico_subset_Ico le_rfl hMN)]
    · refine Finset.sum_congr rfl ?_
      intro k hk
      rw [Finset.mem_Ico] at hk
      have h' : ¬ (0 < k ∧ M ≤ k) := by omega
      simp [h']
    · intro y hy hny
      rw [Finset.mem_Ico] at hy
      rw [Finset.mem_Ico] at hny
      have h' : 0 < y ∧ M ≤ y := by omega
      simp [h']
  simp only [cosPoly]
  rw [hsum]
  simp

/-- Blueprint: `lem:vdcConst-antitone`.  Enlarging `N` enlarges the class of
admissible polynomials. -/
theorem vdcConst_antitone (H : Set ℕ) : Antitone (vdcConst H) := by
  intro M N hMN
  classical
  have hsub : {c : ℝ | ∃ a : ℕ → ℝ, IsAdmissible H M a ∧ a 0 = c} ⊆
      {c : ℝ | ∃ a : ℕ → ℝ, IsAdmissible H N a ∧ a 0 = c} := by
    rintro c ⟨a, ha, rfl⟩
    refine ⟨fun k => if 0 < k ∧ M ≤ k then 0 else a k, ⟨?_, ?_, ?_⟩, by simp⟩
    · intro k hk1 _ hk3
      have h' : ¬ (0 < k ∧ M ≤ k) := by
        by_contra hcon
        simp only [hcon] at hk3
        exact hk3 rfl
      simp only [h'] at hk3
      exact ha.support k hk1 (by omega) (by simpa using hk3)
    · intro x
      rw [cosPoly_truncate a hMN x]
      exact ha.nonneg x
    · rw [cosPoly_truncate a hMN 0]
      exact ha.normalized
  exact csInf_le_csInf ⟨0, by rintro c ⟨a, ha, rfl⟩; exact coeff_nonneg ha⟩
    ⟨1, _, admissible_one H M, by simp⟩ hsub

/-! ### Two elementary principles -/

/-- Blueprint: `lem:packing`.  If every non-zero difference of elements of `E`
has absolute value in `K`, and `A ⊆ [N]` avoids `K`, then the translates
`A + e` are disjoint inside an interval of length `N + max E - min E`. -/
theorem card_le_of_differences_mem (K : Set ℕ) (E A : Finset ℕ) (N : ℕ)
    (hE : E.Nonempty)
    (hdiff : ∀ x ∈ E, ∀ y ∈ E, y < x → (x - y) ∈ K)
    (hA : A ⊆ Finset.Icc 1 N)
    (havoid : ∀ x ∈ A, ∀ y ∈ A, y < x → (x - y) ∉ K) :
    A.card * E.card ≤ N + E.max' hE - E.min' hE := by
  classical
  -- two translates `a + e`, `a' + e'` of `A` that collide force `a - a' = e' - e`,
  -- which lies in `K` because `e, e' ∈ E` and avoids `K` because `a, a' ∈ A`
  have key : ∀ a ∈ A, ∀ e ∈ E, ∀ a' ∈ A, ∀ e' ∈ E, a + e = a' + e' → e < e' → False := by
    intro a ha e he a' ha' e' he' hsum hlt
    refine havoid a ha a' ha' (by omega) ?_
    rw [show a - a' = e' - e from by omega]
    exact hdiff e' he' e he hlt
  have hmaps : ∀ p ∈ A ×ˢ E, p.1 + p.2 ∈ Finset.Icc (1 + E.min' hE) (N + E.max' hE) := by
    rintro ⟨a, e⟩ hp
    obtain ⟨hpA, hpE⟩ := Finset.mem_product.1 hp
    have ha := Finset.mem_Icc.1 (hA hpA)
    have h1 := E.min'_le e hpE
    have h2 := E.le_max' e hpE
    rw [Finset.mem_Icc]
    constructor <;> simp only [] <;> omega
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.1 + p.2) (↑(A ×ˢ E) : Set (ℕ × ℕ)) := by
    rintro ⟨a, e⟩ hp ⟨a', e'⟩ hq hsum
    obtain ⟨hpA, hpE⟩ := Finset.mem_product.1 (Finset.mem_coe.1 hp)
    obtain ⟨hqA, hqE⟩ := Finset.mem_product.1 (Finset.mem_coe.1 hq)
    have hsum' : a + e = a' + e' := hsum
    rcases lt_trichotomy e e' with hc | hc | hc
    · exact (key a hpA e hpE a' hqA e' hqE hsum' hc).elim
    · subst hc
      have : a = a' := by omega
      subst this
      rfl
    · exact (key a' hqA e' hqE a hpA e hpE hsum'.symm hc).elim
  have hcard := Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.1 + p.2) hmaps hinj
  rw [Finset.card_product, Nat.card_Icc] at hcard
  omega

/-- The real form of `|∑_{j<n} e(θ_j)|² ≥ 0`: the full double sum of
`cos(θ_i - θ_j)` is a sum of two squares. -/
theorem sum_sum_cos_sub (n : ℕ) (θ : ℕ → ℝ) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, Real.cos (θ i - θ j)
      = (∑ i ∈ Finset.range n, Real.cos (θ i))^2
        + (∑ i ∈ Finset.range n, Real.sin (θ i))^2 := by
  simp_rw [Real.cos_sub, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, sq]

/-- Blueprint: `lem:fejer`.  A finite set all of whose differences lie in
`H` and are below `N` gives a Fejér kernel witnessing `τ(H,N) ≤ 1/n`. -/
theorem vdcConst_le_of_differences_mem (H : Set ℕ) (N n : ℕ) (hn : 0 < n)
    (u : ℕ → ℕ) (hmono : ∀ i j, i < j → j < n → u i < u j)
    (hmem : ∀ i j, i < j → j < n → (u j - u i) ∈ H)
    (hlt : ∀ i j, i < j → j < n → u j - u i < N) :
    vdcConst H N ≤ 1 / n := by
  classical
  rcases Nat.lt_or_ge n 2 with h1 | hn2
  · have hn1 : n = 1 := by omega
    subst hn1
    simpa using vdcConst_le_one H N
  have hN1 : 1 ≤ N := by
    have h01 := hlt 0 1 (by omega) (by omega)
    omega
  have hn0 : (n:ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  -- `d p` is the absolute difference of the two entries of the pair `p`
  set d : ℕ × ℕ → ℕ := fun p => max (u p.1) (u p.2) - min (u p.1) (u p.2) with hdd
  set P : Finset (ℕ × ℕ) := Finset.range n ×ˢ Finset.range n with hPP
  have hPmem : ∀ p : ℕ × ℕ, p ∈ P ↔ p.1 < n ∧ p.2 < n := by
    intro p
    rw [hPP, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  have hkey : ∀ p ∈ P, p.1 ≠ p.2 → (d p ∈ H ∧ d p < N ∧ d p ≠ 0) := by
    intro p hp hne
    obtain ⟨hp1, hp2⟩ := (hPmem p).1 hp
    rcases lt_or_gt_of_ne hne with hc | hc
    · have hu := hmono p.1 p.2 hc hp2
      have hv : d p = u p.2 - u p.1 := by
        simp only [hdd, max_eq_right hu.le, min_eq_left hu.le]
      rw [hv]
      exact ⟨hmem _ _ hc hp2, hlt _ _ hc hp2, by omega⟩
    · have hu := hmono p.2 p.1 hc hp1
      have hv : d p = u p.1 - u p.2 := by
        simp only [hdd, max_eq_left hu.le, min_eq_right hu.le]
      rw [hv]
      exact ⟨hmem _ _ hc hp1, hlt _ _ hc hp1, by omega⟩
  have hdlt : ∀ p ∈ P, d p ∈ Finset.range N := by
    intro p hp
    rw [Finset.mem_range]
    by_cases hne : p.1 = p.2
    · have : d p = 0 := by simp [hdd, hne]
      omega
    · exact (hkey p hp hne).2.1
  -- the pairs with equal entries are exactly the diagonal, and there are `n` of them
  have hdiag : P.filter (fun p => d p = 0) = (Finset.range n).diag := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_diag, Finset.mem_range, hPmem]
    constructor
    · rintro ⟨⟨hq1, hq2⟩, hq3⟩
      refine ⟨hq1, ?_⟩
      by_contra hne
      have hmemp : p ∈ P := (hPmem p).2 ⟨hq1, hq2⟩
      exact (hkey p hmemp hne).2.2 hq3
    · rintro ⟨hq1, hq2⟩
      refine ⟨⟨hq1, hq2 ▸ hq1⟩, ?_⟩
      have : p.2 = p.1 := hq2.symm
      simp [hdd, this]
  -- the Fejér kernel, written as a coefficient function
  set a : ℕ → ℝ := fun m => ((P.filter (fun p => d p = m)).card : ℝ) / n^2 with haa
  have hcos : ∀ (x : ℝ) (p : ℕ × ℕ),
      Real.cos (2 * Real.pi * (d p) * x)
        = Real.cos (2 * Real.pi * (u p.1) * x - 2 * Real.pi * (u p.2) * x) := by
    intro x p
    rcases le_total (u p.1) (u p.2) with hc | hc
    · have hv : ((d p : ℕ) : ℝ) = (u p.2 : ℝ) - (u p.1 : ℝ) := by
        simp only [hdd, max_eq_right hc, min_eq_left hc]
        exact Nat.cast_sub hc
      rw [hv, show 2*Real.pi*((u p.2:ℝ) - (u p.1:ℝ))*x
          = -(2*Real.pi*(u p.1:ℝ)*x - 2*Real.pi*(u p.2:ℝ)*x) from by ring, Real.cos_neg]
    · have hv : ((d p : ℕ) : ℝ) = (u p.1 : ℝ) - (u p.2 : ℝ) := by
        simp only [hdd, max_eq_left hc, min_eq_right hc]
        exact Nat.cast_sub hc
      rw [hv, show 2*Real.pi*((u p.1:ℝ) - (u p.2:ℝ))*x
          = 2*Real.pi*(u p.1:ℝ)*x - 2*Real.pi*(u p.2:ℝ)*x from by ring]
  -- `Ψ(x) = |n⁻¹ ∑_{j<n} e(u_j x)|²`, in the real form `(∑ cos)² + (∑ sin)²`
  have hkeyid : ∀ x : ℝ, cosPoly a N x
      = ((∑ i ∈ Finset.range n, Real.cos (2*Real.pi*(u i)*x))^2
         + (∑ i ∈ Finset.range n, Real.sin (2*Real.pi*(u i)*x))^2) / n^2 := by
    intro x
    have step1 : cosPoly a N x = ∑ m ∈ Finset.range N, a m * Real.cos (2*Real.pi*m*x) := by
      simp only [cosPoly]
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hN1]
      simp
    have step2 : ∑ m ∈ Finset.range N, a m * Real.cos (2*Real.pi*m*x)
        = (∑ p ∈ P, Real.cos (2*Real.pi*(d p)*x)) / n^2 := by
      rw [← Finset.sum_fiberwise_of_maps_to hdlt (fun p => Real.cos (2*Real.pi*(d p)*x)),
        Finset.sum_div]
      refine Finset.sum_congr rfl ?_
      intro m _
      have hinner : ∑ p ∈ P.filter (fun p => d p = m), Real.cos (2*Real.pi*(d p)*x)
          = ((P.filter (fun p => d p = m)).card : ℝ) * Real.cos (2*Real.pi*(m:ℝ)*x) := by
        rw [Finset.sum_congr rfl (g := fun _ => Real.cos (2*Real.pi*(m:ℝ)*x))
          (fun p hp => by rw [(Finset.mem_filter.1 hp).2]), Finset.sum_const, nsmul_eq_mul]
      rw [hinner, haa]
      ring
    have step3 : ∑ p ∈ P, Real.cos (2*Real.pi*(d p)*x)
        = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
            Real.cos (2*Real.pi*(u i)*x - 2*Real.pi*(u j)*x) := by
      rw [hPP, Finset.sum_product]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hcos x (i,j)))
    rw [step1, step2, step3, sum_sum_cos_sub n (fun i => 2*Real.pi*(u i)*x)]
  have hadm : IsAdmissible H N a := by
    refine ⟨?_, ?_, ?_⟩
    · intro m hm1 _ hm3
      have hcard : ((P.filter (fun p => d p = m)).card : ℝ) ≠ 0 := by
        intro h0
        apply hm3
        rw [haa]
        simp only [h0, zero_div]
      have hne : (P.filter (fun p => d p = m)).Nonempty :=
        Finset.card_pos.1 (Nat.pos_of_ne_zero (Nat.cast_ne_zero.1 hcard))
      obtain ⟨p, hp⟩ := hne
      rw [Finset.mem_filter] at hp
      have hpne : p.1 ≠ p.2 := by
        intro he
        have : d p = 0 := by simp [hdd, he]
        omega
      have := (hkey p hp.1 hpne).1
      rwa [hp.2] at this
    · intro x
      rw [hkeyid x]
      positivity
    · rw [hkeyid 0]
      simp only [mul_zero, Real.cos_zero, Real.sin_zero, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_one, Finset.sum_const_zero]
      rw [div_eq_one_iff_eq (by positivity)]
      ring
  have ha0 : a 0 = 1 / n := by
    rw [haa]
    simp only [hdiag, Finset.diag_card, Finset.card_range]
    rw [sq, ← div_div, div_self hn0]
  calc vdcConst H N ≤ a 0 := vdcConst_le hadm
    _ = 1/n := ha0

/-! ### Cantor sets are van der Corput with a `1 / log N` rate -/

/-- Blueprint: `def:tower`.  `u j = ∑_{t < j} d bᵗ`, so `u 0 = 0`. -/
def tower (b d : ℕ) (j : ℕ) : ℕ := ∑ t ∈ Finset.range j, d * b ^ t

@[simp] theorem tower_zero (b d : ℕ) : tower b d 0 = 0 := by simp [tower]

theorem tower_add (b d i m : ℕ) :
    tower b d (i + m) = tower b d i + b ^ i * tower b d m := by
  simp only [tower, Finset.sum_range_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro t _
  rw [pow_add]
  ring

theorem tower_succ (b d k : ℕ) : tower b d (k + 1) = d + b * tower b d k := by
  rw [show k + 1 = 1 + k from by omega, tower_add]
  simp [tower]

theorem tower_pos {b d : ℕ} (hd0 : d ≠ 0) {k : ℕ} (hk : 0 < k) : 0 < tower b d k := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [tower_succ]
  omega

/-- The tower is strictly increasing. -/
theorem tower_lt_tower {b : ℕ} (hb : 0 < b) {d : ℕ} (hd0 : d ≠ 0) {i j : ℕ} (hij : i < j) :
    tower b d i < tower b d j := by
  obtain ⟨m, rfl⟩ : ∃ m, j = i + (m + 1) := ⟨j - i - 1, by omega⟩
  rw [tower_add]
  have h1 : 0 < b ^ i * tower b d (m + 1) :=
    Nat.mul_pos (pow_pos hb i) (tower_pos hd0 (by omega))
  omega

theorem ofDigits_replicate (b d k : ℕ) :
    Nat.ofDigits b (List.replicate k d) = tower b d k := by
  induction k with
  | zero => simp [tower]
  | succ k ih =>
    rw [List.replicate_succ, Nat.ofDigits_cons, ih, tower_succ]

theorem ofDigits_replicate_zero (b k : ℕ) :
    Nat.ofDigits b (List.replicate k 0) = 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, Nat.ofDigits_cons, ih]; simp

/-- The base `b` digits of `bⁱ (d + db + ⋯ + db^m)`: the digit `d` in positions
`i, …, i+m` and `0` elsewhere. -/
theorem digits_pow_mul_tower (h : Standing b D) {d : ℕ} (hd : d < b) (hd0 : d ≠ 0) (i m : ℕ) :
    Nat.digits b (b ^ i * tower b d (m + 1))
      = List.replicate i 0 ++ List.replicate (m + 1) d := by
  have hb1 : 1 < b := by have := h.three_le_base; omega
  have hofd : Nat.ofDigits b (List.replicate i 0 ++ List.replicate (m + 1) d)
      = b ^ i * tower b d (m + 1) := by
    rw [Nat.ofDigits_append, ofDigits_replicate_zero, ofDigits_replicate]
    simp
  rw [← hofd]
  refine Nat.digits_ofDigits b hb1 _ ?_ ?_
  · intro l hl
    rcases List.mem_append.1 hl with h1 | h1
    · rw [List.eq_of_mem_replicate h1]; omega
    · rw [List.eq_of_mem_replicate h1]; exact hd
  · intro _
    rw [List.getLast_append_of_right_ne_nil _ _ (by simp), List.getLast_replicate_succ]
    exact hd0

/-- Blueprint: `lem:tower-diff`.  The differences of the tower lie in the
Cantor set. -/
theorem tower_sub_mem (h : Standing b D) {d : ℕ} (hd : d ∈ D) (hd0 : d ≠ 0)
    {i j : ℕ} (hij : i < j) :
    tower b d j - tower b d i ∈ cantorSet b D ∧ tower b d j - tower b d i ≠ 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, j = i + (m + 1) := ⟨j - i - 1, by omega⟩
  rw [tower_add, Nat.add_sub_cancel_left]
  have hb3 := h.three_le_base
  have hdig := digits_pow_mul_tower h (h.lt_base d hd) hd0 i m
  refine ⟨?_, ?_⟩
  · intro c hc
    rw [hdig] at hc
    rcases List.mem_append.1 hc with h1 | h1
    · rw [List.eq_of_mem_replicate h1]; exact h.zero_mem
    · rw [List.eq_of_mem_replicate h1]; exact hd
  · have : 0 < b ^ i * tower b d (m + 1) :=
      Nat.mul_pos (pow_pos (by omega) i) (tower_pos hd0 (by omega))
    omega

/-- Blueprint: `lem:tower-lt`. -/
theorem tower_lt (hb : 3 ≤ b) {d : ℕ} (hd : d < b) (n : ℕ) :
    tower b d n < b ^ n := by
  induction n with
  | zero => simp [tower]
  | succ k ih =>
    have he : tower b d (k + 1) = tower b d k + d * b ^ k := by
      simp [tower, Finset.sum_range_succ]
    calc tower b d (k + 1) = tower b d k + d * b ^ k := he
      _ < b ^ k + d * b ^ k := Nat.add_lt_add_right ih _
      _ = (1 + d) * b ^ k := by ring
      _ ≤ b * b ^ k := Nat.mul_le_mul_right _ (by omega)
      _ = b ^ (k + 1) := by ring

/-- **Proposition 3.3 of the paper.**  `τ(C, N) ≤ log b / log N`.

Blueprint: `thm:logSavings`.  This is the first real target of the
formalization. -/
theorem vdcConst_cantorSet_le (h : Standing b D) {N : ℕ} (hN : 2 ≤ N) :
    vdcConst (cantorSet b D \ {0}) N ≤ Real.log b / Real.log N := by
  obtain ⟨d, hdD, hd0⟩ : ∃ d ∈ D, d ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hsub : D ⊆ {0} := fun x hx => Finset.mem_singleton.2 (hcon x hx)
    have hcard := Finset.card_le_card hsub
    have h2 := h.two_le_card
    simp only [Finset.card_singleton] at hcard
    omega
  have hb3 := h.three_le_base
  have hb1 : 1 < b := by omega
  set k := Nat.log b N with hk
  have hbkN : b ^ k ≤ N := Nat.pow_log_le_self b (by omega)
  have hNbk : N < b ^ (k + 1) := Nat.lt_pow_succ_log_self hb1 N
  -- the tower `u j = ∑_{t<j} d bᵗ`, `j ≤ k`, has all differences in `C \ {0}` and `< N`
  have hfej : vdcConst (cantorSet b D \ {0}) N ≤ 1 / ((k + 1 : ℕ) : ℝ) := by
    refine vdcConst_le_of_differences_mem _ _ (k + 1) (by omega) (tower b d) ?_ ?_ ?_
    · exact fun i j hij _ => tower_lt_tower (by omega) hd0 hij
    · intro i j hij hj
      exact ⟨(tower_sub_mem h hdD hd0 hij).1, by simpa using (tower_sub_mem h hdD hd0 hij).2⟩
    · intro i j hij hj
      calc tower b d j - tower b d i ≤ tower b d j := Nat.sub_le _ _
        _ < b ^ j := tower_lt hb3 (h.lt_base d hdD) j
        _ ≤ b ^ k := Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ N := hbkN
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb1)
  have hlog : Real.log N ≤ ((k : ℝ) + 1) * Real.log b := by
    have h1 : (N:ℝ) ≤ (b:ℝ) ^ (k + 1) := by exact_mod_cast hNbk.le
    calc Real.log N ≤ Real.log ((b:ℝ) ^ (k + 1)) :=
          Real.log_le_log (by positivity) h1
      _ = ((k : ℝ) + 1) * Real.log b := by rw [Real.log_pow]; push_cast; ring
  calc vdcConst (cantorSet b D \ {0}) N ≤ 1 / ((k + 1 : ℕ) : ℝ) := hfej
    _ = 1 / ((k : ℝ) + 1) := by push_cast; ring
    _ ≤ Real.log b / Real.log N := by
        rw [div_le_div_iff₀ (by positivity) hlogN]
        linarith

/-- `C` is a van der Corput set. -/
theorem isVdC_cantorSet (h : Standing b D) : IsVdC (cantorSet b D \ {0}) := by
  have hg : Filter.Tendsto (fun N : ℕ => Real.log b / Real.log N) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine squeeze_zero' (.of_forall fun N => vdcConst_nonneg _ _) ?_ hg
  filter_upwards [Filter.eventually_ge_atTop 2] with N hN using vdcConst_cantorSet_le h hN

/-- Blueprint: `thm:logSavings-intersective`.  Proved directly from
`card_le_of_differences_mem`, deliberately avoiding Ruzsa's `I ≪ τ`. -/
theorem intersectiveConst_cantorSet_le (h : Standing b D) {N : ℕ} (hN : b ≤ N) :
    intersectiveConst (cantorSet b D \ {0}) N ≤ 2 * Real.log b / Real.log N := by
  classical
  obtain ⟨d, hdD, hd0⟩ : ∃ d ∈ D, d ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hsub : D ⊆ {0} := fun x hx => Finset.mem_singleton.2 (hcon x hx)
    have hcard := Finset.card_le_card hsub
    have h2 := h.two_le_card
    simp only [Finset.card_singleton] at hcard
    omega
  have hb3 := h.three_le_base
  have hb1 : 1 < b := by omega
  have hN3 : 3 ≤ N := le_trans hb3 hN
  set k := Nat.log b N with hk
  have hbkN : b ^ k ≤ N := Nat.pow_log_le_self b (by omega)
  have hNbk : N < b ^ (k + 1) := Nat.lt_pow_succ_log_self hb1 N
  -- the packing set: the `k+1` towers `u 0 = 0 < u 1 < ⋯ < u k`, all below `N`
  set E : Finset ℕ := (Finset.range (k + 1)).image (tower b d) with hEdef
  have hEne : E.Nonempty := ⟨tower b d 0, by rw [hEdef]; exact Finset.mem_image_of_mem _ (by simp)⟩
  have hEcard : E.card = k + 1 := by
    have hinj : Set.InjOn (tower b d) (Finset.range (k + 1)) := by
      intro i _ j _ hij
      by_contra hne
      rcases lt_or_gt_of_ne hne with hc | hc
      · exact (tower_lt_tower (show 0 < b by omega) hd0 hc).ne hij
      · exact (tower_lt_tower (show 0 < b by omega) hd0 hc).ne' hij
    rw [hEdef, Finset.card_image_of_injOn hinj, Finset.card_range]
  have hEmax : E.max' hEne ≤ N := by
    refine Finset.max'_le E hEne N ?_
    intro y hy
    rw [hEdef, Finset.mem_image] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    rw [Finset.mem_range] at hi
    have hlt : tower b d i < N :=
      calc tower b d i < b ^ i := tower_lt hb3 (h.lt_base d hdD) i
        _ ≤ b ^ k := Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ N := hbkN
    omega
  have hdiffE : ∀ x ∈ E, ∀ y ∈ E, y < x → (x - y) ∈ cantorSet b D \ {0} := by
    intro x hx y hy hyx
    rw [hEdef, Finset.mem_image] at hx hy
    obtain ⟨i, -, rfl⟩ := hx
    obtain ⟨j, -, rfl⟩ := hy
    have hji : j < i := by
      by_contra hc
      push_neg at hc
      rcases eq_or_lt_of_le hc with he | he
      · rw [he] at hyx; omega
      · have := tower_lt_tower (show 0 < b by omega) hd0 he
        omega
    exact ⟨(tower_sub_mem h hdD hd0 hji).1, by simpa using (tower_sub_mem h hdD hd0 hji).2⟩
  -- packing: every avoiding set `A ⊆ [N]` satisfies `|A| (k+1) ≤ N + max E ≤ 2N`
  have hΛ : maxAvoiding (cantorSet b D \ {0}) N ≤ 2 * N / (k + 1) := by
    refine maxAvoiding_le fun A hA hAavoid => ?_
    rw [Nat.le_div_iff_mul_le (by omega)]
    have hpack := card_le_of_differences_mem (cantorSet b D \ {0}) E A N hEne hdiffE hA hAavoid
    rw [hEcard] at hpack
    have := Nat.zero_le (E.min' hEne)
    omega
  have hΛ' : maxAvoiding (cantorSet b D \ {0}) N * (k + 1) ≤ 2 * N :=
    le_trans (Nat.mul_le_mul_right _ hΛ) (Nat.div_mul_le_self _ _)
  -- and `2/(k+1) ≤ 2 log b / log N`, exactly as in `vdcConst_cantorSet_le`
  have hNpos : (0:ℝ) < N := by positivity
  have hNpos' : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogb : 0 < Real.log b := Real.log_pos (by exact_mod_cast hb1)
  have hlog : Real.log N ≤ ((k : ℝ) + 1) * Real.log b := by
    have h1 : (N:ℝ) ≤ (b:ℝ) ^ (k + 1) := by exact_mod_cast hNbk.le
    calc Real.log N ≤ Real.log ((b:ℝ) ^ (k + 1)) := Real.log_le_log (by positivity) h1
      _ = ((k : ℝ) + 1) * Real.log b := by rw [Real.log_pow]; push_cast; ring
  have hcast : ((maxAvoiding (cantorSet b D \ {0}) N : ℝ)) * ((k:ℝ) + 1) ≤ 2 * N := by
    exact_mod_cast hΛ'
  rw [intersectiveConst]
  calc (maxAvoiding (cantorSet b D \ {0}) N : ℝ) / N ≤ 2 / ((k:ℝ) + 1) := by
        rw [div_le_div_iff₀ hNpos' (by positivity)]
        linarith
    _ ≤ 2 * Real.log b / Real.log N := by
        rw [div_le_div_iff₀ (by positivity) hlogN]
        nlinarith [hlog, hlogb]

theorem isIntersective_cantorSet (h : Standing b D) :
    IsIntersective (cantorSet b D \ {0}) := by
  have hg : Filter.Tendsto (fun N : ℕ => 2 * Real.log b / Real.log N) Filter.atTop (nhds 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine squeeze_zero' (.of_forall fun N => ?_) ?_ hg
  · simp only [intersectiveConst]
    positivity
  · filter_upwards [Filter.eventually_ge_atTop b] with N hN using
      intersectiveConst_cantorSet_le h hN

/-- Blueprint: `lem:zero-necessary`.  An intersective set meets every
`qℕ \ {0}`; hence `0 ∈ D` is necessary. -/
theorem exists_dvd_of_isIntersective {H : Set ℕ} (h : IsIntersective H) (q : ℕ)
    (hq : 1 ≤ q) : ∃ m ∈ H, m ≠ 0 ∧ q ∣ m := by
  classical
  by_contra hcon
  push_neg at hcon
  -- `hcon` : no non-zero multiple of `q` lies in `H`, so `{q, 2q, …, Mq}` avoids `H`
  have hqpos : (0:ℝ) < q := by exact_mod_cast hq
  have hev : ∀ᶠ N in Filter.atTop, intersectiveConst H N < 1 / (q:ℝ) :=
    h.eventually (gt_mem_nhds (by positivity))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hev
  set M := N₀ + 1 with hM
  have hcard : M ≤ maxAvoiding H (q * M) := by
    have hinj : Set.InjOn (fun i => q * (i + 1)) (Finset.range M) := by
      intro i _ j _ hij
      have hij' : q * (i + 1) = q * (j + 1) := hij
      have := Nat.eq_of_mul_eq_mul_left (by omega) hij'
      omega
    have hsub : (Finset.range M).image (fun i => q * (i + 1)) ⊆ Finset.Icc 1 (q * M) := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      rw [Finset.mem_range] at hi
      rw [Finset.mem_Icc]
      exact ⟨Nat.one_le_iff_ne_zero.2 (by positivity), Nat.mul_le_mul_left q (by omega)⟩
    have havoid : ∀ x ∈ (Finset.range M).image (fun i => q * (i + 1)),
        ∀ y ∈ (Finset.range M).image (fun i => q * (i + 1)), y < x → (x - y) ∉ H := by
      intro x hx y hy hyx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
      have hji : j < i := by
        by_contra hc
        push_neg at hc
        have : q * (j + 1) ≥ q * (i + 1) := Nat.mul_le_mul_left q (by omega)
        omega
      obtain ⟨c, rfl⟩ : ∃ c, i = j + c + 1 := ⟨i - j - 1, by omega⟩
      have hd : q * (j + c + 1 + 1) - q * (j + 1) = q * (c + 1) := by
        rw [show q * (j + c + 1 + 1) = q * (j + 1) + q * (c + 1) from by ring,
          Nat.add_sub_cancel_left]
      rw [hd]
      exact fun hmem => hcon _ hmem (by positivity) ⟨c + 1, rfl⟩
    have := le_maxAvoiding H (q * M) _ hsub havoid
    rwa [Finset.card_image_of_injOn hinj, Finset.card_range] at this
  have hqM : (0:ℝ) < (q * M : ℕ) := by
    have : 0 < q * M := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  have hge : 1 / (q:ℝ) ≤ intersectiveConst H (q * M) := by
    rw [intersectiveConst, div_le_div_iff₀ hqpos hqM]
    have h1 : (M:ℝ) ≤ (maxAvoiding H (q * M) : ℝ) := by exact_mod_cast hcard
    have h2 : ((q * M : ℕ) : ℝ) = (q:ℝ) * (M:ℝ) := by push_cast; ring
    rw [h2]
    nlinarith
  have hlt := hN₀ (q * M) (by nlinarith [Nat.le_mul_of_pos_left M (show 0 < q by omega)])
  linarith

end IntegerCantorSet
