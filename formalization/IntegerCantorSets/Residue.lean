/-
Distribution in residue classes.

Blueprint: `blueprint/src/content.tex`, Chapter 6 (`chap:residue`); Section 5
of the paper.

Everything here is finite Fourier analysis on `ℤ/q` layered over Lemma 4.7
(`tendsto_expSum`): the exponential sums whose limits that lemma supplies are
exactly the Fourier coefficients of the distribution of `κ(n) mod q` and of
`s_b(κ(n)) mod q`.
-/
import IntegerCantorSets.PUDU

namespace IntegerCantorSet

open Finset Filter
open scoped Real

variable {b : ℕ} {D : Finset ℕ}

/-! ### Counting in residue classes -/

/-- `countMod f q x N` is the number of `n < N` with `f n ≡ x` modulo `q`. -/
def countMod (f : ℕ → ℕ) (q x N : ℕ) : ℕ :=
  #((range N).filter fun n => f n % q = x % q)

/-- The density of `{n < N : f n ≡ x mod q}` in `[0, N)`. -/
noncomputable def densityMod (f : ℕ → ℕ) (q x N : ℕ) : ℝ :=
  (countMod f q x N : ℝ) / N

theorem countMod_eq_sum (f : ℕ → ℕ) (q x N : ℕ) :
    countMod f q x N = ∑ n ∈ range N, if f n % q = x % q then 1 else 0 := by
  rw [countMod, Finset.card_filter]

theorem countMod_le (f : ℕ → ℕ) (q x N : ℕ) : countMod f q x N ≤ N := by
  simpa [countMod] using Finset.card_filter_le (range N) fun n => f n % q = x % q

theorem countMod_mono (f : ℕ → ℕ) (q x : ℕ) {M N : ℕ} (hMN : M ≤ N) :
    countMod f q x M ≤ countMod f q x N := by
  rw [countMod_eq_sum, countMod_eq_sum]
  have hsub : range M ⊆ range N := fun i hi =>
    Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hi) hMN)
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
  intro i _ _
  positivity

/-- `countMod f q 0 N` counts the `n < N` with `q ∣ f n`. -/
theorem countMod_zero (f : ℕ → ℕ) (q N : ℕ) :
    countMod f q 0 N = #((range N).filter fun n => q ∣ f n) := by
  rw [countMod]
  congr 1


/-! ### Finite Fourier inversion on `ℤ/q` -/

/-- The indicator of a residue class, as a sum of additive characters. -/
theorem expc_indicator {q : ℕ} (hq : 0 < q) (m x : ℕ) :
    (q : ℂ)⁻¹ * ∑ u ∈ range q, expc ((u : ℝ) * ((m : ℝ) - (x : ℝ)) / q)
      = if m % q = x % q then 1 else 0 := by
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hiff : ((q : ℤ) ∣ ((m : ℤ) - (x : ℤ))) ↔ (m % q = x % q) := by
    rw [← Nat.modEq_iff_dvd]
    exact eq_comm
  have h1 : ∑ u ∈ range q, expc ((u : ℝ) * ((m : ℝ) - (x : ℝ)) / q)
      = if (q : ℤ) ∣ ((m : ℤ) - (x : ℤ)) then (q : ℂ) else 0 := by
    rw [← sum_expc_orthogonality hq ((m : ℤ) - (x : ℤ))]
    refine Finset.sum_congr rfl fun u _ => ?_
    congr 1
    push_cast
    ring
  rw [h1]
  by_cases hd : m % q = x % q
  · have h2 : (q : ℤ) ∣ ((m : ℤ) - (x : ℤ)) := hiff.2 hd
    simp [h2, hd, hqC]
  · have h2 : ¬ ((q : ℤ) ∣ ((m : ℤ) - (x : ℤ))) := fun hc => hd (hiff.1 hc)
    simp [h2, hd]

/-- Fourier inversion: the count of `n < N` in a residue class as a
combination of the exponential sums `∑_{n<N} e(u f(n)/q)`. -/
theorem countMod_fourier {q : ℕ} (hq : 0 < q) (f : ℕ → ℕ) (x N : ℕ) :
    ((countMod f q x N : ℕ) : ℂ)
      = (q : ℂ)⁻¹ * ∑ u ∈ range q,
          expc (-((u : ℝ) * x / q)) * ∑ n ∈ range N, expc ((u : ℝ) * f n / q) := by
  rw [countMod_eq_sum]
  push_cast
  have key : ∀ n ∈ range N, (if f n % q = x % q then (1 : ℂ) else 0)
      = (q : ℂ)⁻¹ * ∑ u ∈ range q,
          expc (-((u : ℝ) * x / q)) * expc ((u : ℝ) * f n / q) := by
    intro n _
    rw [← expc_indicator hq (f n) x]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← expc_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun u _ => by rw [Finset.mul_sum]

/-- Convergence of a real sequence from convergence of its complex image. -/
theorem tendsto_of_tendsto_ofReal {g : ℕ → ℝ} {L : ℝ}
    (h : Tendsto (fun N => ((g N : ℝ) : ℂ)) atTop (nhds ((L : ℝ) : ℂ))) :
    Tendsto g atTop (nhds L) := by
  have h2 := (Complex.continuous_re.tendsto ((L : ℝ) : ℂ)).comp h
  simpa [Function.comp_def] using h2

/-- The master convergence statement: if every Fourier coefficient
`N⁻¹ ∑_{n<N} e(u f(n)/q)` converges, so does the density of each residue
class, to the Fourier inverse of the limits. -/
theorem tendsto_densityMod_complex {q : ℕ} (hq : 0 < q) (f : ℕ → ℕ) (c : ℕ → ℂ)
    (hc : ∀ u ∈ range q,
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N, expc ((u : ℝ) * f n / q))
        atTop (nhds (c u)))
    (x : ℕ) :
    Tendsto (fun N => ((densityMod f q x N : ℝ) : ℂ)) atTop
      (nhds ((q : ℂ)⁻¹ * ∑ u ∈ range q, expc (-((u : ℝ) * x / q)) * c u)) := by
  have hre : ∀ N : ℕ, ((densityMod f q x N : ℝ) : ℂ)
      = (q : ℂ)⁻¹ * ∑ u ∈ range q,
          expc (-((u : ℝ) * x / q)) * ((N : ℂ)⁻¹ * ∑ n ∈ range N, expc ((u : ℝ) * f n / q)) := by
    intro N
    have h2 : (q : ℂ)⁻¹ * ∑ u ∈ range q,
          expc (-((u : ℝ) * x / q)) * ((N : ℂ)⁻¹ * ∑ n ∈ range N, expc ((u : ℝ) * f n / q))
        = (N : ℂ)⁻¹ * ((q : ℂ)⁻¹ * ∑ u ∈ range q,
          expc (-((u : ℝ) * x / q)) * ∑ n ∈ range N, expc ((u : ℝ) * f n / q)) := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun n _ => by ring
    rw [h2, ← countMod_fourier hq f x N, densityMod]
    push_cast
    ring
  refine Tendsto.congr (fun N => (hre N).symm) ?_
  refine Tendsto.const_mul _ ?_
  refine tendsto_finsetSum _ fun u hu => ?_
  exact Tendsto.const_mul _ (hc u hu)

/-- The real form of `tendsto_densityMod_complex` when the Fourier inverse is
known to be a given real number. -/
theorem tendsto_densityMod {q : ℕ} (hq : 0 < q) (f : ℕ → ℕ) (c : ℕ → ℂ)
    (hc : ∀ u ∈ range q,
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N, expc ((u : ℝ) * f n / q))
        atTop (nhds (c u)))
    (x : ℕ) {v : ℝ}
    (hv : (q : ℂ)⁻¹ * ∑ u ∈ range q, expc (-((u : ℝ) * x / q)) * c u = (v : ℂ)) :
    Tendsto (densityMod f q x) atTop (nhds v) := by
  refine tendsto_of_tendsto_ofReal ?_
  rw [← hv]
  exact tendsto_densityMod_complex hq f c hc x

/-- The real form of `tendsto_densityMod_complex` with no information about
the Fourier inverse: the density still converges, to its real part. -/
theorem tendsto_densityMod_re {q : ℕ} (hq : 0 < q) (f : ℕ → ℕ) (c : ℕ → ℂ)
    (hc : ∀ u ∈ range q,
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N, expc ((u : ℝ) * f n / q))
        atTop (nhds (c u)))
    (x : ℕ) :
    Tendsto (densityMod f q x) atTop
      (nhds ((q : ℂ)⁻¹ * ∑ u ∈ range q, expc (-((u : ℝ) * x / q)) * c u).re) := by
  have h2 := (Complex.continuous_re.tendsto _).comp (tendsto_densityMod_complex hq f c hc x)
  simpa [Function.comp_def] using h2

/-! ### The step size -/

theorem stepSize_dvd_enum (h : Standing b D) (n : ℕ) : stepSize D ∣ enum b D n :=
  stepSize_dvd h (enum_mem_cantorSet h n)

theorem stepSize_dvd_sumDigits_enum (h : Standing b D) (n : ℕ) :
    stepSize D ∣ sumDigits b (enum b D n) :=
  stepSize_dvd_sumDigits h (enum_mem_cantorSet h n)

/-! ### Elementary arithmetic -/

/-- If `q ∣ s * u` then `q / gcd(q, s)` divides `u`. -/
theorem div_gcd_dvd_of_dvd_mul {q s u : ℕ} (hq : 0 < q) (hdvd : q ∣ s * u) :
    q / Nat.gcd q s ∣ u := by
  have hg : 0 < Nat.gcd q s := Nat.gcd_pos_of_pos_left _ hq
  have hcop : Nat.Coprime (q / Nat.gcd q s) (s / Nat.gcd q s) :=
    Nat.coprime_div_gcd_div_gcd hg
  have hq' : Nat.gcd q s * (q / Nat.gcd q s) = q := Nat.mul_div_cancel' (Nat.gcd_dvd_left q s)
  have hs' : Nat.gcd q s * (s / Nat.gcd q s) = s := Nat.mul_div_cancel' (Nat.gcd_dvd_right q s)
  have h2 : Nat.gcd q s * (q / Nat.gcd q s) ∣ Nat.gcd q s * ((s / Nat.gcd q s) * u) := by
    rw [hq', ← mul_assoc, hs']
    exact hdvd
  exact hcop.dvd_of_dvd_mul_left ((mul_dvd_mul_iff_left (by omega : Nat.gcd q s ≠ 0)).1 h2)

/-- If `g ∣ q`, `g ∣ m` and `(q/g) ∣ u`, then `e(um/q) = 1`. -/
theorem expc_eq_one_of_dvd {q g u m : ℕ} (hq : 0 < q) (hgq : g ∣ q) (hgm : g ∣ m)
    (hu : q / g ∣ u) : expc ((u : ℝ) * (m : ℝ) / (q : ℝ)) = 1 := by
  have hg0 : 0 < g := Nat.pos_of_dvd_of_pos hgq hq
  obtain ⟨d, hd⟩ : ∃ d, q / g = d := ⟨_, rfl⟩
  have hdg : d * g = q := by rw [← hd]; exact Nat.div_mul_cancel hgq
  rw [hd] at hu
  obtain ⟨v, hv⟩ := hu
  obtain ⟨w, hw⟩ := hgm
  refine expc_eq_one_iff.2 ⟨((v * w : ℕ) : ℤ), ?_⟩
  have hnat : u * m = q * (v * w) := by
    rw [hv, hw, ← hdg]; ring
  have hcast : ((u * m : ℕ) : ℝ) = ((q * (v * w) : ℕ) : ℝ) := by exact_mod_cast hnat
  push_cast at hcast ⊢
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  field_simp
  linarith [hcast]

/-- A real identity between a natural and an integer multiple of `q` is a
divisibility. -/
theorem dvd_of_eq_intCast {q m : ℕ} {k : ℤ}
    (h : (m : ℝ) = (q : ℝ) * (k : ℝ)) : q ∣ m := by
  have hZ : (m : ℤ) = (q : ℤ) * k := by exact_mod_cast h
  exact Int.natCast_dvd_natCast.1 ⟨k, hZ⟩

/-- If `a/(b-1) + r/b^t + k = 0` with `a, r, k` integers, then `(b-1) ∣ a`;
`gcd(b-1, b^t) = 1` is what makes this work. -/
theorem sub_one_dvd_of_eq_zero (hb : 3 ≤ b) {a r k : ℤ} {t : ℕ}
    (h : (0 : ℝ) = (a : ℝ) / ((b : ℝ) - 1) + (r : ℝ) / (b : ℝ) ^ t + (k : ℝ)) :
    ((b : ℤ) - 1) ∣ a := by
  have hbR : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have h1 : ((b : ℝ) - 1) ≠ 0 := by linarith
  have h2 : ((b : ℝ)) ≠ 0 := by linarith
  have h3 : ((b : ℝ)) ^ t ≠ 0 := pow_ne_zero _ h2
  have h4 : ((a : ℝ) / ((b : ℝ) - 1) + (r : ℝ) / (b : ℝ) ^ t + (k : ℝ))
      * (((b : ℝ) - 1) * (b : ℝ) ^ t) = 0 := by
    rw [← h]; ring
  have key : (a : ℝ) * (b : ℝ) ^ t + ((r : ℝ) + (k : ℝ) * (b : ℝ) ^ t) * ((b : ℝ) - 1) = 0 := by
    rw [← h4]; field_simp; ring
  have keyZ : a * (b : ℤ) ^ t + (r + k * (b : ℤ) ^ t) * ((b : ℤ) - 1) = 0 := by
    exact_mod_cast key
  have hcop : IsCoprime ((b : ℤ) - 1) ((b : ℤ)) := ⟨-1, 1, by ring⟩
  refine (hcop.pow_right (n := t)).dvd_of_dvd_mul_right ?_
  exact ⟨-(r + k * (b : ℤ) ^ t), by linear_combination keyZ⟩

/-! ### Exceptional pairs do not arise -/

/-- Blueprint: the exceptional-pair exclusion behind `prop:sumDigits`. -/
theorem not_exceptional_sumDigits (h : Standing b D) {q u : ℕ} (hq : 0 < q)
    (hu : ¬ (q / Nat.gcd q (stepSize D) ∣ u)) :
    ¬ Exceptional b D 0 ((u : ℝ) / q) := by
  rintro ⟨a, r, t, ⟨k1, hk1⟩, ⟨k2, hk2⟩⟩
  refine hu ?_
  have hb := h.three_le_base
  have hbR : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb1 : ((b : ℝ) - 1) ≠ 0 := by linarith
  rw [mul_zero] at hk1
  obtain ⟨m, hm⟩ := sub_one_dvd_of_eq_zero hb hk1
  have ham : (a : ℝ) / ((b : ℝ) - 1) = (m : ℝ) := by
    have hreal : (a : ℝ) = ((b : ℝ) - 1) * (m : ℝ) := by exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hm
    rw [hreal]
    field_simp
  rw [ham] at hk2
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hqdvd : q ∣ stepSize D * u := by
    refine dvd_of_eq_intCast (k := k2 - m) ?_
    field_simp at hk2
    push_cast
    linarith [hk2]
  exact div_gcd_dvd_of_dvd_mul hq hqdvd

/-- Blueprint: the exceptional-pair exclusion behind part (1) of `lem:Allq`. -/
theorem not_exceptional_enum (h : Standing b D) {q u : ℕ} (hq : 0 < q)
    (hqb : Nat.Coprime q b) (hu : ¬ (q / Nat.gcd q (stepSize D) ∣ u)) :
    ¬ Exceptional b D ((u : ℝ) / q) 0 := by
  rintro ⟨a, r, t, ⟨k1, hk1⟩, ⟨k2, hk2⟩⟩
  refine hu ?_
  have hb := h.three_le_base
  have hbR : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hbne : ((b : ℝ)) ≠ 0 := by linarith
  have hbt : ((b : ℝ)) ^ t ≠ 0 := pow_ne_zero _ hbne
  rw [mul_zero] at hk2
  have ham : (a : ℝ) / ((b : ℝ) - 1) = (k2 : ℝ) := by linarith
  rw [ham] at hk1
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hqdvd : q ∣ stepSize D * u * b ^ t := by
    refine dvd_of_eq_intCast (k := (k2 + k1) * (b : ℤ) ^ t + r) ?_
    field_simp at hk1
    push_cast
    linarith [hk1]
  have hcop : Nat.Coprime q (b ^ t) := hqb.pow_right t
  exact div_gcd_dvd_of_dvd_mul hq (hcop.dvd_of_dvd_mul_right hqdvd)

/-! ### The uniform distribution on a subgroup -/

/-- The multiples of `d` below `d * g`, reindexed. -/
theorem sum_filter_dvd {M : Type*} [AddCommMonoid M] {d g : ℕ} (hd : 0 < d) (F : ℕ → M) :
    ∑ u ∈ (range (d * g)).filter (fun u => d ∣ u), F u = ∑ v ∈ range g, F (d * v) := by
  classical
  have himg : (range (d * g)).filter (fun u => d ∣ u) = (range g).image (fun v => d * v) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hu, v, rfl⟩
      exact ⟨v, by exact (Nat.mul_lt_mul_left hd).1 hu, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨(Nat.mul_lt_mul_left hd).2 hv, ⟨v, rfl⟩⟩
  rw [himg, Finset.sum_image]
  intro p _ r _ hpr
  exact Nat.eq_of_mul_eq_mul_left hd hpr

/-- The Fourier coefficients of the uniform distribution on the subgroup
`g ℤ_q`: the character `u` contributes exactly when `(q/g) ∣ u`, and the
inversion returns `g/q` on `gℤ_q` and `0` elsewhere. -/
theorem fourier_subgroup {q g x : ℕ} (hq : 0 < q) (hgq : g ∣ q) :
    (q : ℂ)⁻¹ * ∑ u ∈ range q,
        expc (-((u : ℝ) * x / q)) * (if q / g ∣ u then (1 : ℂ) else 0)
      = ((if g ∣ x then (g : ℝ) / q else 0 : ℝ) : ℂ) := by
  classical
  have hg0 : 0 < g := Nat.pos_of_dvd_of_pos hgq hq
  obtain ⟨d, hd⟩ : ∃ d, q / g = d := ⟨_, rfl⟩
  have hdg : d * g = q := by rw [← hd]; exact Nat.div_mul_cancel hgq
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | hp
    · simp at hdg; omega
    · exact hp
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hgR : (g : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hqdg : (q : ℝ) = (d : ℝ) * (g : ℝ) := by exact_mod_cast hdg.symm
  rw [hd]
  simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  rw [← hdg, sum_filter_dvd hd0]
  have hterm : ∀ v ∈ range g, expc (-(((d * v : ℕ) : ℝ) * x / (d * g : ℕ)))
      = expc ((v : ℝ) * ((-(x : ℤ) : ℤ) : ℝ) / (g : ℝ)) := by
    intro v _
    congr 1
    push_cast
    field_simp
  rw [Finset.sum_congr rfl hterm, sum_expc_orthogonality hg0 (-(x : ℤ))]
  have hiff : ((g : ℤ) ∣ (-(x : ℤ))) ↔ g ∣ x := by
    rw [dvd_neg, Int.natCast_dvd_natCast]
  by_cases hgx : g ∣ x
  · rw [ite_eq_left (hiff.2 hgx), ite_eq_left hgx]
    push_cast
    field_simp
  · rw [ite_eq_right (fun hc => hgx (hiff.1 hc)), ite_eq_right hgx]
    simp

/-- The main consequence: a sequence all of whose values are divisible by the
step size, and whose nontrivial Fourier coefficients vanish in the limit, is
asymptotically uniformly distributed on the subgroup `gℤ_q`, `g = gcd(q, s)`. -/
theorem tendsto_densityMod_subgroup {q : ℕ} (hq : 0 < q) (f : ℕ → ℕ)
    (hfs : ∀ n, stepSize D ∣ f n)
    (hzero : ∀ u : ℕ, ¬ (q / Nat.gcd q (stepSize D) ∣ u) →
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N, expc ((u : ℝ) * f n / q))
        atTop (nhds 0))
    (x : ℕ) :
    Tendsto (densityMod f q x) atTop
      (nhds (if Nat.gcd q (stepSize D) ∣ x then (Nat.gcd q (stepSize D) : ℝ) / q else 0)) := by
  classical
  refine tendsto_densityMod hq f
    (fun u => if q / Nat.gcd q (stepSize D) ∣ u then 1 else 0) ?_ x
    (fourier_subgroup hq (Nat.gcd_dvd_left _ _))
  intro u _
  by_cases hu : q / Nat.gcd q (stepSize D) ∣ u
  · rw [ite_eq_left hu]
    have hterm : ∀ n, expc ((u : ℝ) * f n / q) = 1 := fun n =>
      expc_eq_one_of_dvd hq (Nat.gcd_dvd_left _ _)
        ((Nat.gcd_dvd_right q (stepSize D)).trans (hfs n)) hu
    have hev : ∀ᶠ N : ℕ in atTop,
        (N : ℂ)⁻¹ * ∑ n ∈ range N, expc ((u : ℝ) * f n / q) = 1 := by
      filter_upwards [eventually_gt_atTop 0] with N hN
      have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      rw [Finset.sum_congr rfl (fun n (_ : n ∈ range N) => hterm n), Finset.sum_const,
        Finset.card_range, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hN']
    have hev' : (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N, expc ((u : ℝ) * f n / q))
        =ᶠ[atTop] (fun _ => (1 : ℂ)) := hev
    exact Tendsto.congr' hev'.symm tendsto_const_nhds
  · rw [ite_eq_right hu]
    exact hzero u hu

/-! ### Proposition 5.1: the sum of digits in residue classes -/

/-- Blueprint: `prop:sumDigits`, Proposition 5.1 of the paper.  With
`g = gcd(q, s)`, the sequence `s_b(κ(n)) mod q` is asymptotically uniformly
distributed on the subgroup `gℤ_q`. -/
theorem sumDigits_equidistributed (h : Standing b D) {q : ℕ} (hq : 0 < q) (x : ℕ) :
    Tendsto (densityMod (fun n => sumDigits b (enum b D n)) q x) atTop
      (nhds (if Nat.gcd q (stepSize D) ∣ x then (Nat.gcd q (stepSize D) : ℝ) / q else 0)) := by
  refine tendsto_densityMod_subgroup hq _ (fun n => stepSize_dvd_sumDigits_enum h n) ?_ x
  intro u hu
  obtain ⟨L, hL, hL0⟩ := tendsto_expSum h 0 ((u : ℝ) / q)
  obtain ⟨hLzero, -⟩ := hL0 (not_exceptional_sumDigits h hq hu)
  rw [hLzero] at hL
  refine hL.congr fun N => ?_
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [expPhi]
  congr 1
  ring

/-- The sum of digits is asymptotically uniformly distributed on all of `ℤ_q`
exactly when `gcd(q, s) = 1`. -/
theorem sumDigits_uniform_iff (h : Standing b D) {q : ℕ} (hq : 0 < q) :
    (∀ x : ℕ, Tendsto (densityMod (fun n => sumDigits b (enum b D n)) q x) atTop
      (nhds ((q : ℝ)⁻¹))) ↔ Nat.gcd q (stepSize D) = 1 := by
  constructor
  · intro hall
    by_contra hg
    have h1 := hall 1
    have h2 := sumDigits_equidistributed h hq 1
    have hgx : ¬ (Nat.gcd q (stepSize D) ∣ 1) := fun hc => hg (Nat.dvd_one.1 hc)
    rw [ite_eq_right hgx] at h2
    have huniq := tendsto_nhds_unique h1 h2
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    rw [inv_eq_zero] at huniq
    exact hqR.ne' huniq
  · intro hg x
    have h2 := sumDigits_equidistributed h hq x
    rw [hg] at h2
    simpa [one_div] using h2

/-! ### Lemma 5.3: the limiting distribution of `κ(n)` modulo `q` -/

/-- The summand of `tendsto_expSum` at `(u/q, 0)` is the `u`-th character of
`κ(n)` modulo `q`. -/
theorem expPhi_enum (u q : ℕ) (n : ℕ) :
    expPhi b D ((u : ℝ) / q) 0 n = expc ((u : ℝ) * enum b D n / q) := by
  rw [expPhi]
  congr 1
  ring

/-- The summand of `tendsto_expSum` at `(0, u/q)` is the `u`-th character of
`s_b(κ(n))` modulo `q`. -/
theorem expPhi_sumDigits (u q : ℕ) (n : ℕ) :
    expPhi b D 0 ((u : ℝ) / q) n = expc ((u : ℝ) * sumDigits b (enum b D n) / q) := by
  rw [expPhi]
  congr 1
  ring

/-- Blueprint: `lem:Allq`, existence part.  For every `q` the residues
`κ(n) mod q` have a limiting distribution. -/
theorem limitDistribution (h : Standing b D) {q : ℕ} (hq : 0 < q) (x : ℕ) :
    ∃ L : ℝ, Tendsto (densityMod (enum b D) q x) atTop (nhds L) := by
  classical
  choose c hc using fun u : ℕ => tendsto_expSum h ((u : ℝ) / q) 0
  refine ⟨_, tendsto_densityMod_re hq (enum b D) c ?_ x⟩
  intro u _
  refine ((hc u).1).congr fun N => ?_
  congr 1
  exact Finset.sum_congr rfl fun n _ => expPhi_enum u q n

/-- Blueprint: `lem:Allq` (1).  If `gcd(q, b) = 1` the limiting distribution
is uniform on the subgroup `gℤ_q`, `g = gcd(q, s)`. -/
theorem limitDistribution_coprime (h : Standing b D) {q : ℕ} (hq : 0 < q)
    (hqb : Nat.Coprime q b) (x : ℕ) :
    Tendsto (densityMod (enum b D) q x) atTop
      (nhds (if Nat.gcd q (stepSize D) ∣ x then (Nat.gcd q (stepSize D) : ℝ) / q else 0)) := by
  refine tendsto_densityMod_subgroup hq _ (fun n => stepSize_dvd_enum h n) ?_ x
  intro u hu
  obtain ⟨L, hL, hL0⟩ := tendsto_expSum h ((u : ℝ) / q) 0
  obtain ⟨hLzero, -⟩ := hL0 (not_exceptional_enum h hq hqb hu)
  rw [hLzero] at hL
  refine hL.congr fun N => ?_
  congr 1
  exact Finset.sum_congr rfl fun n _ => expPhi_enum u q n

/-- In the coprime case, `κ(n) mod q` is asymptotically uniformly distributed
on all of `ℤ_q` exactly when `gcd(q, s) = 1`. -/
theorem limitDistribution_uniform_iff (h : Standing b D) {q : ℕ} (hq : 0 < q)
    (hqb : Nat.Coprime q b) :
    (∀ x : ℕ, Tendsto (densityMod (enum b D) q x) atTop (nhds ((q : ℝ)⁻¹)))
      ↔ Nat.gcd q (stepSize D) = 1 := by
  constructor
  · intro hall
    by_contra hg
    have h1 := hall 1
    have h2 := limitDistribution_coprime h hq hqb 1
    have hgx : ¬ (Nat.gcd q (stepSize D) ∣ 1) := fun hc => hg (Nat.dvd_one.1 hc)
    rw [ite_eq_right hgx] at h2
    have huniq := tendsto_nhds_unique h1 h2
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    rw [inv_eq_zero] at huniq
    exact hqR.ne' huniq
  · intro hg x
    have h2 := limitDistribution_coprime h hq hqb x
    rw [hg] at h2
    simpa [one_div] using h2

/-! #### The `b`-adic case -/

theorem countMod_le_add (f : ℕ → ℕ) (q x : ℕ) {M N : ℕ} (hMN : M ≤ N) :
    countMod f q x N ≤ countMod f q x M + (N - M) := by
  have hsplit : countMod f q x N
      = countMod f q x M + ∑ n ∈ Finset.Ico M N, if f n % q = x % q then 1 else 0 := by
    rw [countMod_eq_sum, countMod_eq_sum, Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le M) hMN]
  have htail : (∑ n ∈ Finset.Ico M N, if f n % q = x % q then 1 else 0) ≤ N - M := by
    calc (∑ n ∈ Finset.Ico M N, if f n % q = x % q then 1 else 0)
        ≤ ∑ _n ∈ Finset.Ico M N, 1 := Finset.sum_le_sum fun n _ => by
            split <;> omega
      _ = N - M := by simp
  omega

/-- On a block of length `δ^j`, the residues of `κ` modulo `q` repeat, when
`q ∣ b^j`. -/
theorem countMod_block (h : Standing b D) {q j : ℕ} (hqb : q ∣ b ^ j) (x M : ℕ) :
    countMod (enum b D) q x (D.card ^ j * M) = M * countMod (enum b D) q x (D.card ^ j) := by
  classical
  rw [countMod_eq_sum, mul_comm (D.card ^ j) M, sum_range_mul M (D.card ^ j)]
  have hin : ∀ m ∈ range M,
      (∑ i ∈ range (D.card ^ j),
        if enum b D (D.card ^ j * m + i) % q = x % q then 1 else 0)
        = countMod (enum b D) q x (D.card ^ j) := by
    intro m _
    rw [countMod_eq_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < D.card ^ j := Finset.mem_range.1 hi
    have hmod : (b ^ j * enum b D m + enum b D i) % q = enum b D i % q := by
      obtain ⟨e, he⟩ := hqb
      simp [Nat.add_mod, he, mul_assoc, Nat.mul_mod_right]
    simp only [enum_block' h j m hi', hmod]
  rw [Finset.sum_congr rfl hin, Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- Blueprint: `lem:Allq` (2).  If `q ∣ b^j` the limiting distribution of
`κ(n) mod q` is the distribution of `C ∩ [0, b^j) mod q`, that is, of
`κ(i) mod q` for `i` uniform on `[0, δ^j)`. -/
theorem limitDistribution_dvd_pow (h : Standing b D) {q j : ℕ}
    (hqb : q ∣ b ^ j) (x : ℕ) :
    Tendsto (densityMod (enum b D) q x) atTop
      (nhds ((countMod (enum b D) q x (D.card ^ j) : ℝ) / (D.card ^ j : ℕ))) := by
  classical
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ, D.card ^ j = Λ := ⟨_, rfl⟩
  have hcard : 0 < D.card := by have := h.two_le_card; omega
  have hΛ : 0 < Λ := by rw [← hΛdef]; exact pow_pos hcard j
  obtain ⟨A, hAdef⟩ : ∃ A, countMod (enum b D) q x Λ = A := ⟨_, rfl⟩
  have hA : A ≤ Λ := by rw [← hAdef]; exact countMod_le _ _ _ _
  have hblock : ∀ M : ℕ, countMod (enum b D) q x (Λ * M) = M * A := by
    intro M
    rw [← hΛdef, countMod_block h hqb x M, hΛdef, hAdef]
  have hΛR : (0 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  have hAR : (A : ℝ) ≤ (Λ : ℝ) := by exact_mod_cast hA
  have hkey : ∀ N : ℕ, 0 < N →
      |densityMod (enum b D) q x N - (A : ℝ) / (Λ : ℝ)| ≤ (Λ : ℝ) / (N : ℝ) := by
    intro N hN
    obtain ⟨K, hK⟩ : ∃ K, N / Λ = K := ⟨_, rfl⟩
    obtain ⟨F, hF⟩ : ∃ F, N % Λ = F := ⟨_, rfl⟩
    have hNdecomp : Λ * K + F = N := by rw [← hK, ← hF]; exact Nat.div_add_mod N Λ
    have hFlt : F < Λ := by rw [← hF]; exact Nat.mod_lt _ hΛ
    have hlow : K * A ≤ countMod (enum b D) q x N := by
      rw [← hblock K]
      exact countMod_mono _ _ _ (by omega)
    have hhigh : countMod (enum b D) q x N ≤ K * A + F := by
      have := countMod_le_add (enum b D) q x (M := Λ * K) (N := N) (by omega)
      rw [hblock K] at this
      omega
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hlowR : ((K : ℝ) * (A : ℝ)) ≤ (countMod (enum b D) q x N : ℝ) := by exact_mod_cast hlow
    have hhighR : (countMod (enum b D) q x N : ℝ) ≤ (K : ℝ) * (A : ℝ) + (F : ℝ) := by
      exact_mod_cast hhigh
    have hNdR : (Λ : ℝ) * (K : ℝ) + (F : ℝ) = (N : ℝ) := by exact_mod_cast hNdecomp
    have hFR : (F : ℝ) < (Λ : ℝ) := by exact_mod_cast hFlt
    have hF0 : (0 : ℝ) ≤ (F : ℝ) := by positivity
    have hA0 : (0 : ℝ) ≤ (A : ℝ) := by positivity
    have hdiff : (countMod (enum b D) q x N : ℝ) / N - (A : ℝ) / Λ
        = ((countMod (enum b D) q x N : ℝ) * Λ - (A : ℝ) * N) / ((N : ℝ) * (Λ : ℝ)) := by
      field_simp
    have habs : |(countMod (enum b D) q x N : ℝ) * Λ - (A : ℝ) * N| ≤ (Λ : ℝ) * (Λ : ℝ) := by
      rw [abs_le]
      constructor <;> nlinarith
    rw [densityMod, hdiff, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) * (Λ : ℝ)),
      div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) * (Λ : ℝ))]
    have hcollapse : (Λ : ℝ) / (N : ℝ) * ((N : ℝ) * (Λ : ℝ)) = (Λ : ℝ) * (Λ : ℝ) := by
      field_simp
    rw [hcollapse]
    exact habs
  have hzero : Tendsto (fun N : ℕ => densityMod (enum b D) q x N - (A : ℝ) / (Λ : ℝ))
      atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_div_atTop_nhds_zero_nat (Λ : ℝ))
    filter_upwards [eventually_gt_atTop 0] with N hN
    simpa [Real.norm_eq_abs] using hkey N hN
  have hfin := hzero.add_const ((A : ℝ) / (Λ : ℝ))
  rw [zero_add] at hfin
  rw [hΛdef, hAdef]
  exact hfin.congr fun N => by ring

/-! #### The general case: the product structure -/

/-- The solution `y < r` of the linear congruence `w y + c ≡ x (mod r)`, when
`gcd(w, r) = 1`. -/
noncomputable def linSol (r w c x : ℕ) : ℕ :=
  (((x : ZMod r) - (c : ZMod r)) * ((w : ZMod r))⁻¹).val

theorem linSol_lt {r : ℕ} (hr : 0 < r) (w c x : ℕ) : linSol r w c x < r := by
  have : NeZero r := ⟨by omega⟩
  exact ZMod.val_lt _

/-- `w z + c ≡ x (mod r)` has `z ≡ linSol r w c x` as its only solution. -/
theorem lin_cond_iff {r w : ℕ} (hr : 0 < r) (hcop : Nat.Coprime w r) (c x z : ℕ) :
    (w * z + c ≡ x [MOD r]) ↔ (z ≡ linSol r w c x [MOD r]) := by
  have : NeZero r := ⟨by omega⟩
  have hw : ((w : ZMod r)) * ((w : ZMod r))⁻¹ = 1 := ZMod.coe_mul_inv_eq_one w hcop
  rw [← ZMod.natCast_eq_natCast_iff, ← ZMod.natCast_eq_natCast_iff, linSol]
  simp only [ZMod.natCast_val, ZMod.cast_id, Nat.cast_add, Nat.cast_mul]
  constructor
  · intro hh
    calc (z : ZMod r) = ((w : ZMod r) * (z : ZMod r)) * ((w : ZMod r))⁻¹ := by
          rw [mul_comm ((w : ZMod r)) ((z : ZMod r)), mul_assoc, hw, mul_one]
      _ = ((x : ZMod r) - (c : ZMod r)) * ((w : ZMod r))⁻¹ := by
          rw [← hh]; ring
  · intro hh
    rw [hh]
    calc (w : ZMod r) * (((x : ZMod r) - (c : ZMod r)) * ((w : ZMod r))⁻¹) + (c : ZMod r)
        = ((w : ZMod r) * ((w : ZMod r))⁻¹) * ((x : ZMod r) - (c : ZMod r)) + (c : ZMod r) := by
          ring
      _ = (x : ZMod r) := by rw [hw]; ring

/-- Blueprint: `lem:Allq` (3).  Writing `q = r u` with `gcd(r, b) = 1` and
`u ∣ b^j`, the limiting distribution of `κ(n) mod q` is the product of the
distributions of parts (1) and (2). -/
theorem limitDistribution_mul (h : Standing b D) {r u j : ℕ} (hr : 0 < r) (hu : 0 < u)
    (hrb : Nat.Coprime r b) (hub : u ∣ b ^ j) (x : ℕ) :
    Tendsto (densityMod (enum b D) (r * u) x) atTop
      (nhds ((if Nat.gcd r (stepSize D) ∣ x then (Nat.gcd r (stepSize D) : ℝ) / r else 0)
        * ((countMod (enum b D) u x (D.card ^ j) : ℝ) / (D.card ^ j : ℕ)))) := by
  classical
  have hru : Nat.Coprime r u := (hrb.pow_right j).coprime_dvd_right hub
  have hbr : Nat.Coprime (b ^ j) r := Nat.Coprime.pow_left j hrb.symm
  have hq : 0 < r * u := Nat.mul_pos hr hu
  have hcard : 0 < D.card := by have := h.two_le_card; omega
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ, D.card ^ j = Λ := ⟨_, rfl⟩
  have hΛ : 0 < Λ := by rw [← hΛdef]; exact pow_pos hcard j
  have hΛR : (0 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  -- the solution of the congruence attached to the `i`-th element of a block
  obtain ⟨y, hydef⟩ : ∃ y : ℕ → ℕ, y = fun i => linSol r (b ^ j) (enum b D i) x := ⟨_, rfl⟩
  have hylt : ∀ i, y i < r := by intro i; rw [hydef]; exact linSol_lt hr _ _ _
  have hymod : ∀ i, y i % r = y i := fun i => Nat.mod_eq_of_lt (hylt i)
  -- the block decomposition of the count
  have hcond : ∀ (m i : ℕ), i < Λ →
      ((enum b D (Λ * m + i) % (r * u) = x % (r * u))
        ↔ (enum b D i % u = x % u ∧ enum b D m % r = y i % r)) := by
    intro m i hi
    have hi' : i < D.card ^ j := by rw [hΛdef]; exact hi
    have hblk : enum b D (Λ * m + i) = b ^ j * enum b D m + enum b D i := by
      rw [← hΛdef]; exact enum_block' h j m hi'
    have hmodu : (enum b D (Λ * m + i) ≡ x [MOD u]) ↔ (enum b D i ≡ x [MOD u]) := by
      have hrepl : (b ^ j * enum b D m + enum b D i) % u = enum b D i % u := by
        obtain ⟨e, he⟩ := hub
        simp [Nat.add_mod, he, mul_assoc, Nat.mul_mod_right]
      rw [hblk]
      simp only [Nat.ModEq, hrepl]
    have hmodr : (enum b D (Λ * m + i) ≡ x [MOD r]) ↔ (enum b D m ≡ y i [MOD r]) := by
      rw [hblk, hydef]
      exact lin_cond_iff hr hbr _ _ _
    constructor
    · intro hh
      have := (Nat.modEq_and_modEq_iff_modEq_mul hru).2 hh
      exact ⟨hmodu.1 this.2, hmodr.1 this.1⟩
    · rintro ⟨h1, h2⟩
      exact (Nat.modEq_and_modEq_iff_modEq_mul hru).1 ⟨hmodr.2 h2, hmodu.2 h1⟩
  have hblockcount : ∀ M : ℕ, countMod (enum b D) (r * u) x (Λ * M)
      = ∑ i ∈ (range Λ).filter (fun i => enum b D i % u = x % u),
          countMod (enum b D) r (y i) M := by
    intro M
    rw [countMod_eq_sum, mul_comm Λ M, sum_range_mul M Λ, Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < Λ := Finset.mem_range.1 hi
    by_cases hib : enum b D i % u = x % u
    · rw [ite_eq_left hib, countMod_eq_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      by_cases hc : enum b D m % r = y i % r
      · rw [ite_eq_left hc, ite_eq_left ((hcond m i hi').2 ⟨hib, hc⟩)]
      · rw [ite_eq_right hc, ite_eq_right (fun hh => hc ((hcond m i hi').1 hh).2)]
    · rw [ite_eq_right hib]
      refine Finset.sum_eq_zero fun m _ => ?_
      exact ite_eq_right (fun hh => hib ((hcond m i hi').1 hh).1)
  -- divisibility of the solution by `gcd(r, s)` matches that of `x`
  have hgdvd : ∀ i, (Nat.gcd r (stepSize D) ∣ y i) ↔ (Nat.gcd r (stepSize D) ∣ x) := by
    intro i
    have hgr : Nat.gcd r (stepSize D) ∣ r := Nat.gcd_dvd_left _ _
    have hgk : Nat.gcd r (stepSize D) ∣ enum b D i :=
      (Nat.gcd_dvd_right r (stepSize D)).trans (stepSize_dvd_enum h i)
    have hsol : b ^ j * y i + enum b D i ≡ x [MOD r] := by
      rw [hydef]
      exact (lin_cond_iff hr hbr (enum b D i) x _).2 (Nat.ModEq.refl _)
    have hsolg : b ^ j * y i + enum b D i ≡ x [MOD Nat.gcd r (stepSize D)] :=
      Nat.ModEq.of_dvd hgr hsol
    have hki : enum b D i ≡ 0 [MOD Nat.gcd r (stepSize D)] := Nat.modEq_zero_iff_dvd.2 hgk
    have hstep : b ^ j * y i ≡ x [MOD Nat.gcd r (stepSize D)] := by
      have := (Nat.ModEq.add_left (b ^ j * y i) hki).symm.trans hsolg
      simpa using this
    have hcopg : Nat.Coprime (Nat.gcd r (stepSize D)) (b ^ j) :=
      (Nat.Coprime.coprime_dvd_left hgr hrb).pow_right j
    constructor
    · intro hy
      exact Nat.modEq_zero_iff_dvd.1 (hstep.symm.trans (Nat.modEq_zero_iff_dvd.2
        (Dvd.dvd.mul_left hy _)))
    · intro hx
      have : Nat.gcd r (stepSize D) ∣ b ^ j * y i :=
        Nat.modEq_zero_iff_dvd.1 (hstep.trans (Nat.modEq_zero_iff_dvd.2 hx))
      exact hcopg.dvd_of_dvd_mul_left this
  -- the limit along the subsequence `N = Λ M`
  obtain ⟨L, hL⟩ := limitDistribution h hq x
  have hmulto : Tendsto (fun M : ℕ => Λ * M) atTop atTop := by
    refine Filter.tendsto_atTop_atTop.2 fun z => ⟨z, fun K hK => ?_⟩
    calc z ≤ K := hK
      _ ≤ Λ * K := Nat.le_mul_of_pos_left K hΛ
  have hsub : Tendsto (fun M : ℕ => densityMod (enum b D) (r * u) x (Λ * M)) atTop (nhds L) :=
    hL.comp hmulto
  have hsplit : ∀ M : ℕ, 0 < M → densityMod (enum b D) (r * u) x (Λ * M)
      = (Λ : ℝ)⁻¹ * ∑ i ∈ (range Λ).filter (fun i => enum b D i % u = x % u),
          densityMod (enum b D) r (y i) M := by
    intro M hM
    have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    rw [densityMod, hblockcount M]
    push_cast
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [densityMod]
    field_simp
  have hterm : ∀ i : ℕ, Tendsto (densityMod (enum b D) r (y i)) atTop
      (nhds (if Nat.gcd r (stepSize D) ∣ x then (Nat.gcd r (stepSize D) : ℝ) / r else 0)) := by
    intro i
    have := limitDistribution_coprime h hr hrb (y i)
    by_cases hx : Nat.gcd r (stepSize D) ∣ x
    · rw [ite_eq_left ((hgdvd i).2 hx)] at this
      rw [ite_eq_left hx]
      exact this
    · rw [ite_eq_right (fun hc => hx ((hgdvd i).1 hc))] at this
      rw [ite_eq_right hx]
      exact this
  have hrhs : Tendsto (fun M : ℕ => (Λ : ℝ)⁻¹ *
        ∑ i ∈ (range Λ).filter (fun i => enum b D i % u = x % u),
          densityMod (enum b D) r (y i) M) atTop
      (nhds ((Λ : ℝ)⁻¹ * ∑ _i ∈ (range Λ).filter (fun i => enum b D i % u = x % u),
        (if Nat.gcd r (stepSize D) ∣ x then (Nat.gcd r (stepSize D) : ℝ) / r else 0))) :=
    Tendsto.const_mul _ (tendsto_finsetSum _ fun i _ => hterm i)
  have heq : Tendsto (fun M : ℕ => densityMod (enum b D) (r * u) x (Λ * M)) atTop
      (nhds ((Λ : ℝ)⁻¹ * ∑ _i ∈ (range Λ).filter (fun i => enum b D i % u = x % u),
        (if Nat.gcd r (stepSize D) ∣ x then (Nat.gcd r (stepSize D) : ℝ) / r else 0))) := by
    refine hrhs.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with M hM using (hsplit M hM).symm
  have hLval := tendsto_nhds_unique hsub heq
  rw [hLval, Finset.sum_const, nsmul_eq_mul] at hL
  rw [hΛdef]
  have hfin : (Λ : ℝ)⁻¹ * ((((range Λ).filter (fun i => enum b D i % u = x % u)).card : ℝ)
        * (if Nat.gcd r (stepSize D) ∣ x then (Nat.gcd r (stepSize D) : ℝ) / r else 0))
      = (if Nat.gcd r (stepSize D) ∣ x then (Nat.gcd r (stepSize D) : ℝ) / r else 0)
        * ((countMod (enum b D) u x Λ : ℝ) / ((Λ : ℕ) : ℝ)) := by
    rw [countMod]
    field_simp
  rw [hfin] at hL
  exact hL

/-! ### Lemma 5.5: positive density of the multiples of `q` -/

/-- For `j ≥ q` the prime factors of `q / gcd(q, b^j)` all miss `b`: this is
the `b`-free part `r` of `q` in the decomposition `q = r u` of `lem:Allq` (3). -/
theorem coprime_div_gcd_pow {q j : ℕ} (hq : 0 < q) (hj : q ≤ j) :
    Nat.Coprime (q / Nat.gcd q (b ^ j)) b := by
  by_contra hcop
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcop
  have hpr : p ∣ q / Nat.gcd q (b ^ j) := hpdvd.trans (Nat.gcd_dvd_left _ _)
  have hpb : p ∣ b := hpdvd.trans (Nat.gcd_dvd_right _ _)
  have hgq : Nat.gcd q (b ^ j) ∣ q := Nat.gcd_dvd_left _ _
  obtain ⟨e, hedef⟩ : ∃ e, q.factorization p = e := ⟨_, rfl⟩
  have he : e < q := by rw [← hedef]; exact Nat.factorization_lt p (by omega)
  have hpe : p ^ e ∣ q := by
    refine (Nat.Prime.pow_dvd_iff_le_factorization hp (by omega : q ≠ 0)).2 ?_
    omega
  have hpebj : p ^ e ∣ b ^ j :=
    (pow_dvd_pow p (by omega)).trans (pow_dvd_pow_of_dvd hpb j)
  have hpeg : p ^ e ∣ Nat.gcd q (b ^ j) := Nat.dvd_gcd hpe hpebj
  have hsplit : Nat.gcd q (b ^ j) * (q / Nat.gcd q (b ^ j)) = q :=
    Nat.mul_div_cancel' hgq
  have hbig : p ^ (e + 1) ∣ q := by
    obtain ⟨y, hy⟩ := hpr
    obtain ⟨z, hz⟩ := hpeg
    refine ⟨z * y, ?_⟩
    rw [← hsplit, hy, hz]
    ring
  have hle := (Nat.Prime.pow_dvd_iff_le_factorization hp (by omega : q ≠ 0)).1 hbig
  omega

/-- Blueprint: `lem:positiveDensity`, Lemma 5.5 of the paper.  For every `q`
the set `{n : q ∣ κ(n)}` has positive density. -/
theorem positive_density (h : Standing b D) {q : ℕ} (hq : 0 < q) :
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun N => (#((range N).filter fun n => q ∣ enum b D n) : ℝ) / N)
        atTop (nhds c) := by
  classical
  obtain ⟨c, hc⟩ := limitDistribution h hq 0
  refine ⟨c, ?_, ?_⟩
  swap
  · exact hc.congr fun N => by rw [densityMod, countMod_zero]
  -- the `b`-free part `r` of `q`
  obtain ⟨g, hgdef⟩ : ∃ g, Nat.gcd q (b ^ q) = g := ⟨_, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r, q / g = r := ⟨_, rfl⟩
  have hgq : g ∣ q := by rw [← hgdef]; exact Nat.gcd_dvd_left _ _
  have hgb : g ∣ b ^ q := by rw [← hgdef]; exact Nat.gcd_dvd_right _ _
  have hg0 : 0 < g := Nat.pos_of_dvd_of_pos hgq hq
  have hgr : g * r = q := by rw [← hrdef]; exact Nat.mul_div_cancel' hgq
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with hz | hp
    · rw [hz, mul_zero] at hgr; omega
    · exact hp
  have hcop : Nat.Coprime r b := by
    rw [← hrdef, ← hgdef]; exact coprime_div_gcd_pow hq (le_refl q)
  -- blocks of length `δ^q`
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ, D.card ^ q = Λ := ⟨_, rfl⟩
  have hcard : 0 < D.card := by have := h.two_le_card; omega
  have hΛ : 0 < Λ := by rw [← hΛdef]; exact pow_pos hcard q
  have hΛR : (0 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  -- `r ∣ κ(m)` implies `q ∣ κ(δ^q m)`
  have hincl : ∀ m : ℕ, r ∣ enum b D m → q ∣ enum b D (Λ * m) := by
    intro m hm
    have hz : (0 : ℕ) < D.card ^ q := pow_pos hcard q
    have hb0 := enum_block' h q m (j := 0) hz
    rw [Nat.add_zero, enum_zero, Nat.add_zero, hΛdef] at hb0
    have hmd : g * r ∣ b ^ q * enum b D m := mul_dvd_mul hgb hm
    rw [hgr] at hmd
    rw [hb0]
    exact hmd
  -- counting
  have hcount : ∀ K : ℕ, countMod (enum b D) r 0 K ≤ countMod (enum b D) q 0 (Λ * K) := by
    intro K
    rw [countMod_zero, countMod_zero]
    refine Finset.card_le_card_of_injOn (fun m => Λ * m) ?_ ?_
    · intro m hm
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_range] at hm ⊢
      exact ⟨(Nat.mul_lt_mul_left hΛ).2 hm.1, hincl m hm.2⟩
    · intro p _ y _ hpy
      exact Nat.eq_of_mul_eq_mul_left hΛ hpy
  have hdens : ∀ K : ℕ, 0 < K →
      (Λ : ℝ)⁻¹ * densityMod (enum b D) r 0 K ≤ densityMod (enum b D) q 0 (Λ * K) := by
    intro K hK
    have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
    have h1 : ((countMod (enum b D) r 0 K : ℕ) : ℝ)
        ≤ ((countMod (enum b D) q 0 (Λ * K) : ℕ) : ℝ) := by exact_mod_cast hcount K
    have hLK : (((Λ * K : ℕ)) : ℝ) = (Λ : ℝ) * (K : ℝ) := by push_cast; ring
    rw [densityMod, densityMod, hLK]
    have heq : (Λ : ℝ)⁻¹ * ((countMod (enum b D) r 0 K : ℝ) / (K : ℝ))
        = (countMod (enum b D) r 0 K : ℝ) / ((Λ : ℝ) * (K : ℝ)) := by
      field_simp
    rw [heq]
    exact div_le_div_of_nonneg_right h1 (by positivity)
  -- limits
  have hmulto : Tendsto (fun K : ℕ => Λ * K) atTop atTop := by
    refine Filter.tendsto_atTop_atTop.2 fun z => ⟨z, fun K hK => ?_⟩
    calc z ≤ K := hK
      _ ≤ Λ * K := Nat.le_mul_of_pos_left K hΛ
  have hright : Tendsto (fun K : ℕ => densityMod (enum b D) q 0 (Λ * K)) atTop (nhds c) :=
    hc.comp hmulto
  have hleft0 := limitDistribution_coprime h hr0 hcop 0
  rw [ite_eq_left (dvd_zero _)] at hleft0
  have hleft : Tendsto (fun K : ℕ => (Λ : ℝ)⁻¹ * densityMod (enum b D) r 0 K) atTop
      (nhds ((Λ : ℝ)⁻¹ * ((Nat.gcd r (stepSize D) : ℝ) / r))) := hleft0.const_mul _
  have hle : (Λ : ℝ)⁻¹ * ((Nat.gcd r (stepSize D) : ℝ) / r) ≤ c := by
    refine le_of_tendsto_of_tendsto hleft hright ?_
    filter_upwards [eventually_gt_atTop 0] with K hK using hdens K hK
  have hgcd0 : 0 < Nat.gcd r (stepSize D) := Nat.gcd_pos_of_pos_left _ hr0
  have hgcdR : (0 : ℝ) < (Nat.gcd r (stepSize D) : ℝ) := by exact_mod_cast hgcd0
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr0
  have hpos : (0 : ℝ) < (Λ : ℝ)⁻¹ * ((Nat.gcd r (stepSize D) : ℝ) / r) := by positivity
  linarith

/-! ### Theorem 5.7: the joint distribution of `(κ(n), s_b(κ(n)))` -/

/-- `countMod2 f g a a' x y N` counts the `n < N` with `f n ≡ x` modulo `a`
and `g n ≡ y` modulo `a'`. -/
def countMod2 (f g : ℕ → ℕ) (a a' x y N : ℕ) : ℕ :=
  #((range N).filter fun n => f n % a = x % a ∧ g n % a' = y % a')

/-- The density of `{n < N : f n ≡ x mod a, g n ≡ y mod a'}`. -/
noncomputable def densityMod2 (f g : ℕ → ℕ) (a a' x y N : ℕ) : ℝ :=
  (countMod2 f g a a' x y N : ℝ) / N

theorem countMod2_eq_sum (f g : ℕ → ℕ) (a a' x y N : ℕ) :
    countMod2 f g a a' x y N
      = ∑ n ∈ range N, if f n % a = x % a ∧ g n % a' = y % a' then 1 else 0 := by
  rw [countMod2, Finset.card_filter]

/-- Fourier inversion on `ℤ_a × ℤ_{a'}`. -/
theorem countMod2_fourier {a a' : ℕ} (ha : 0 < a) (ha' : 0 < a') (f g : ℕ → ℕ)
    (x y N : ℕ) :
    ((countMod2 f g a a' x y N : ℕ) : ℂ)
      = (a : ℂ)⁻¹ * (a' : ℂ)⁻¹ * ∑ u ∈ range a, ∑ v ∈ range a',
          expc (-((u : ℝ) * x / a + (v : ℝ) * y / a'))
            * ∑ n ∈ range N, expc ((u : ℝ) * f n / a + (v : ℝ) * g n / a') := by
  classical
  rw [countMod2_eq_sum]
  push_cast
  have key : ∀ n ∈ range N,
      (if f n % a = x % a ∧ g n % a' = y % a' then (1 : ℂ) else 0)
      = (a : ℂ)⁻¹ * (a' : ℂ)⁻¹ * ∑ u ∈ range a, ∑ v ∈ range a',
          expc (-((u : ℝ) * x / a + (v : ℝ) * y / a'))
            * expc ((u : ℝ) * f n / a + (v : ℝ) * g n / a') := by
    intro n _
    have hfactor : (if f n % a = x % a ∧ g n % a' = y % a' then (1 : ℂ) else 0)
        = (if f n % a = x % a then (1 : ℂ) else 0)
          * (if g n % a' = y % a' then (1 : ℂ) else 0) := by
      by_cases h1 : f n % a = x % a <;> by_cases h2 : g n % a' = y % a' <;> simp [h1, h2]
    have hprod : (∑ u ∈ range a, expc ((u : ℝ) * ((f n : ℝ) - (x : ℝ)) / a))
          * (∑ v ∈ range a', expc ((v : ℝ) * ((g n : ℝ) - (y : ℝ)) / a'))
        = ∑ u ∈ range a, ∑ v ∈ range a',
            expc (-((u : ℝ) * x / a + (v : ℝ) * y / a'))
              * expc ((u : ℝ) * f n / a + (v : ℝ) * g n / a') := by
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
      rw [← expc_add, ← expc_add]
      congr 1
      ring
    rw [hfactor, ← expc_indicator ha (f n) x, ← expc_indicator ha' (g n) y,
      mul_mul_mul_comm, hprod]
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun v _ => by rw [Finset.mul_sum]

/-- The two-dimensional master convergence statement. -/
theorem tendsto_densityMod2_complex {a a' : ℕ} (ha : 0 < a) (ha' : 0 < a') (f g : ℕ → ℕ)
    (c : ℕ → ℕ → ℂ)
    (hc : ∀ u ∈ range a, ∀ v ∈ range a',
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ *
          ∑ n ∈ range N, expc ((u : ℝ) * f n / a + (v : ℝ) * g n / a'))
        atTop (nhds (c u v)))
    (x y : ℕ) :
    Tendsto (fun N => ((densityMod2 f g a a' x y N : ℝ) : ℂ)) atTop
      (nhds ((a : ℂ)⁻¹ * (a' : ℂ)⁻¹ * ∑ u ∈ range a, ∑ v ∈ range a',
        expc (-((u : ℝ) * x / a + (v : ℝ) * y / a')) * c u v)) := by
  have hre : ∀ N : ℕ, ((densityMod2 f g a a' x y N : ℝ) : ℂ)
      = (a : ℂ)⁻¹ * (a' : ℂ)⁻¹ * ∑ u ∈ range a, ∑ v ∈ range a',
          expc (-((u : ℝ) * x / a + (v : ℝ) * y / a'))
            * ((N : ℂ)⁻¹ *
              ∑ n ∈ range N, expc ((u : ℝ) * f n / a + (v : ℝ) * g n / a')) := by
    intro N
    have h2 : (a : ℂ)⁻¹ * (a' : ℂ)⁻¹ * ∑ u ∈ range a, ∑ v ∈ range a',
          expc (-((u : ℝ) * x / a + (v : ℝ) * y / a'))
            * ((N : ℂ)⁻¹ *
              ∑ n ∈ range N, expc ((u : ℝ) * f n / a + (v : ℝ) * g n / a'))
        = (N : ℂ)⁻¹ * ((a : ℂ)⁻¹ * (a' : ℂ)⁻¹ * ∑ u ∈ range a, ∑ v ∈ range a',
          expc (-((u : ℝ) * x / a + (v : ℝ) * y / a'))
            * ∑ n ∈ range N, expc ((u : ℝ) * f n / a + (v : ℝ) * g n / a')) := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ =>
        Finset.sum_congr rfl fun n _ => by ring
    rw [h2, ← countMod2_fourier ha ha' f g x y N, densityMod2]
    push_cast
    ring
  refine Tendsto.congr (fun N => (hre N).symm) ?_
  refine Tendsto.const_mul _ ?_
  refine tendsto_finsetSum _ fun u hu => ?_
  refine tendsto_finsetSum _ fun v hv => ?_
  exact Tendsto.const_mul _ (hc u hu v hv)

/-- The real form: the density converges to the real part of the Fourier
inverse. -/
theorem tendsto_densityMod2_re {a a' : ℕ} (ha : 0 < a) (ha' : 0 < a') (f g : ℕ → ℕ)
    (c : ℕ → ℕ → ℂ)
    (hc : ∀ u ∈ range a, ∀ v ∈ range a',
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ *
          ∑ n ∈ range N, expc ((u : ℝ) * f n / a + (v : ℝ) * g n / a'))
        atTop (nhds (c u v)))
    (x y : ℕ) :
    Tendsto (densityMod2 f g a a' x y) atTop
      (nhds ((a : ℂ)⁻¹ * (a' : ℂ)⁻¹ * ∑ u ∈ range a, ∑ v ∈ range a',
        expc (-((u : ℝ) * x / a + (v : ℝ) * y / a')) * c u v).re) := by
  have h2 := (Complex.continuous_re.tendsto _).comp
    (tendsto_densityMod2_complex ha ha' f g c hc x y)
  simpa [Function.comp_def] using h2

/-- The summand of `tendsto_expSum` at `(u/a, v/a')` is the `(u,v)`-th
character of `(κ(n), s_b(κ(n)))`. -/
theorem expPhi_joint (u a v a' : ℕ) (n : ℕ) :
    expPhi b D ((u : ℝ) / a) ((v : ℝ) / a') n
      = expc ((u : ℝ) * enum b D n / a + (v : ℝ) * sumDigits b (enum b D n) / a') := by
  rw [expPhi]
  congr 1
  ring

/-- Blueprint: `thm:modularJoint` (1), Theorem 5.7 of the paper.  The pair
`(κ(n) mod a, s_b(κ(n)) mod a')` has a limiting distribution. -/
theorem joint_limitDistribution (h : Standing b D) {a a' : ℕ} (ha : 0 < a) (ha' : 0 < a')
    (x y : ℕ) :
    ∃ L : ℝ, Tendsto
      (densityMod2 (enum b D) (fun n => sumDigits b (enum b D n)) a a' x y) atTop (nhds L) := by
  classical
  choose c hc using fun uv : ℕ × ℕ =>
    tendsto_expSum h ((uv.1 : ℝ) / a) ((uv.2 : ℝ) / a')
  refine ⟨_, tendsto_densityMod2_re ha ha' (enum b D) _
    (fun u v => c (u, v)) ?_ x y⟩
  intro u _ v _
  refine ((hc (u, v)).1).congr fun N => ?_
  congr 1
  exact Finset.sum_congr rfl fun n _ => expPhi_joint u a v a' n

/-- The real form of `tendsto_densityMod2_complex` when the Fourier inverse is
known to be a given real number. -/
theorem tendsto_densityMod2 {a a' : ℕ} (ha : 0 < a) (ha' : 0 < a') (f g : ℕ → ℕ)
    (c : ℕ → ℕ → ℂ)
    (hc : ∀ u ∈ range a, ∀ v ∈ range a',
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ *
          ∑ n ∈ range N, expc ((u : ℝ) * f n / a + (v : ℝ) * g n / a'))
        atTop (nhds (c u v)))
    (x y : ℕ) {w : ℝ}
    (hw : (a : ℂ)⁻¹ * (a' : ℂ)⁻¹ * ∑ u ∈ range a, ∑ v ∈ range a',
        expc (-((u : ℝ) * x / a + (v : ℝ) * y / a')) * c u v = (w : ℂ)) :
    Tendsto (densityMod2 f g a a' x y) atTop (nhds w) := by
  refine tendsto_of_tendsto_ofReal ?_
  rw [← hw]
  exact tendsto_densityMod2_complex ha ha' f g c hc x y

/-- An integrality criterion by Bézout: if `n Y` and `m Y` are integers and
`gcd(n, m) = 1`, then `Y` is an integer. -/
theorem isInt_of_coprime {n m : ℕ} (hcop : Nat.Coprime n m) {Y : ℝ} {A C : ℤ}
    (h1 : (n : ℝ) * Y = (A : ℝ)) (h2 : (m : ℝ) * Y = (C : ℝ)) : ∃ k : ℤ, Y = (k : ℝ) := by
  obtain ⟨α, β, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  refine ⟨α * A + β * C, ?_⟩
  have habR : (α : ℝ) * (n : ℝ) + (β : ℝ) * (m : ℝ) = 1 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hab
  calc Y = ((α : ℝ) * (n : ℝ) + (β : ℝ) * (m : ℝ)) * Y := by rw [habR]; ring
    _ = (α : ℝ) * ((n : ℝ) * Y) + (β : ℝ) * ((m : ℝ) * Y) := by ring
    _ = (α : ℝ) * (A : ℝ) + (β : ℝ) * (C : ℝ) := by rw [h1, h2]
    _ = ((α * A + β * C : ℤ) : ℝ) := by push_cast; ring

/-- Blueprint: the exceptional-pair exclusion behind `thm:modularJoint` (2). -/
theorem not_exceptional_joint (h : Standing b D) {a a' u v : ℕ} (ha : 0 < a) (ha' : 0 < a')
    (hab : Nat.Coprime a (stepSize D * b)) (hab' : Nat.Coprime a' (stepSize D * (b - 1)))
    (hu : u < a) (hv : v < a') (huv : ¬ (u = 0 ∧ v = 0)) :
    ¬ Exceptional b D ((u : ℝ) / a) ((v : ℝ) / a') := by
  rintro ⟨c, r, t, ⟨k1, hk1⟩, ⟨k2, hk2⟩⟩
  have hb := h.three_le_base
  have hbR : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hb1 : ((b : ℝ) - 1) ≠ 0 := by linarith
  have hbne : ((b : ℝ)) ≠ 0 := by linarith
  have hbt : ((b : ℝ)) ^ t ≠ 0 := pow_ne_zero _ hbne
  have haR : ((a : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have ha'R : ((a' : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hb1cast : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
    have : (1 : ℕ) ≤ b := by omega
    push_cast [this]
    ring
  -- `Y = c/(b-1)` is an integer
  have hY1 : ((b - 1 : ℕ) : ℝ) * ((c : ℝ) / ((b : ℝ) - 1)) = (c : ℝ) := by
    rw [hb1cast]
    field_simp
  have hY2 : ((a' : ℕ) : ℝ) * ((c : ℝ) / ((b : ℝ) - 1))
      = ((a' * k2 - stepSize D * v : ℤ) : ℝ) := by
    field_simp at hk2 ⊢
    push_cast
    linarith [hk2]
  have hcopb1 : Nat.Coprime a' (b - 1) := hab'.coprime_dvd_right (dvd_mul_left _ _)
  obtain ⟨m, hm⟩ := isInt_of_coprime hcopb1 hY2 hY1
  rw [hm] at hk2 hk1
  -- hence `v = 0`
  have hdvdv : a' ∣ stepSize D * v := by
    refine dvd_of_eq_intCast (k := k2 - m) ?_
    field_simp at hk2
    push_cast
    linarith [hk2]
  have hcops' : Nat.Coprime a' (stepSize D) := hab'.coprime_dvd_right (dvd_mul_right _ _)
  have hv0 : v = 0 := Nat.eq_zero_of_dvd_of_lt (hcops'.dvd_of_dvd_mul_left hdvdv) hv
  -- and then `u = 0`
  have hdvdu : a ∣ stepSize D * u * b ^ t := by
    refine dvd_of_eq_intCast (k := (m + k1) * (b : ℤ) ^ t + r) ?_
    field_simp at hk1
    push_cast
    linarith [hk1]
  have hcopb : Nat.Coprime a b := hab.coprime_dvd_right (dvd_mul_left _ _)
  have hcops : Nat.Coprime a (stepSize D) := hab.coprime_dvd_right (dvd_mul_right _ _)
  have hdvdu' : a ∣ stepSize D * u := (hcopb.pow_right t).dvd_of_dvd_mul_right hdvdu
  have hu0 : u = 0 := Nat.eq_zero_of_dvd_of_lt (hcops.dvd_of_dvd_mul_left hdvdu') hu
  exact huv ⟨hu0, hv0⟩

/-- The limiting distribution of `(κ(n) mod a, s_b(κ(n)) mod a')` is the
uniform distribution on `ℤ_a × ℤ_{a'}`. -/
def JointUniform (b : ℕ) (D : Finset ℕ) (a a' : ℕ) : Prop :=
  ∀ x y : ℕ, Tendsto
    (densityMod2 (enum b D) (fun n => sumDigits b (enum b D n)) a a' x y)
    atTop (nhds (((a : ℝ) * (a' : ℝ))⁻¹))

/-- Blueprint: `thm:modularJoint` (2).  If `gcd(a, sb) = 1` and
`gcd(a', s(b-1)) = 1` the limiting distribution is uniform. -/
theorem joint_uniform (h : Standing b D) {a a' : ℕ} (ha : 0 < a) (ha' : 0 < a')
    (hab : Nat.Coprime a (stepSize D * b)) (hab' : Nat.Coprime a' (stepSize D * (b - 1))) :
    JointUniform b D a a' := by
  classical
  intro x y
  refine tendsto_densityMod2 ha ha' (enum b D) (fun n => sumDigits b (enum b D n))
    (fun u v => if u = 0 ∧ v = 0 then 1 else 0) ?_ x y ?_
  · intro u hu v hv
    by_cases huv : u = 0 ∧ v = 0
    · rw [ite_eq_left huv]
      obtain ⟨rfl, rfl⟩ := huv
      have hterm : ∀ n : ℕ, expc (((0 : ℕ) : ℝ) * enum b D n / a
          + ((0 : ℕ) : ℝ) * sumDigits b (enum b D n) / a') = 1 := by
        intro n
        have : ((0 : ℕ) : ℝ) * enum b D n / a
            + ((0 : ℕ) : ℝ) * sumDigits b (enum b D n) / a' = 0 := by
          push_cast; ring
        rw [this, expc_zero]
      have hev : ∀ᶠ N : ℕ in atTop, (N : ℂ)⁻¹ * ∑ n ∈ range N,
          expc (((0 : ℕ) : ℝ) * enum b D n / a
            + ((0 : ℕ) : ℝ) * sumDigits b (enum b D n) / a') = 1 := by
        filter_upwards [eventually_gt_atTop 0] with N hN
        have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
        rw [Finset.sum_congr rfl (fun n (_ : n ∈ range N) => hterm n), Finset.sum_const,
          Finset.card_range, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hN']
      have hev' : (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N,
          expc (((0 : ℕ) : ℝ) * enum b D n / a
            + ((0 : ℕ) : ℝ) * sumDigits b (enum b D n) / a'))
          =ᶠ[atTop] (fun _ => (1 : ℂ)) := hev
      exact Tendsto.congr' hev'.symm tendsto_const_nhds
    · rw [ite_eq_right huv]
      obtain ⟨L, hL, hL0⟩ := tendsto_expSum h ((u : ℝ) / a) ((v : ℝ) / a')
      obtain ⟨hLz, -⟩ := hL0 (not_exceptional_joint h ha ha' hab hab'
        (Finset.mem_range.1 hu) (Finset.mem_range.1 hv) huv)
      rw [hLz] at hL
      refine hL.congr fun N => ?_
      congr 1
      exact Finset.sum_congr rfl fun n _ => expPhi_joint u a v a' n
  · have hsum : (∑ u ∈ range a, ∑ v ∈ range a',
        expc (-((u : ℝ) * x / a + (v : ℝ) * y / a'))
          * (if u = 0 ∧ v = 0 then (1 : ℂ) else 0)) = 1 := by
      rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 ha)]
      · rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 ha')]
        · norm_num
        · intro v _ hv0
          simp [hv0]
      · intro u _ hu0
        refine Finset.sum_eq_zero fun v _ => ?_
        simp [hu0]
    rw [hsum, mul_one]
    have haC : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have ha'C : (a' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    push_cast
    field_simp

/-- A residue class that is never hit witnesses non-uniformity. -/
theorem not_jointUniform_of_countMod2_eq_zero {a a' x y : ℕ} (ha : 0 < a) (ha' : 0 < a')
    (hzero : ∀ N, countMod2 (enum b D) (fun n => sumDigits b (enum b D n)) a a' x y N = 0) :
    ¬ JointUniform b D a a' := by
  intro hJ
  have h0 : Tendsto (densityMod2 (enum b D) (fun n => sumDigits b (enum b D n)) a a' x y)
      atTop (nhds 0) := by
    refine Tendsto.congr (fun N => ?_) tendsto_const_nhds
    rw [densityMod2, hzero N]
    simp
  have huniq := tendsto_nhds_unique (hJ x y) h0
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have ha'R : (0 : ℝ) < (a' : ℝ) := by exact_mod_cast ha'
  rw [inv_eq_zero] at huniq
  nlinarith [huniq]

/-- Blueprint: `thm:modularJoint` (3), first case.  If `gcd(a, s) > 1` the
limiting distribution is not uniform: every `κ(n)` is divisible by `s`. -/
theorem not_jointUniform_of_gcd_enum (h : Standing b D) {a a' : ℕ} (ha : 0 < a) (ha' : 0 < a')
    (hgcd : 1 < Nat.gcd a (stepSize D)) : ¬ JointUniform b D a a' := by
  classical
  refine not_jointUniform_of_countMod2_eq_zero (x := 1) (y := 0) ha ha' fun N => ?_
  rw [countMod2, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro n - ⟨h1, -⟩
  have hda : Nat.gcd a (stepSize D) ∣ a := Nat.gcd_dvd_left _ _
  have hdk : Nat.gcd a (stepSize D) ∣ enum b D n :=
    (Nat.gcd_dvd_right a (stepSize D)).trans (stepSize_dvd_enum h n)
  have hmod : enum b D n ≡ 1 [MOD Nat.gcd a (stepSize D)] := Nat.ModEq.of_dvd hda h1
  have hmod0 : enum b D n ≡ 0 [MOD Nat.gcd a (stepSize D)] := (Nat.modEq_zero_iff_dvd).2 hdk
  have hone : (1 : ℕ) ≡ 0 [MOD Nat.gcd a (stepSize D)] := hmod.symm.trans hmod0
  have hd1 : Nat.gcd a (stepSize D) ∣ 1 := (Nat.modEq_zero_iff_dvd).1 hone
  have := Nat.le_of_dvd one_pos hd1
  omega

/-- Blueprint: `thm:modularJoint` (3), second case.  If `gcd(a', s) > 1` the
limiting distribution is not uniform: every `s_b(κ(n))` is divisible by `s`. -/
theorem not_jointUniform_of_gcd_sumDigits (h : Standing b D) {a a' : ℕ} (ha : 0 < a)
    (ha' : 0 < a') (hgcd : 1 < Nat.gcd a' (stepSize D)) : ¬ JointUniform b D a a' := by
  classical
  refine not_jointUniform_of_countMod2_eq_zero (x := 0) (y := 1) ha ha' fun N => ?_
  rw [countMod2, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro n - ⟨-, h2⟩
  have hda : Nat.gcd a' (stepSize D) ∣ a' := Nat.gcd_dvd_left _ _
  have hdk : Nat.gcd a' (stepSize D) ∣ sumDigits b (enum b D n) :=
    (Nat.gcd_dvd_right a' (stepSize D)).trans (stepSize_dvd_sumDigits_enum h n)
  have hmod : sumDigits b (enum b D n) ≡ 1 [MOD Nat.gcd a' (stepSize D)] :=
    Nat.ModEq.of_dvd hda h2
  have hmod0 : sumDigits b (enum b D n) ≡ 0 [MOD Nat.gcd a' (stepSize D)] :=
    (Nat.modEq_zero_iff_dvd).2 hdk
  have hone : (1 : ℕ) ≡ 0 [MOD Nat.gcd a' (stepSize D)] := hmod.symm.trans hmod0
  have hd1 : Nat.gcd a' (stepSize D) ∣ 1 := (Nat.modEq_zero_iff_dvd).1 hone
  have := Nat.le_of_dvd one_pos hd1
  omega

/-- Blueprint: `thm:modularJoint` (3), third case.  If `gcd(a, a', b-1) > 1`
the limiting distribution is not uniform: `κ(n) ≡ s_b(κ(n)) mod (b-1)`, so the
distribution is supported on a diagonal. -/
theorem not_jointUniform_of_gcd_sub_one (h : Standing b D) {a a' : ℕ} (ha : 0 < a)
    (ha' : 0 < a') (hgcd : 1 < Nat.gcd a (Nat.gcd a' (b - 1))) :
    ¬ JointUniform b D a a' := by
  classical
  refine not_jointUniform_of_countMod2_eq_zero (x := 0) (y := 1) ha ha' fun N => ?_
  rw [countMod2, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro n - ⟨h1, h2⟩
  have hda : Nat.gcd a (Nat.gcd a' (b - 1)) ∣ a := Nat.gcd_dvd_left _ _
  have hda' : Nat.gcd a (Nat.gcd a' (b - 1)) ∣ a' :=
    (Nat.gcd_dvd_right a _).trans (Nat.gcd_dvd_left _ _)
  have hdb : Nat.gcd a (Nat.gcd a' (b - 1)) ∣ b - 1 :=
    (Nat.gcd_dvd_right a _).trans (Nat.gcd_dvd_right _ _)
  have hk0 : enum b D n ≡ 0 [MOD Nat.gcd a (Nat.gcd a' (b - 1))] := Nat.ModEq.of_dvd hda h1
  have hs1 : sumDigits b (enum b D n) ≡ 1 [MOD Nat.gcd a (Nat.gcd a' (b - 1))] :=
    Nat.ModEq.of_dvd hda' h2
  have hks : enum b D n ≡ sumDigits b (enum b D n) [MOD Nat.gcd a (Nat.gcd a' (b - 1))] :=
    Nat.ModEq.of_dvd hdb (modEq_sumDigits h.three_le_base _)
  have hone : (1 : ℕ) ≡ 0 [MOD Nat.gcd a (Nat.gcd a' (b - 1))] :=
    (hs1.symm.trans (hks.symm.trans hk0))
  have hd1 : Nat.gcd a (Nat.gcd a' (b - 1)) ∣ 1 := (Nat.modEq_zero_iff_dvd).1 hone
  have := Nat.le_of_dvd one_pos hd1
  omega

end IntegerCantorSet
