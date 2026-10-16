/-
Polynomial uniform distribution.

Blueprint: `blueprint/src/content.tex`, Chapter 5 (`chap:pudu`); Section 4 of
the paper, Theorem 4.3.

The sequence `x_n = (κ(n), s_b(κ(n)))` is *PUDU*: for every two-variable real
polynomial `p` having an irrational coefficient on some non-constant monomial,
the averages of `e(p(x_n))` over a window `M ≤ n < N` tend to `0` as
`N - M → ∞`.
-/
import IntegerCantorSets.ExpSum

namespace IntegerCantorSet

open Finset Filter MvPolynomial
open scoped Real

variable {b : ℕ} {D : Finset ℕ}

/-! ### Monomials in two variables -/

/-- The monomial `X^a Y^c`, as an exponent vector. -/
noncomputable def mono2 (a c : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 a + Finsupp.single 1 c

@[simp] theorem mono2_apply_zero (a c : ℕ) : mono2 a c 0 = a := by
  simp [mono2]

@[simp] theorem mono2_apply_one (a c : ℕ) : mono2 a c 1 = c := by
  simp [mono2]

theorem finsupp_fin2_ext {m m' : Fin 2 →₀ ℕ} (h0 : m 0 = m' 0) (h1 : m 1 = m' 1) :
    m = m' := by
  refine Finsupp.ext fun a => ?_
  fin_cases a
  · exact h0
  · exact h1

theorem mono2_self (m : Fin 2 →₀ ℕ) : mono2 (m 0) (m 1) = m :=
  finsupp_fin2_ext (by simp) (by simp)

theorem mono2_eq_zero_iff {a c : ℕ} : mono2 a c = 0 ↔ a = 0 ∧ c = 0 := by
  constructor
  · intro h
    constructor
    · simpa using congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
    · simpa using congrArg (fun f : Fin 2 →₀ ℕ => f 1) h
  · rintro ⟨rfl, rfl⟩
    exact finsupp_fin2_ext (by simp) (by simp)

/-- The total degree of a two-variable monomial. -/
theorem sum_support_eq (m : Fin 2 →₀ ℕ) : ∑ i ∈ m.support, m i = m 0 + m 1 := by
  classical
  have : m.support ⊆ ({0, 1} : Finset (Fin 2)) := fun a _ => by fin_cases a <;> simp
  rw [Finset.sum_subset this (by intro x _ hx; simpa using Finsupp.notMem_support_iff.1 hx)]
  simp

/-! ### Irrational polynomials -/

/-- Blueprint: `def:irrationalPoly`.  A polynomial in two variables over `ℝ`
is *irrational* when some non-constant monomial has an irrational
coefficient. -/
def IsIrrationalPoly (p : MvPolynomial (Fin 2) ℝ) : Prop :=
  ∃ m : Fin 2 →₀ ℕ, m ≠ 0 ∧ Irrational (p.coeff m)

/-- The *irrational degree* of `p` is at most `l`: every monomial of total
degree exceeding `l` has a rational coefficient. -/
def IrrDegLE (p : MvPolynomial (Fin 2) ℝ) (l : ℕ) : Prop :=
  ∀ m : Fin 2 →₀ ℕ, l < m 0 + m 1 → ¬ Irrational (p.coeff m)

theorem IrrDegLE.mono {p : MvPolynomial (Fin 2) ℝ} {l l' : ℕ} (h : IrrDegLE p l)
    (hl : l ≤ l') : IrrDegLE p l' := fun m hm => h m (lt_of_le_of_lt hl hm)

/-- Every polynomial has irrational degree at most its total degree. -/
theorem irrDegLE_totalDegree (p : MvPolynomial (Fin 2) ℝ) :
    IrrDegLE p p.totalDegree := by
  intro m hm
  have : p.coeff m = 0 := by
    refine MvPolynomial.coeff_eq_zero_of_totalDegree_lt ?_
    rw [sum_support_eq]
    exact hm
  rw [this]
  simp

/-- A polynomial of irrational degree at most `1` which is irrational has an
irrational coefficient on `X` or on `Y`. -/
theorem irrational_coeff_of_irrDegLE_one {p : MvPolynomial (Fin 2) ℝ}
    (h1 : IrrDegLE p 1) (hp : IsIrrationalPoly p) :
    Irrational (p.coeff (mono2 1 0)) ∨ Irrational (p.coeff (mono2 0 1)) := by
  obtain ⟨m, hm0, hm⟩ := hp
  have hle : m 0 + m 1 ≤ 1 := by
    by_contra hc
    exact h1 m (by omega) hm
  have hne : ¬ (m 0 = 0 ∧ m 1 = 0) := by
    rintro ⟨h0, h1'⟩
    exact hm0 (finsupp_fin2_ext (by simpa using h0) (by simpa using h1'))
  rcases Nat.eq_zero_or_pos (m 0) with h0 | h0
  · have h1' : m 1 = 1 := by omega
    right
    rw [← mono2_self m, h0, h1'] at hm
    exact hm
  · have h0' : m 0 = 1 := by omega
    have h1' : m 1 = 0 := by omega
    left
    rw [← mono2_self m, h0', h1'] at hm
    exact hm

/-! ### PUDU -/

/-- `p` evaluated at an integer point of the plane. -/
noncomputable def polyEval (p : MvPolynomial (Fin 2) ℝ) (x : Fin 2 → ℤ) : ℝ :=
  eval (fun i => ((x i : ℤ) : ℝ)) p

/-- Blueprint: `def:PUDU`.  The sequence `x` in `ℤ²` is *polynomially uniformly
distributed* when, for every irrational polynomial `p`, the averages of
`e(p(xₙ))` over a window `M ≤ n < N` tend to `0` uniformly as `N - M → ∞`. -/
def IsPUDU (x : ℕ → Fin 2 → ℤ) : Prop :=
  ∀ p : MvPolynomial (Fin 2) ℝ, IsIrrationalPoly p →
    ∀ ε > 0, ∃ K : ℕ, ∀ M N : ℕ, M + K ≤ N →
      ‖((N - M : ℕ) : ℂ)⁻¹ * ∑ n ∈ Ico M N, expc (polyEval p (x n))‖ < ε

/-- The averaging statement of `IsPUDU` for a single polynomial. -/
def UniformAvg (x : ℕ → Fin 2 → ℤ) (p : MvPolynomial (Fin 2) ℝ) : Prop :=
  ∀ ε > 0, ∃ K : ℕ, ∀ M N : ℕ, M + K ≤ N →
    ‖((N - M : ℕ) : ℂ)⁻¹ * ∑ n ∈ Ico M N, expc (polyEval p (x n))‖ < ε

/-- The Cantor-set sequence `n ↦ (κ(n), s_b(κ(n)))`. -/
def cantorSeq (b : ℕ) (D : Finset ℕ) (n : ℕ) : Fin 2 → ℤ :=
  ![(enum b D n : ℤ), (sumDigits b (enum b D n) : ℤ)]

/-! ### Bad directions -/

/-- The derivative of `p` in the integer direction `w`. -/
noncomputable def dirDeriv (w : ℤ × ℤ) (p : MvPolynomial (Fin 2) ℝ) :
    MvPolynomial (Fin 2) ℝ :=
  C (w.1 : ℝ) * pderiv 0 p + C (w.2 : ℝ) * pderiv 1 p

theorem coeff_dirDeriv (w : ℤ × ℤ) (p : MvPolynomial (Fin 2) ℝ) (m : Fin 2 →₀ ℕ) :
    (dirDeriv w p).coeff m =
      (w.1 : ℝ) * (p.coeff (m + Finsupp.single 0 1) * ((m 0 : ℝ) + 1)) +
      (w.2 : ℝ) * (p.coeff (m + Finsupp.single 1 1) * ((m 1 : ℝ) + 1)) := by
  have hadd : ∀ f g : MvPolynomial (Fin 2) ℝ, (f + g).coeff m = f.coeff m + g.coeff m :=
    fun _ _ => rfl
  rw [dirDeriv, hadd, coeff_C_mul, coeff_C_mul, coeff_pderiv, coeff_pderiv]

/-- The arithmetic core of `badDirections`: if `u` or `v` is irrational, the
integer directions `w` with `w₁u + w₂v` rational lie on a rational line. -/
theorem exists_bad_direction {u v : ℝ} (h : Irrational u ∨ Irrational v) :
    ∃ c : ℤ × ℤ, c ≠ 0 ∧ ∀ w : ℤ × ℤ,
      ¬ Irrational ((w.1 : ℝ) * u + (w.2 : ℝ) * v) → c.1 * w.1 + c.2 * w.2 = 0 := by
  classical
  by_cases hK : ∀ w : ℤ × ℤ, ¬ Irrational ((w.1 : ℝ) * u + (w.2 : ℝ) * v) → w = 0
  · refine ⟨(1, 0), by simp, fun w hw => ?_⟩
    rw [hK w hw]
    simp
  · push Not at hK
    obtain ⟨w₀, hw₀, hw₀ne⟩ := hK
    refine ⟨(-w₀.2, w₀.1), ?_, fun w hw => ?_⟩
    · intro hc
      apply hw₀ne
      have h1 : -w₀.2 = 0 := congrArg Prod.fst hc
      have h2 : w₀.1 = 0 := congrArg Prod.snd hc
      have h3 : w₀.2 = 0 := by omega
      rw [Prod.ext_iff]
      exact ⟨by simpa using h2, by simpa using h3⟩
    · obtain ⟨r, hr⟩ := exists_rat_of_not_irrational hw
      obtain ⟨r₀, hr₀⟩ := exists_rat_of_not_irrational hw₀
      have hdv : ((w₀.1 * w.2 - w₀.2 * w.1 : ℤ) : ℝ) * v
          = (w₀.1 : ℝ) * (r : ℝ) - (w.1 : ℝ) * (r₀ : ℝ) := by
        rw [← hr, ← hr₀]; push_cast; ring
      have hdu : ((w₀.1 * w.2 - w₀.2 * w.1 : ℤ) : ℝ) * u
          = (w.2 : ℝ) * (r₀ : ℝ) - (w₀.2 : ℝ) * (r : ℝ) := by
        rw [← hr, ← hr₀]; push_cast; ring
      have hd0 : w₀.1 * w.2 - w₀.2 * w.1 = 0 := by
        by_contra hdne
        rcases h with hu | hv
        · exact (hu.intCast_mul hdne) ⟨(w.2 : ℚ) * r₀ - (w₀.2 : ℚ) * r, by
            rw [hdu]; push_cast; ring⟩
        · exact (hv.intCast_mul hdne) ⟨(w₀.1 : ℚ) * r - (w.1 : ℚ) * r₀, by
            rw [hdv]; push_cast; ring⟩
      show (-w₀.2) * w.1 + w₀.1 * w.2 = 0
      linarith [hd0]

/-- Blueprint: `lem:badDirections`.  If some monomial of total degree `l ≥ 1`
has an irrational coefficient, there is a non-zero integer direction
`(c₁, c₂)` such that every integer direction `w` whose derivative
`∂_w p` has only rational coefficients in degree `l - 1` satisfies
`c₁ w₁ + c₂ w₂ = 0`. -/
theorem badDirections (p : MvPolynomial (Fin 2) ℝ) {l : ℕ} (hl : 1 ≤ l)
    {m₀ : Fin 2 →₀ ℕ} (hm₀ : m₀ 0 + m₀ 1 = l) (hirr : Irrational (p.coeff m₀)) :
    ∃ c : ℤ × ℤ, c ≠ 0 ∧ ∀ w : ℤ × ℤ,
      (∀ m : Fin 2 →₀ ℕ, m 0 + m 1 = l - 1 →
        ¬ Irrational ((dirDeriv w p).coeff m)) →
      c.1 * w.1 + c.2 * w.2 = 0 := by
  classical
  rcases Nat.eq_zero_or_pos (m₀ 0) with h0 | h0
  · -- the irrational coefficient sits on a monomial involving `Y`
    have h1 : 1 ≤ m₀ 1 := by omega
    set m : Fin 2 →₀ ℕ := mono2 (m₀ 0) (m₀ 1 - 1) with hm
    have hmdeg : m 0 + m 1 = l - 1 := by simp [hm]; omega
    have hshift : m + Finsupp.single 1 1 = m₀ :=
      finsupp_fin2_ext (by simp [hm, Finsupp.single_apply]) (by simp [hm]; omega)
    have hv : Irrational (p.coeff (m + Finsupp.single 1 1) * (((m 1 : ℕ) : ℝ) + 1)) := by
      rw [hshift]
      have : (((m 1 : ℕ) : ℝ) + 1) = ((m₀ 1 : ℕ) : ℝ) := by
        simp [hm]; push_cast [Nat.cast_sub h1]; ring
      rw [this]
      exact hirr.mul_natCast (by omega)
    obtain ⟨c, hc, hcw⟩ := exists_bad_direction (Or.inr hv)
    refine ⟨c, hc, fun w hw => ?_⟩
    refine hcw w ?_
    have := hw m hmdeg
    rwa [coeff_dirDeriv] at this
  · -- the irrational coefficient sits on a monomial involving `X`
    set m : Fin 2 →₀ ℕ := mono2 (m₀ 0 - 1) (m₀ 1) with hm
    have hmdeg : m 0 + m 1 = l - 1 := by simp [hm]; omega
    have hshift : m + Finsupp.single 0 1 = m₀ :=
      finsupp_fin2_ext (by simp [hm]; omega) (by simp [hm, Finsupp.single_apply])
    have hu : Irrational (p.coeff (m + Finsupp.single 0 1) * (((m 0 : ℕ) : ℝ) + 1)) := by
      rw [hshift]
      have : (((m 0 : ℕ) : ℝ) + 1) = ((m₀ 0 : ℕ) : ℝ) := by
        simp [hm]; push_cast [Nat.cast_sub h0]; ring
      rw [this]
      exact hirr.mul_natCast (by omega)
    obtain ⟨c, hc, hcw⟩ := exists_bad_direction (Or.inl hu)
    refine ⟨c, hc, fun w hw => ?_⟩
    refine hcw w ?_
    have := hw m hmdeg
    rwa [coeff_dirDeriv] at this

/-! ### Non-exceptional pairs -/

theorem stepSize_pos (h : Standing b D) : 0 < stepSize D := by
  classical
  rcases Nat.eq_zero_or_pos (stepSize D) with hz | hpos
  · exfalso
    have hall : ∀ d ∈ D, d = 0 := by
      intro d hd
      have := (Finset.gcd_eq_zero_iff (s := D) (f := (id : ℕ → ℕ))).1 hz d hd
      simpa using this
    have h0 : (0 : ℕ) ∈ D := h.zero_mem
    have hsub : D ⊆ {0} := fun d hd => by simp [hall d hd]
    have : D.card ≤ 1 := by
      simpa using Finset.card_le_card hsub
    have := h.two_le_card
    omega
  · exact hpos

/-- An exceptional pair has both coordinates rational, so a pair with an
irrational coordinate is never exceptional. -/
theorem not_exceptional_of_irrational (h : Standing b D) {α β : ℝ}
    (hirr : Irrational α ∨ Irrational β) : ¬ Exceptional b D α β := by
  rintro ⟨a, r, t, ⟨k, hk⟩, ⟨k', hk'⟩⟩
  have hb3 : (3 : ℕ) ≤ b := h.three_le_base
  have hbR : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb3
  have hb1 : ((b : ℝ) - 1) ≠ 0 := by linarith
  have hb3Q : (3 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb3
  have hb1Q : ((b : ℚ) - 1) ≠ 0 := by intro hc; rw [sub_eq_zero] at hc; rw [hc] at hb3Q; norm_num at hb3Q
  have hbne : ((b : ℝ)) ≠ 0 := by linarith
  have hbneQ : ((b : ℚ)) ≠ 0 := by intro hc; rw [hc] at hb3Q; norm_num at hb3Q
  have hs : 0 < stepSize D := stepSize_pos h
  have hsR : ((stepSize D : ℕ) : ℝ) ≠ 0 := by positivity
  have hsQ : ((stepSize D : ℕ) : ℚ) ≠ 0 := by
    have : stepSize D ≠ 0 := by omega
    exact_mod_cast this
  have hαrat : ¬ Irrational α := by
    refine not_not_intro ⟨((a : ℚ) / ((b : ℚ) - 1) + (r : ℚ) / (b : ℚ) ^ t + (k : ℚ))
      / ((stepSize D : ℕ) : ℚ), ?_⟩
    have : α = ((a : ℝ) / ((b : ℝ) - 1) + (r : ℝ) / (b : ℝ) ^ t + (k : ℝ))
        / ((stepSize D : ℕ) : ℝ) := by
      rw [← hk]; field_simp
    rw [this]
    push_cast
    ring
  have hβrat : ¬ Irrational β := by
    refine not_not_intro ⟨(-((a : ℚ) / ((b : ℚ) - 1)) + (k' : ℚ))
      / ((stepSize D : ℕ) : ℚ), ?_⟩
    have : β = (-((a : ℝ) / ((b : ℝ) - 1)) + (k' : ℝ)) / ((stepSize D : ℕ) : ℝ) := by
      rw [← hk']; field_simp
    rw [this]
    push_cast
    ring
  rcases hirr with hα | hβ
  · exact hαrat hα
  · exact hβrat hβ

/-! ### Characters and finite Fourier analysis modulo `q` -/

theorem expc_intCast (k : ℤ) : expc (k : ℝ) = 1 := expc_eq_one_iff.2 ⟨k, rfl⟩

theorem expc_eq_of_sub_int {x y : ℝ} (h : ∃ k : ℤ, x - y = k) : expc x = expc y := by
  obtain ⟨k, hk⟩ := h
  have hx : x = y + (k : ℝ) := by linarith
  rw [hx, expc_add, expc_intCast, mul_one]

theorem expc_natCast_mul (t : ℕ) (x : ℝ) : expc ((t : ℝ) * x) = expc x ^ t := by
  have h := expc_zpow (t : ℤ) x
  rw [zpow_natCast] at h
  simpa using h

/-- Orthogonality of the additive characters of `ℤ/q`. -/
theorem sum_expc_orthogonality {q : ℕ} (hq : 0 < q) (z : ℤ) :
    ∑ t ∈ range q, expc ((t : ℝ) * (z : ℝ) / (q : ℝ))
      = if (q : ℤ) ∣ z then (q : ℂ) else 0 := by
  have hqR : ((q : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hterm : ∀ t ∈ range q,
      expc ((t : ℝ) * (z : ℝ) / (q : ℝ)) = expc ((z : ℝ) / (q : ℝ)) ^ t := by
    intro t _
    rw [← expc_natCast_mul]
    congr 1
    field_simp
  rw [Finset.sum_congr rfl hterm]
  by_cases hdvd : (q : ℤ) ∣ z
  · obtain ⟨c, hc⟩ := id hdvd
    have hz1 : expc ((z : ℝ) / (q : ℝ)) = 1 := by
      refine expc_eq_one_iff.2 ⟨c, ?_⟩
      have : (z : ℝ) = (q : ℝ) * (c : ℝ) := by exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) hc
      rw [this]
      field_simp
    simp [hz1, hdvd]
  · have hzne : expc ((z : ℝ) / (q : ℝ)) ≠ 1 := by
      intro h1
      obtain ⟨k, hk⟩ := expc_eq_one_iff.1 h1
      refine hdvd ⟨k, ?_⟩
      have : (z : ℝ) = (q : ℝ) * (k : ℝ) := by
        field_simp at hk
        linarith [hk]
      exact_mod_cast this
    have hzq : expc ((z : ℝ) / (q : ℝ)) ^ q = 1 := by
      rw [← expc_natCast_mul]
      have : (q : ℝ) * ((z : ℝ) / (q : ℝ)) = (z : ℝ) := by field_simp
      rw [this, expc_intCast]
    rw [geom_sum_eq hzne, hzq]
    simp [hdvd]

/-- Reordering a four-fold sum. -/
theorem sum_comm4 {M : Type*} [AddCommMonoid M] {ι : Type*} (s : Finset ι)
    (F : ι → ι → ι → ι → M) :
    (∑ a ∈ s, ∑ c ∈ s, ∑ u ∈ s, ∑ v ∈ s, F a c u v)
      = ∑ u ∈ s, ∑ v ∈ s, ∑ a ∈ s, ∑ c ∈ s, F a c u v := by
  calc (∑ a ∈ s, ∑ c ∈ s, ∑ u ∈ s, ∑ v ∈ s, F a c u v)
      = ∑ a ∈ s, ∑ u ∈ s, ∑ c ∈ s, ∑ v ∈ s, F a c u v :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ u ∈ s, ∑ a ∈ s, ∑ c ∈ s, ∑ v ∈ s, F a c u v := Finset.sum_comm
    _ = ∑ u ∈ s, ∑ a ∈ s, ∑ v ∈ s, ∑ c ∈ s, F a c u v :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ u ∈ s, ∑ v ∈ s, ∑ a ∈ s, ∑ c ∈ s, F a c u v :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-! ### Polynomials with rational coefficients -/

/-- A polynomial all of whose coefficients are rational has a common
denominator. -/
theorem exists_common_denom {g : MvPolynomial (Fin 2) ℝ}
    (hg : ∀ m : Fin 2 →₀ ℕ, ¬ Irrational (g.coeff m)) :
    ∃ q : ℕ, 0 < q ∧ ∀ m : Fin 2 →₀ ℕ, ∃ z : ℤ, (q : ℝ) * g.coeff m = z := by
  classical
  choose rr hrr using fun m : Fin 2 →₀ ℕ => exists_rat_of_not_irrational (hg m)
  refine ⟨∏ d ∈ g.support, (rr d).den, Finset.prod_pos fun d _ => (rr d).pos, ?_⟩
  intro m
  by_cases hm : m ∈ g.support
  · obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun d => (rr d).den) hm
    refine ⟨(c : ℤ) * (rr m).num, ?_⟩
    have hQ : ((∏ d ∈ g.support, (rr d).den : ℕ) : ℚ) * rr m
        = (((c : ℤ) * (rr m).num : ℤ) : ℚ) := by
      rw [hc]
      push_cast
      rw [mul_comm ((rr m).den : ℚ) (c : ℚ), mul_assoc, Rat.den_mul_eq_num]
    have := congrArg (fun z : ℚ => (z : ℝ)) hQ
    push_cast at this ⊢
    rw [hrr m]
    exact_mod_cast this
  · refine ⟨0, ?_⟩
    rw [MvPolynomial.notMem_support_iff.1 hm]
    simp

/-- The value of a polynomial with common denominator `q` changes by an
integer when the arguments are changed modulo `q`. -/
theorem polyEval_sub_int_of_dvd {g : MvPolynomial (Fin 2) ℝ} {q : ℕ} (hq : 0 < q)
    (hden : ∀ m : Fin 2 →₀ ℕ, ∃ z : ℤ, (q : ℝ) * g.coeff m = z)
    {x y x' y' : ℤ} (hx : (q : ℤ) ∣ (x - x')) (hy : (q : ℤ) ∣ (y - y')) :
    ∃ k : ℤ, polyEval g ![x, y] - polyEval g ![x', y'] = k := by
  classical
  choose zz hzz using hden
  have hqR : ((q : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have heval : ∀ u v : ℤ, (q : ℝ) * polyEval g ![u, v]
      = ((∑ d ∈ g.support, zz d * (u ^ d 0 * v ^ d 1) : ℤ) : ℝ) := by
    intro u v
    rw [polyEval, eval_eq', Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Fin.prod_univ_two]
    rw [← mul_assoc, hzz d]
    simp
  have hxm : x ≡ x' [ZMOD (q : ℤ)] := (Int.modEq_iff_dvd.2 hx).symm
  have hym : y ≡ y' [ZMOD (q : ℤ)] := (Int.modEq_iff_dvd.2 hy).symm
  have hmod : (∑ d ∈ g.support, zz d * (x ^ d 0 * y ^ d 1))
      ≡ (∑ d ∈ g.support, zz d * (x' ^ d 0 * y' ^ d 1)) [ZMOD (q : ℤ)] :=
    Int.ModEq.sum fun d _ => Int.ModEq.mul_left _ ((hxm.pow _).mul (hym.pow _))
  obtain ⟨c, hc⟩ := Int.modEq_iff_dvd.1 hmod.symm
  refine ⟨c, ?_⟩
  have hdiff : (q : ℝ) * (polyEval g ![x, y] - polyEval g ![x', y'])
      = (q : ℝ) * (c : ℝ) := by
    rw [mul_sub, heval x y, heval x' y', ← Int.cast_sub, hc]
    push_cast
    ring
  have := mul_left_cancel₀ hqR hdiff
  exact this

/-- For `u < q`, the residue `u` is determined by divisibility of `x - u`. -/
theorem dvd_sub_natCast_iff {q : ℕ} (hq : 0 < q) (x : ℤ) {u : ℕ} (hu : u < q) :
    ((q : ℤ) ∣ (x - u)) ↔ u = (x % (q : ℤ)).toNat := by
  have hqz : ((q : ℤ)) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hnn : 0 ≤ x % (q : ℤ) := Int.emod_nonneg x hqz
  constructor
  · intro hd
    have h1 : (u : ℤ) ≡ x [ZMOD (q : ℤ)] := Int.modEq_iff_dvd.2 hd
    have h2 : (u : ℤ) % (q : ℤ) = x % (q : ℤ) := h1
    have h3 : (u : ℤ) % (q : ℤ) = (u : ℤ) :=
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hu)
    rw [h3] at h2
    rw [← h2]
    simp
  · rintro rfl
    rw [Int.toNat_of_nonneg hnn]
    exact Int.dvd_self_sub_emod

theorem sum_sum_mul_mul (q : ℕ) (A B C : ℂ) (f1 f2 : ℕ → ℂ) :
    ∑ s ∈ range q, ∑ t ∈ range q, A * (B * (C * (f1 s * f2 t)))
      = A * (B * (C * ((∑ s ∈ range q, f1 s) * (∑ t ∈ range q, f2 t)))) := by
  have hinner : ∀ s : ℕ, ∑ t ∈ range q, A * (B * (C * (f1 s * f2 t)))
      = (A * B * C * f1 s) * ∑ t ∈ range q, f2 t := by
    intro s
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  rw [Finset.sum_congr rfl (fun s _ => hinner s), ← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- The finite Fourier coefficients of `(x, y) ↦ e(g(x, y))`, a function of
`(x, y)` modulo `q`. -/
noncomputable def fourierCoeff (g : MvPolynomial (Fin 2) ℝ) (q s t : ℕ) : ℂ :=
  (q : ℂ)⁻¹ * (q : ℂ)⁻¹ * ∑ u ∈ range q, ∑ v ∈ range q,
    expc (polyEval g ![(u : ℤ), (v : ℤ)]) * expc (-((s : ℝ) * u + (t : ℝ) * v) / (q : ℝ))

/-- Finite Fourier expansion of `e(g(x,y))` for `g` with denominator `q`. -/
theorem fourier_expansion {g : MvPolynomial (Fin 2) ℝ} {q : ℕ} (hq : 0 < q)
    (hden : ∀ m : Fin 2 →₀ ℕ, ∃ z : ℤ, (q : ℝ) * g.coeff m = z) (x y : ℤ) :
    expc (polyEval g ![x, y])
      = ∑ s ∈ range q, ∑ t ∈ range q, fourierCoeff g q s t
          * expc (((s : ℝ) * (x : ℝ) + (t : ℝ) * (y : ℝ)) / (q : ℝ)) := by
  classical
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hqR : ((q : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  -- Step 1: expand the Fourier coefficient into a four-fold sum.
  have step1 : (∑ s ∈ range q, ∑ t ∈ range q, fourierCoeff g q s t
        * expc (((s : ℝ) * (x : ℝ) + (t : ℝ) * (y : ℝ)) / (q : ℝ)))
      = ∑ s ∈ range q, ∑ t ∈ range q, ∑ u ∈ range q, ∑ v ∈ range q,
          (q : ℂ)⁻¹ * ((q : ℂ)⁻¹ * (expc (polyEval g ![(u : ℤ), (v : ℤ)])
            * (expc ((s : ℝ) * ((x : ℝ) - (u : ℝ)) / (q : ℝ))
              * expc ((t : ℝ) * ((y : ℝ) - (v : ℝ)) / (q : ℝ))))) := by
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    simp only [fourierCoeff, mul_assoc, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    have hchar : expc (-((s : ℝ) * u + (t : ℝ) * v) / (q : ℝ))
          * expc (((s : ℝ) * (x : ℝ) + (t : ℝ) * (y : ℝ)) / (q : ℝ))
        = expc ((s : ℝ) * ((x : ℝ) - (u : ℝ)) / (q : ℝ))
          * expc ((t : ℝ) * ((y : ℝ) - (v : ℝ)) / (q : ℝ)) := by
      rw [← expc_add, ← expc_add]
      congr 1
      field_simp
      ring
    rw [hchar]
  -- Step 2: reorder, and carry out the sums over `s` and `t`.
  have step2 : (∑ s ∈ range q, ∑ t ∈ range q, ∑ u ∈ range q, ∑ v ∈ range q,
          (q : ℂ)⁻¹ * ((q : ℂ)⁻¹ * (expc (polyEval g ![(u : ℤ), (v : ℤ)])
            * (expc ((s : ℝ) * ((x : ℝ) - (u : ℝ)) / (q : ℝ))
              * expc ((t : ℝ) * ((y : ℝ) - (v : ℝ)) / (q : ℝ))))))
      = ∑ u ∈ range q, ∑ v ∈ range q,
          (q : ℂ)⁻¹ * ((q : ℂ)⁻¹ * (expc (polyEval g ![(u : ℤ), (v : ℤ)])
            * ((if (q : ℤ) ∣ (x - (u : ℤ)) then (q : ℂ) else 0)
              * (if (q : ℤ) ∣ (y - (v : ℤ)) then (q : ℂ) else 0)))) := by
    rw [sum_comm4]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    have hx : (∑ s ∈ range q, expc ((s : ℝ) * ((x : ℝ) - (u : ℝ)) / (q : ℝ)))
        = if (q : ℤ) ∣ (x - (u : ℤ)) then (q : ℂ) else 0 := by
      rw [← sum_expc_orthogonality hq (x - (u : ℤ))]
      refine Finset.sum_congr rfl fun s _ => ?_
      congr 1
      push_cast
      ring
    have hy : (∑ t ∈ range q, expc ((t : ℝ) * ((y : ℝ) - (v : ℝ)) / (q : ℝ)))
        = if (q : ℤ) ∣ (y - (v : ℤ)) then (q : ℂ) else 0 := by
      rw [← sum_expc_orthogonality hq (y - (v : ℤ))]
      refine Finset.sum_congr rfl fun t _ => ?_
      congr 1
      push_cast
      ring
    rw [sum_sum_mul_mul, hx, hy]
  -- Step 3: only the residue class of `(x, y)` survives.
  set u₀ : ℕ := (x % (q : ℤ)).toNat with hu₀
  set v₀ : ℕ := (y % (q : ℤ)).toNat with hv₀
  have hu₀mem : u₀ ∈ range q := by
    rw [Finset.mem_range, hu₀]
    have h1 : x % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos x (by exact_mod_cast hq)
    omega
  have hv₀mem : v₀ ∈ range q := by
    rw [Finset.mem_range, hv₀]
    have h1 : y % (q : ℤ) < (q : ℤ) := Int.emod_lt_of_pos y (by exact_mod_cast hq)
    omega
  have hxdvd : (q : ℤ) ∣ (x - (u₀ : ℤ)) :=
    (dvd_sub_natCast_iff hq x (Finset.mem_range.1 hu₀mem)).2 rfl
  have hydvd : (q : ℤ) ∣ (y - (v₀ : ℤ)) :=
    (dvd_sub_natCast_iff hq y (Finset.mem_range.1 hv₀mem)).2 rfl
  have step3 : (∑ u ∈ range q, ∑ v ∈ range q,
          (q : ℂ)⁻¹ * ((q : ℂ)⁻¹ * (expc (polyEval g ![(u : ℤ), (v : ℤ)])
            * ((if (q : ℤ) ∣ (x - (u : ℤ)) then (q : ℂ) else 0)
              * (if (q : ℤ) ∣ (y - (v : ℤ)) then (q : ℂ) else 0)))))
      = expc (polyEval g ![(u₀ : ℤ), (v₀ : ℤ)]) := by
    rw [Finset.sum_eq_single_of_mem u₀ hu₀mem]
    · rw [Finset.sum_eq_single_of_mem v₀ hv₀mem]
      · rw [if_pos hxdvd, if_pos hydvd]
        field_simp
      · intro v hv hvne
        rw [if_neg (fun hc => hvne ((dvd_sub_natCast_iff hq y (Finset.mem_range.1 hv)).1 hc))]
        ring
    · intro u hu hune
      refine Finset.sum_eq_zero fun v _ => ?_
      rw [if_neg (fun hc => hune ((dvd_sub_natCast_iff hq x (Finset.mem_range.1 hu)).1 hc))]
      ring
  rw [step1, step2, step3]
  exact expc_eq_of_sub_int (polyEval_sub_int_of_dvd hq hden hxdvd hydvd)

/-! ### Splitting off the rational part -/

theorem mono2_one_zero : mono2 1 0 = Finsupp.single (0 : Fin 2) 1 := by
  simp [mono2]

theorem mono2_zero_one : mono2 0 1 = Finsupp.single (1 : Fin 2) 1 := by
  simp [mono2]

/-- `p` with its constant term and its two linear terms removed. -/
noncomputable def ratPart (p : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 2) ℝ :=
  p - C (p.coeff 0) - C (p.coeff (mono2 1 0)) * X 0 - C (p.coeff (mono2 0 1)) * X 1

theorem coeff_ratPart (p : MvPolynomial (Fin 2) ℝ) (m : Fin 2 →₀ ℕ) :
    (ratPart p).coeff m = p.coeff m - (if (0 : Fin 2 →₀ ℕ) = m then p.coeff 0 else 0)
      - p.coeff (mono2 1 0) * (if Finsupp.single (0 : Fin 2) 1 = m then 1 else 0)
      - p.coeff (mono2 0 1) * (if Finsupp.single (1 : Fin 2) 1 = m then 1 else 0) := by
  classical
  have hs : ∀ f g : MvPolynomial (Fin 2) ℝ, (f - g).coeff m = f.coeff m - g.coeff m :=
    fun _ _ => rfl
  rw [ratPart, hs, hs, hs, coeff_C, coeff_C_mul, coeff_C_mul, coeff_X, coeff_X]

/-- Every coefficient of `ratPart p` is rational when `p` has irrational
degree at most `1`. -/
theorem ratPart_coeff_rat {p : MvPolynomial (Fin 2) ℝ} (h1 : IrrDegLE p 1)
    (m : Fin 2 →₀ ℕ) : ¬ Irrational ((ratPart p).coeff m) := by
  classical
  rw [coeff_ratPart]
  by_cases hA : (0 : Fin 2 →₀ ℕ) = m
  · have hB : ¬ (Finsupp.single (0 : Fin 2) 1 = m) := by
      rw [← hA]
      intro hc
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) hc
      simp at this
    have hC : ¬ (Finsupp.single (1 : Fin 2) 1 = m) := by
      rw [← hA]
      intro hc
      have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) hc
      simp at this
    rw [if_pos hA, if_neg hB, if_neg hC, ← hA]
    simp
  · by_cases hB : (Finsupp.single (0 : Fin 2) 1 = m)
    · have hC : ¬ (Finsupp.single (1 : Fin 2) 1 = m) := by
        rw [← hB]
        intro hc
        have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) hc
        simp at this
      rw [if_neg hA, if_pos hB, if_neg hC, ← hB, ← mono2_one_zero]
      simp
    · by_cases hC : (Finsupp.single (1 : Fin 2) 1 = m)
      · rw [if_neg hA, if_neg hB, if_pos hC, ← hC, ← mono2_zero_one]
        simp
      · rw [if_neg hA, if_neg hB, if_neg hC]
        simp only [mul_zero, sub_zero]
        refine h1 m ?_
        by_contra hd
        have hle : m 0 + m 1 ≤ 1 := by omega
        rcases Nat.eq_zero_or_pos (m 0) with h0 | h0
        · rcases Nat.eq_zero_or_pos (m 1) with h1' | h1'
          · exact hA (finsupp_fin2_ext (by simp [h0]) (by simp [h1']))
          · refine hC (finsupp_fin2_ext ?_ ?_)
            · simp [Finsupp.single_apply, h0]
            · simp [Finsupp.single_apply]; omega
        · refine hB (finsupp_fin2_ext ?_ ?_)
          · simp [Finsupp.single_apply]; omega
          · simp [Finsupp.single_apply]; omega

theorem polyEval_eq_add_ratPart (p : MvPolynomial (Fin 2) ℝ) (x : Fin 2 → ℤ) :
    polyEval p x = p.coeff 0 + p.coeff (mono2 1 0) * ((x 0 : ℤ) : ℝ)
      + p.coeff (mono2 0 1) * ((x 1 : ℤ) : ℝ) + polyEval (ratPart p) x := by
  simp [polyEval, ratPart]

/-! ### The base case -/

/-- Blueprint: `thm:UD1`.  The conclusion of `IsPUDU` holds for every
polynomial of irrational degree `1`.  This is the first consumer of
`tendsto_expSum`. -/
theorem UD_one (h : Standing b D) {p : MvPolynomial (Fin 2) ℝ}
    (h1 : IrrDegLE p 1) (hp : IsIrrationalPoly p) :
    UniformAvg (cantorSeq b D) p := by
  classical
  have hαβ : Irrational (p.coeff (mono2 1 0)) ∨ Irrational (p.coeff (mono2 0 1)) :=
    irrational_coeff_of_irrDegLE_one h1 hp
  obtain ⟨q, hq, hden⟩ := exists_common_denom (ratPart_coeff_rat h1)
  have hqR : ((q : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  -- the shifted pairs are never exceptional
  have hnotexc : ∀ s t : ℕ, ¬ Exceptional b D
      (p.coeff (mono2 1 0) + (s : ℝ) / (q : ℝ))
      (p.coeff (mono2 0 1) + (t : ℝ) / (q : ℝ)) := by
    intro s t
    refine not_exceptional_of_irrational h ?_
    have hs : ((s : ℝ) / (q : ℝ)) = (((s : ℚ) / (q : ℚ) : ℚ) : ℝ) := by push_cast; ring
    have ht : ((t : ℝ) / (q : ℝ)) = (((t : ℚ) / (q : ℚ) : ℚ) : ℝ) := by push_cast; ring
    rcases hαβ with hα | hβ
    · exact Or.inl (by rw [hs]; exact Irrational.add_ratCast ((s : ℚ) / (q : ℚ)) hα)
    · exact Or.inr (by rw [ht]; exact Irrational.add_ratCast ((t : ℚ) / (q : ℚ)) hβ)
  -- the pointwise Fourier expansion of the summand
  have hpoint : ∀ n : ℕ, expc (polyEval p (cantorSeq b D n))
      = ∑ s ∈ range q, ∑ t ∈ range q,
          (expc (p.coeff 0) * fourierCoeff (ratPart p) q s t)
            * expPhi b D (p.coeff (mono2 1 0) + (s : ℝ) / (q : ℝ))
                (p.coeff (mono2 0 1) + (t : ℝ) / (q : ℝ)) n := by
    intro n
    have hseq : cantorSeq b D n
        = ![(enum b D n : ℤ), (sumDigits b (enum b D n) : ℤ)] := rfl
    rw [polyEval_eq_add_ratPart p (cantorSeq b D n), hseq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [expc_add, fourier_expansion hq hden (enum b D n : ℤ)
        (sumDigits b (enum b D n) : ℤ), Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hcomb : expc (p.coeff 0
            + p.coeff (mono2 1 0) * ((enum b D n : ℤ) : ℝ)
            + p.coeff (mono2 0 1) * ((sumDigits b (enum b D n) : ℤ) : ℝ))
          * expc (((s : ℝ) * ((enum b D n : ℤ) : ℝ)
              + (t : ℝ) * ((sumDigits b (enum b D n) : ℤ) : ℝ)) / (q : ℝ))
        = expc (p.coeff 0)
          * expPhi b D (p.coeff (mono2 1 0) + (s : ℝ) / (q : ℝ))
              (p.coeff (mono2 0 1) + (t : ℝ) / (q : ℝ)) n := by
      rw [expPhi, ← expc_add, ← expc_add]
      congr 1
      push_cast
      field_simp
      ring
    calc expc (p.coeff 0 + p.coeff (mono2 1 0) * ((enum b D n : ℤ) : ℝ)
            + p.coeff (mono2 0 1) * ((sumDigits b (enum b D n) : ℤ) : ℝ))
          * (fourierCoeff (ratPart p) q s t
            * expc (((s : ℝ) * ((enum b D n : ℤ) : ℝ)
              + (t : ℝ) * ((sumDigits b (enum b D n) : ℤ) : ℝ)) / (q : ℝ)))
        = fourierCoeff (ratPart p) q s t
            * (expc (p.coeff 0 + p.coeff (mono2 1 0) * ((enum b D n : ℤ) : ℝ)
                + p.coeff (mono2 0 1) * ((sumDigits b (enum b D n) : ℤ) : ℝ))
              * expc (((s : ℝ) * ((enum b D n : ℤ) : ℝ)
                + (t : ℝ) * ((sumDigits b (enum b D n) : ℤ) : ℝ)) / (q : ℝ))) := by ring
      _ = _ := by rw [hcomb]; ring
  -- the uniform bound
  intro ε hε
  set Bnd : ℝ := ∑ s ∈ range q, ∑ t ∈ range q, ‖fourierCoeff (ratPart p) q s t‖ with hBnd
  have hBnn : 0 ≤ Bnd := by
    rw [hBnd]
    exact Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun t _ => norm_nonneg _
  have hB1 : (0 : ℝ) < Bnd + 1 := by linarith
  have hKex : ∀ s t : ℕ, ∃ Kst : ℕ, ∀ M N : ℕ, M + Kst ≤ N →
      ‖((N - M : ℕ) : ℂ)⁻¹ * ∑ n ∈ Ico M N,
          expPhi b D (p.coeff (mono2 1 0) + (s : ℝ) / (q : ℝ))
            (p.coeff (mono2 0 1) + (t : ℝ) / (q : ℝ)) n‖ < ε / (Bnd + 1) := by
    intro s t
    obtain ⟨L, _, hL⟩ := tendsto_expSum h (p.coeff (mono2 1 0) + (s : ℝ) / (q : ℝ))
      (p.coeff (mono2 0 1) + (t : ℝ) / (q : ℝ))
    obtain ⟨_, hunif⟩ := hL (hnotexc s t)
    exact hunif (ε / (Bnd + 1)) (by positivity)
  choose KK hKK using hKex
  refine ⟨(range q ×ˢ range q).sup (fun z : ℕ × ℕ => KK z.1 z.2), fun M N hMN => ?_⟩
  have hswap : ∑ n ∈ Ico M N, ∑ s ∈ range q, ∑ t ∈ range q,
        (expc (p.coeff 0) * fourierCoeff (ratPart p) q s t)
          * expPhi b D (p.coeff (mono2 1 0) + (s : ℝ) / (q : ℝ))
              (p.coeff (mono2 0 1) + (t : ℝ) / (q : ℝ)) n
      = ∑ s ∈ range q, ∑ t ∈ range q,
          (expc (p.coeff 0) * fourierCoeff (ratPart p) q s t)
            * ∑ n ∈ Ico M N, expPhi b D (p.coeff (mono2 1 0) + (s : ℝ) / (q : ℝ))
                (p.coeff (mono2 0 1) + (t : ℝ) / (q : ℝ)) n := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.mul_sum]
  have hsum : ((N - M : ℕ) : ℂ)⁻¹ * ∑ n ∈ Ico M N, expc (polyEval p (cantorSeq b D n))
      = ∑ s ∈ range q, ∑ t ∈ range q,
          (expc (p.coeff 0) * fourierCoeff (ratPart p) q s t)
            * (((N - M : ℕ) : ℂ)⁻¹ * ∑ n ∈ Ico M N,
                expPhi b D (p.coeff (mono2 1 0) + (s : ℝ) / (q : ℝ))
                  (p.coeff (mono2 0 1) + (t : ℝ) / (q : ℝ)) n) := by
    rw [Finset.sum_congr rfl (fun n _ => hpoint n), hswap, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  rw [hsum]
  have hterm : ∀ s ∈ range q, ∀ t ∈ range q,
      ‖(expc (p.coeff 0) * fourierCoeff (ratPart p) q s t)
        * (((N - M : ℕ) : ℂ)⁻¹ * ∑ n ∈ Ico M N,
            expPhi b D (p.coeff (mono2 1 0) + (s : ℝ) / (q : ℝ))
              (p.coeff (mono2 0 1) + (t : ℝ) / (q : ℝ)) n)‖
      ≤ ‖fourierCoeff (ratPart p) q s t‖ * (ε / (Bnd + 1)) := by
    intro s hs t ht
    have hle : KK s t ≤ (range q ×ˢ range q).sup (fun z : ℕ × ℕ => KK z.1 z.2) :=
      Finset.le_sup (f := fun z : ℕ × ℕ => KK z.1 z.2) (b := ((s, t) : ℕ × ℕ))
        (Finset.mem_product.2 ⟨hs, ht⟩)
    have havg := hKK s t M N (by omega)
    rw [norm_mul, norm_mul, norm_expc, one_mul]
    exact mul_le_mul_of_nonneg_left (le_of_lt havg) (norm_nonneg _)
  calc ‖∑ s ∈ range q, ∑ t ∈ range q,
          (expc (p.coeff 0) * fourierCoeff (ratPart p) q s t)
            * (((N - M : ℕ) : ℂ)⁻¹ * ∑ n ∈ Ico M N,
                expPhi b D (p.coeff (mono2 1 0) + (s : ℝ) / (q : ℝ))
                  (p.coeff (mono2 0 1) + (t : ℝ) / (q : ℝ)) n)‖
      ≤ ∑ s ∈ range q, ∑ t ∈ range q, ‖fourierCoeff (ratPart p) q s t‖ * (ε / (Bnd + 1)) := by
        refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun s hs => ?_)
        exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun t ht => hterm s hs t ht)
    _ = Bnd * (ε / (Bnd + 1)) := by
        rw [hBnd, Finset.sum_mul]
        exact Finset.sum_congr rfl fun s _ => (Finset.sum_mul _ _ _).symm
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ hB1]
        nlinarith

/-! ### The induction step and the main theorem

The induction step is the one part of this chapter that is **not** formalized:
`UD_succ` below is stated but proved by `sorry`.  The intended proof is the
one of the blueprint (`thm:UDstep`):

* split `[M, N)` into blocks of length `δ^ρ` using `enum_block'` and
  `sumDigits_enum_block'`, so that on a block the pair
  `(κ(δ^ρ m + j), s_b(κ(δ^ρ m + j)))` equals
  `(b^ρ κ(m) + κ(j), s_b(κ(m)) + s_b(κ(j)))`;
* apply Cauchy--Schwarz in the block index, which replaces `p` by the
  difference polynomials `R_{j,j'}`, the derivative of `p` in the integer
  direction `w = (κ(j) - κ(j'), s_b(κ(j)) - s_b(κ(j')))` plus lower order
  terms;
* by `badDirections`, `R_{j,j'}` has irrational degree `l - 1`, so the
  inductive hypothesis applies, unless `(j, j')` is *bad*, meaning
  `c₁ κ(j) + c₂ s_b(κ(j))` agrees for `j` and `j'`;
* the proportion of bad pairs tends to `0` as `ρ → ∞` in each of the three
  cases `c₂ = 0`, `c₁ ≠ 0 ≠ c₂` and `c₁ = 0`; the last uses
  `abs_Lhat_eq_one_iff` together with dominated convergence for
  `∫₀¹ |L̂(θ)|^{2ρ} dθ → 0`.
-/

/-- Blueprint: `thm:UDstep`.  If the averaging conclusion holds for all
polynomials of irrational degree at most `l`, it holds for all polynomials of
irrational degree at most `l + 1`.

**Not formalized**: the proof below is `sorry`. -/
theorem UD_succ (h : Standing b D) {l : ℕ} (hl : 1 ≤ l)
    (ih : ∀ r : MvPolynomial (Fin 2) ℝ, IrrDegLE r l → IsIrrationalPoly r →
      UniformAvg (cantorSeq b D) r)
    {p : MvPolynomial (Fin 2) ℝ} (hp1 : IrrDegLE p (l + 1))
    (hp : IsIrrationalPoly p) :
    UniformAvg (cantorSeq b D) p := by
  sorry

/-- The averaging conclusion for every polynomial of irrational degree at
most `l + 1`, by induction on `l`.

Depends on the `sorry` in `UD_succ`. -/
theorem UD_le (h : Standing b D) :
    ∀ l : ℕ, ∀ p : MvPolynomial (Fin 2) ℝ, IrrDegLE p (l + 1) → IsIrrationalPoly p →
      UniformAvg (cantorSeq b D) p := by
  intro l
  induction l with
  | zero => exact fun p hp1 hp => UD_one h hp1 hp
  | succ k ih => exact fun p hp1 hp => UD_succ h (by omega) ih hp1 hp

/-- Blueprint: `thm:polyUniform`, Theorem 4.3 of the paper.  The sequence
`n ↦ (κ(n), s_b(κ(n)))` is polynomially uniformly distributed.

Depends on the `sorry` in `UD_succ`. -/
theorem isPUDU (h : Standing b D) : IsPUDU (cantorSeq b D) := fun p hp =>
  UD_le h p.totalDegree p ((irrDegLE_totalDegree p).mono (Nat.le_succ _)) hp

end IntegerCantorSet
