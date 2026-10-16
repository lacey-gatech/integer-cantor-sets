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

/-! ### Cauchy--Schwarz and the differencing identity -/

theorem conj_expc (x : ℝ) : (starRingEnd ℂ) (expc x) = expc (-x) := by
  rw [expc, expc, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  try ring

theorem le_of_sq_le_sq {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ^ 2 ≤ y ^ 2) : x ≤ y := by
  by_contra hcon
  push Not at hcon
  nlinarith

theorem norm_ofReal_of_nonneg {x : ℝ} (hx : 0 ≤ x) : ‖((x : ℝ) : ℂ)‖ = x := by
  simp [abs_of_nonneg hx]

/-- Expanding `|∑ e(tⱼ)|²` as a double sum of differences. -/
theorem normSq_sum_expc (K : ℕ) (t : ℕ → ℝ) :
    ((‖∑ j ∈ range K, expc (t j)‖ ^ 2 : ℝ) : ℂ)
      = ∑ j ∈ range K, ∑ j' ∈ range K, expc (t j - t j') := by
  have hsq : ((‖∑ j ∈ range K, expc (t j)‖ ^ 2 : ℝ) : ℂ)
      = (∑ j ∈ range K, expc (t j)) * (starRingEnd ℂ) (∑ j ∈ range K, expc (t j)) := by
    rw [Complex.mul_conj, Complex.sq_norm]
  rw [hsq, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [conj_expc, ← expc_add]
  congr 1
  try ring

/-- Cauchy--Schwarz: `‖∑ w‖² ≤ |S| ∑ ‖w‖²`. -/
theorem norm_sum_sq_le_card_mul (S : Finset ℕ) (w : ℕ → ℂ) :
    ‖∑ m ∈ S, w m‖ ^ 2 ≤ (S.card : ℝ) * ∑ m ∈ S, ‖w m‖ ^ 2 := by
  have h1 : ‖∑ m ∈ S, w m‖ ≤ ∑ m ∈ S, ‖w m‖ := norm_sum_le _ _
  have h2 : (∑ m ∈ S, ‖w m‖) ^ 2 ≤ (S.card : ℝ) * ∑ m ∈ S, ‖w m‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  nlinarith [norm_nonneg (∑ m ∈ S, w m), Finset.sum_nonneg (fun m (_ : m ∈ S) => norm_nonneg (w m))]

/-! ### Splitting a window into complete blocks -/

/-- The window `[M, N)` decomposes into the complete blocks of length `Λ` it
contains, up to an error of at most `2Λ` unimodular terms. -/
theorem window_block_split {Λ : ℕ} (hΛ : 0 < Λ) (f : ℕ → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (M N : ℕ) :
    ‖(∑ n ∈ Ico M N, f n)
        - ∑ m ∈ Ico ((M + Λ - 1) / Λ) (N / Λ), ∑ j ∈ range Λ, f (Λ * m + j)‖
      ≤ 2 * (Λ : ℝ) := by
  obtain ⟨hA, hB⟩ := ceil_div_bounds (q := Λ) (M := M) hΛ
  obtain ⟨hC, hDD⟩ := floor_div_bounds (q := Λ) (N := N) hΛ
  obtain ⟨Mi, hMi⟩ : ∃ k, (M + Λ - 1) / Λ = k := ⟨_, rfl⟩
  obtain ⟨Ni, hNi⟩ : ∃ k, N / Λ = k := ⟨_, rfl⟩
  rw [hMi] at hA hB ⊢
  rw [hNi] at hC hDD ⊢
  have hinc : ∀ x y : ℕ, y - x ≤ Λ → ‖∑ n ∈ Ico x y, f n‖ ≤ (Λ : ℝ) := by
    intro x y hxy
    calc ‖∑ n ∈ Ico x y, f n‖ ≤ ∑ n ∈ Ico x y, ‖f n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Ico x y, (1 : ℝ) := Finset.sum_le_sum fun n _ => hf n
      _ = ((y - x : ℕ) : ℝ) := by simp
      _ ≤ (Λ : ℝ) := by exact_mod_cast hxy
  rcases le_or_gt Mi Ni with hle | hgt
  · have h1 : Λ * Mi ≤ Λ * Ni := Nat.mul_le_mul_left Λ hle
    have hmid : ∑ n ∈ Ico (Λ * Mi) (Λ * Ni), f n
        = ∑ m ∈ Ico Mi Ni, ∑ j ∈ range Λ, f (Λ * m + j) := sum_Ico_mul Λ _ hle
    have e2 : (∑ n ∈ Ico (Λ * Mi) (Λ * Ni), f n) + (∑ n ∈ Ico (Λ * Ni) N, f n)
        = ∑ n ∈ Ico (Λ * Mi) N, f n := Finset.sum_Ico_consecutive _ h1 hC
    have e1 : (∑ n ∈ Ico M (Λ * Mi), f n) + (∑ n ∈ Ico (Λ * Mi) N, f n)
        = ∑ n ∈ Ico M N, f n := Finset.sum_Ico_consecutive _ hA (le_trans h1 hC)
    have hdiff : (∑ n ∈ Ico M N, f n) - ∑ m ∈ Ico Mi Ni, ∑ j ∈ range Λ, f (Λ * m + j)
        = (∑ n ∈ Ico M (Λ * Mi), f n) + (∑ n ∈ Ico (Λ * Ni) N, f n) := by
      rw [← e1, ← e2, ← hmid]; ring
    rw [hdiff]
    calc ‖(∑ n ∈ Ico M (Λ * Mi), f n) + (∑ n ∈ Ico (Λ * Ni) N, f n)‖
        ≤ ‖∑ n ∈ Ico M (Λ * Mi), f n‖ + ‖∑ n ∈ Ico (Λ * Ni) N, f n‖ := norm_add_le _ _
      _ ≤ (Λ : ℝ) + (Λ : ℝ) := add_le_add (hinc _ _ (by omega)) (hinc _ _ (by omega))
      _ = 2 * (Λ : ℝ) := by ring
  · have hempty : Ico Mi Ni = (∅ : Finset ℕ) := Finset.Ico_eq_empty (by omega)
    have hstep : Λ * Ni + Λ ≤ Λ * Mi := by
      have hm := Nat.mul_le_mul_left Λ (show Ni + 1 ≤ Mi by omega)
      calc Λ * Ni + Λ = Λ * (Ni + 1) := by ring
        _ ≤ Λ * Mi := hm
    have hNM : N - M ≤ Λ := by
      obtain ⟨X, hX⟩ : ∃ X, Λ * Mi = X := ⟨_, rfl⟩
      obtain ⟨Y, hY⟩ : ∃ Y, Λ * Ni = Y := ⟨_, rfl⟩
      rw [hX] at hB hstep
      rw [hY] at hC hDD hstep
      omega
    rw [hempty]
    simp only [Finset.sum_empty, sub_zero]
    calc ‖∑ n ∈ Ico M N, f n‖ ≤ (Λ : ℝ) := hinc _ _ hNM
      _ ≤ 2 * (Λ : ℝ) := by
          have h0 : (0:ℝ) ≤ (Λ:ℝ) := by positivity
          linarith

/-- The number of complete blocks of length `Λ` in `[M, N)`. -/
theorem block_range_bounds {Λ : ℕ} (hΛ : 0 < Λ) (M N : ℕ) :
    Λ * (N / Λ) ≤ N ∧ M ≤ Λ * ((M + Λ - 1) / Λ)
      ∧ Λ * (N / Λ - (M + Λ - 1) / Λ) ≤ N - M := by
  obtain ⟨hA, _⟩ := ceil_div_bounds (q := Λ) (M := M) hΛ
  obtain ⟨hC, _⟩ := floor_div_bounds (q := Λ) (N := N) hΛ
  exact ⟨hC, hA, block_count_le hΛ⟩

/-! ### Rational reals -/

/-- `x` is the cast of a rational; the negation of `Irrational`. -/
def IsRat (x : ℝ) : Prop := ∃ r : ℚ, x = (r : ℝ)

theorem isRat_iff {x : ℝ} : IsRat x ↔ ¬ Irrational x :=
  ⟨fun ⟨r, hr⟩ => hr ▸ Rat.not_irrational r, fun h => exists_rat_of_not_irrational h⟩

theorem isRat_zero : IsRat 0 := ⟨0, by norm_num⟩

theorem isRat_intCast (z : ℤ) : IsRat ((z : ℤ) : ℝ) := ⟨(z : ℚ), by push_cast; ring⟩

theorem isRat_natCast (n : ℕ) : IsRat ((n : ℕ) : ℝ) := ⟨(n : ℚ), by push_cast; ring⟩

theorem IsRat.add {x y : ℝ} (hx : IsRat x) (hy : IsRat y) : IsRat (x + y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨c, rfl⟩ := hy; exact ⟨a + c, by push_cast; ring⟩

theorem IsRat.sub {x y : ℝ} (hx : IsRat x) (hy : IsRat y) : IsRat (x - y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨c, rfl⟩ := hy; exact ⟨a - c, by push_cast; ring⟩

theorem IsRat.mul {x y : ℝ} (hx : IsRat x) (hy : IsRat y) : IsRat (x * y) := by
  obtain ⟨a, rfl⟩ := hx; obtain ⟨c, rfl⟩ := hy; exact ⟨a * c, by push_cast; ring⟩

theorem IsRat.pow {x : ℝ} (hx : IsRat x) (n : ℕ) : IsRat (x ^ n) := by
  obtain ⟨a, rfl⟩ := hx; exact ⟨a ^ n, by push_cast; ring⟩

theorem IsRat.sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, IsRat (f i)) :
    IsRat (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isRat_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem irrational_of_isRat_sub {x y : ℝ} (hx : Irrational x) (h : IsRat (x - y)) :
    Irrational y := by
  obtain ⟨r, hr⟩ := h
  have : y = x - (r : ℝ) := by linarith [hr]
  rw [this]
  exact Irrational.sub_ratCast r hx

/-! ### Affine substitution -/

/-- `substAffine A u v p` is the polynomial `p(A·X + u, Y + v)`. -/
noncomputable def substAffine (A u v : ℝ) (p : MvPolynomial (Fin 2) ℝ) :
    MvPolynomial (Fin 2) ℝ :=
  bind₁ ![C A * X 0 + C u, X 1 + C v] p

theorem eval_substAffine (A u v : ℝ) (p : MvPolynomial (Fin 2) ℝ) (x y : ℝ) :
    eval ![x, y] (substAffine A u v p) = eval ![A * x + u, y + v] p := by
  have h1 : ∀ (f : Fin 2 → ℝ) (q : MvPolynomial (Fin 2) ℝ), aeval f q = eval f q :=
    fun f q => DFunLike.congr_fun (coe_aeval_eq_eval f) q
  have h := MvPolynomial.aeval_bind₁ (R := ℝ) (S := ℝ) ![x, y]
    ![C A * X 0 + C u, X 1 + C v] p
  simp only [h1] at h
  have h2 : (fun i => eval ![x, y] (![C A * X 0 + C u, X 1 + C v] i))
      = ![A * x + u, y + v] := by
    funext i
    fin_cases i <;> simp
  rw [substAffine, h, h2]

theorem substAffine_add (A u v : ℝ) (p q : MvPolynomial (Fin 2) ℝ) :
    substAffine A u v (p + q) = substAffine A u v p + substAffine A u v q := by
  simp [substAffine]

/-- The one-variable binomial expansion, as a sum of monomials. -/
theorem C_mul_X_add_C_pow (i : Fin 2) (A u : ℝ) (n : ℕ) :
    (C A * X i + C u) ^ n
      = ∑ a ∈ range (n + 1),
          monomial (Finsupp.single i a) (((n.choose a : ℕ) : ℝ) * A ^ a * u ^ (n - a)) := by
  rw [add_pow]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hnat : (((n.choose a : ℕ)) : MvPolynomial (Fin 2) ℝ) = C (((n.choose a : ℕ)) : ℝ) := by
    simp
  rw [hnat, mul_pow, ← C_pow, ← C_pow, X_pow_eq_monomial, C_mul_monomial, mul_one]
  rw [mul_comm (monomial (Finsupp.single i a) (A ^ a)) (C (u ^ (n - a))), C_mul_monomial]
  rw [mul_comm (monomial (Finsupp.single i a) (u ^ (n - a) * A ^ a))
    (C (((n.choose a : ℕ)) : ℝ)), C_mul_monomial]
  congr 1
  ring

theorem substAffine_monomial (A u v : ℝ) (n n' : ℕ) (c : ℝ) :
    substAffine A u v (monomial (mono2 n n') c)
      = C c * ((C A * X 0 + C u) ^ n * (X 1 + C v) ^ n') := by
  classical
  rw [substAffine, bind₁_monomial]
  congr 1
  have hsub : (mono2 n n').support ⊆ (Finset.univ : Finset (Fin 2)) := Finset.subset_univ _
  rw [Finset.prod_subset hsub (by
    intro x _ hx
    rw [Finsupp.notMem_support_iff.1 hx]
    simp)]
  rw [Fin.prod_univ_two]
  simp

/-- The coefficients of an affine substitution of a single monomial. -/
theorem coeff_substAffine_monomial (A u v : ℝ) (n n' : ℕ) (c : ℝ) (m : Fin 2 →₀ ℕ) :
    (substAffine A u v (monomial (mono2 n n') c)).coeff m
      = c * (((n.choose (m 0) : ℕ) : ℝ) * ((n'.choose (m 1) : ℕ) : ℝ)
          * A ^ (m 0) * u ^ (n - m 0) * v ^ (n' - m 1)) := by
  classical
  have hX1 : (X (1 : Fin 2) + C v : MvPolynomial (Fin 2) ℝ) = C 1 * X 1 + C v := by simp
  rw [substAffine_monomial, hX1, C_mul_X_add_C_pow, C_mul_X_add_C_pow]
  have hexp : C c * ((∑ a ∈ range (n + 1),
          monomial (Finsupp.single (0 : Fin 2) a)
            (((n.choose a : ℕ) : ℝ) * A ^ a * u ^ (n - a)))
        * ∑ e ∈ range (n' + 1),
          monomial (Finsupp.single (1 : Fin 2) e)
            (((n'.choose e : ℕ) : ℝ) * (1 : ℝ) ^ e * v ^ (n' - e)))
      = ∑ a ∈ range (n + 1), ∑ e ∈ range (n' + 1),
          monomial (mono2 a e)
            (c * ((((n.choose a : ℕ) : ℝ) * A ^ a * u ^ (n - a))
              * (((n'.choose e : ℕ) : ℝ) * (1 : ℝ) ^ e * v ^ (n' - e)))) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [monomial_mul, C_mul_monomial]
    rfl
  rw [hexp, coeff_sum]
  have h1 : ∀ a ∈ range (n + 1),
      (∑ e ∈ range (n' + 1), monomial (mono2 a e)
          (c * ((((n.choose a : ℕ) : ℝ) * A ^ a * u ^ (n - a))
            * (((n'.choose e : ℕ) : ℝ) * (1 : ℝ) ^ e * v ^ (n' - e))))).coeff m
        = ∑ e ∈ range (n' + 1), (if mono2 a e = m then
            c * ((((n.choose a : ℕ) : ℝ) * A ^ a * u ^ (n - a))
              * (((n'.choose e : ℕ) : ℝ) * (1 : ℝ) ^ e * v ^ (n' - e))) else 0) := by
    intro a _
    rw [coeff_sum]
    exact Finset.sum_congr rfl fun e _ => coeff_monomial _ _ _
  rw [Finset.sum_congr rfl h1]
  have hmono : ∀ a e : ℕ, mono2 a e = m ↔ (a = m 0 ∧ e = m 1) := by
    intro a e
    constructor
    · intro hh
      exact ⟨by rw [← hh]; simp, by rw [← hh]; simp⟩
    · rintro ⟨rfl, rfl⟩
      exact mono2_self m
  by_cases hm0 : m 0 ≤ n
  · by_cases hm1 : m 1 ≤ n'
    · rw [Finset.sum_eq_single_of_mem (m 0) (Finset.mem_range.2 (by omega))]
      · rw [Finset.sum_eq_single_of_mem (m 1) (Finset.mem_range.2 (by omega))]
        · rw [if_pos ((hmono _ _).2 ⟨rfl, rfl⟩)]
          ring
        · intro e _ hene
          rw [if_neg (fun hc => hene ((hmono _ _).1 hc).2)]
      · intro a _ hane
        refine Finset.sum_eq_zero fun e _ => ?_
        rw [if_neg (fun hc => hane ((hmono _ _).1 hc).1)]
    · have hz : n'.choose (m 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun e he => if_neg (fun hc => by
        have h2 := ((hmono _ _).1 hc).2
        have h3 := Finset.mem_range.1 he
        omega))), hz]
      push_cast
      ring
  · have hz : n.choose (m 0) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [Finset.sum_eq_zero (fun a ha => Finset.sum_eq_zero (fun e _ => if_neg (fun hc => by
      have h2 := ((hmono _ _).1 hc).1
      have h3 := Finset.mem_range.1 ha
      omega))), hz]
    push_cast
    ring

theorem coeff_substAffine_monomial' (A u v : ℝ) (m' : Fin 2 →₀ ℕ) (c : ℝ) (m : Fin 2 →₀ ℕ) :
    (substAffine A u v (monomial m' c)).coeff m
      = c * ((((m' 0).choose (m 0) : ℕ) : ℝ) * (((m' 1).choose (m 1) : ℕ) : ℝ)
          * A ^ (m 0) * u ^ (m' 0 - m 0) * v ^ (m' 1 - m 1)) := by
  have h := coeff_substAffine_monomial A u v (m' 0) (m' 1) c m
  rwa [mono2_self] at h

/-- The weight with which `p.coeff m'` enters the `m`-th coefficient of
`substAffine A u v p`. -/
noncomputable def substWeight (A u v : ℝ) (m m' : Fin 2 →₀ ℕ) : ℝ :=
  (((m' 0).choose (m 0) : ℕ) : ℝ) * (((m' 1).choose (m 1) : ℕ) : ℝ)
    * A ^ (m 0) * u ^ (m' 0 - m 0) * v ^ (m' 1 - m 1)

/-- The coefficients of an affine substitution, over any finset containing the
support. -/
theorem coeff_substAffine (A u v : ℝ) (p : MvPolynomial (Fin 2) ℝ) (m : Fin 2 →₀ ℕ)
    {T : Finset (Fin 2 →₀ ℕ)} (hT : p.support ⊆ T) :
    (substAffine A u v p).coeff m = ∑ m' ∈ T, p.coeff m' * substWeight A u v m m' := by
  classical
  have hp : p = ∑ m' ∈ T, monomial m' (p.coeff m') := by
    conv_lhs => rw [MvPolynomial.as_sum p]
    refine Finset.sum_subset hT ?_
    intro x _ hx
    rw [MvPolynomial.notMem_support_iff.1 hx, map_zero]
  conv_lhs => rw [hp]
  rw [substAffine, map_sum, coeff_sum]
  exact Finset.sum_congr rfl fun m' _ => coeff_substAffine_monomial' A u v m' _ m

theorem substWeight_eq_zero (A u v : ℝ) {m m' : Fin 2 →₀ ℕ}
    (h : ¬ (m 0 ≤ m' 0 ∧ m 1 ≤ m' 1)) : substWeight A u v m m' = 0 := by
  rw [substWeight]
  rcases Nat.lt_or_ge (m' 0) (m 0) with h0 | h0
  · rw [Nat.choose_eq_zero_of_lt h0]
    push_cast
    ring
  · have h1 : m' 1 < m 1 := by omega
    rw [Nat.choose_eq_zero_of_lt h1]
    push_cast
    ring

theorem substWeight_self (A u v : ℝ) (m : Fin 2 →₀ ℕ) :
    substWeight A u v m m = A ^ (m 0) := by
  simp [substWeight]

theorem substWeight_add_zero (A u v : ℝ) (m : Fin 2 →₀ ℕ) :
    substWeight A u v m (m + Finsupp.single 0 1) = ((m 0 : ℝ) + 1) * A ^ (m 0) * u := by
  have e0 : ((m + Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ)) 0 = m 0 + 1 := by simp
  have e1 : ((m + Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ)) 1 = m 1 := by
    simp [Finsupp.single_apply]
  rw [substWeight, e0, e1, Nat.choose_succ_self_right, Nat.choose_self]
  push_cast
  simp

theorem substWeight_add_one (A u v : ℝ) (m : Fin 2 →₀ ℕ) :
    substWeight A u v m (m + Finsupp.single 1 1) = ((m 1 : ℝ) + 1) * A ^ (m 0) * v := by
  have e0 : ((m + Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ)) 0 = m 0 := by
    simp [Finsupp.single_apply]
  have e1 : ((m + Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ)) 1 = m 1 + 1 := by simp
  rw [substWeight, e0, e1, Nat.choose_succ_self_right, Nat.choose_self]
  push_cast
  simp

theorem isRat_substWeight {A u v : ℝ} (hA : IsRat A) (hu : IsRat u) (hv : IsRat v)
    (m m' : Fin 2 →₀ ℕ) : IsRat (substWeight A u v m m') := by
  rw [substWeight]
  exact (((isRat_natCast _).mul (isRat_natCast _)).mul (hA.pow _) |>.mul (hu.pow _)).mul (hv.pow _)

@[simp] theorem add_e0_apply_zero (m : Fin 2 →₀ ℕ) :
    ((m + Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ)) 0 = m 0 + 1 := by simp

@[simp] theorem add_e0_apply_one (m : Fin 2 →₀ ℕ) :
    ((m + Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ)) 1 = m 1 := by
  simp [Finsupp.single_apply]

@[simp] theorem add_e1_apply_zero (m : Fin 2 →₀ ℕ) :
    ((m + Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ)) 0 = m 0 := by
  simp [Finsupp.single_apply]

@[simp] theorem add_e1_apply_one (m : Fin 2 →₀ ℕ) :
    ((m + Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ)) 1 = m 1 + 1 := by simp

theorem eq_of_le_of_deg_le {m m' : Fin 2 →₀ ℕ} (h0 : m 0 ≤ m' 0) (h1 : m 1 ≤ m' 1)
    (hd : m' 0 + m' 1 ≤ m 0 + m 1 + 1) :
    m' = m ∨ m' = m + Finsupp.single 0 1 ∨ m' = m + Finsupp.single 1 1 := by
  rcases Nat.eq_or_lt_of_le h0 with e0 | e0
  · rcases Nat.eq_or_lt_of_le h1 with e1 | e1
    · exact Or.inl (finsupp_fin2_ext e0.symm e1.symm)
    · exact Or.inr (Or.inr (finsupp_fin2_ext (by simp; omega) (by simp; omega)))
  · exact Or.inr (Or.inl (finsupp_fin2_ext (by simp; omega) (by simp; omega)))

/-- The difference polynomial `p(A·+u, ·+v) - p(A·+u', ·+v')`. -/
noncomputable def diffPoly (A u v u' v' : ℤ) (p : MvPolynomial (Fin 2) ℝ) :
    MvPolynomial (Fin 2) ℝ :=
  substAffine (A : ℝ) (u : ℝ) (v : ℝ) p - substAffine (A : ℝ) (u' : ℝ) (v' : ℝ) p

theorem coeff_diffPoly (A u v u' v' : ℤ) (p : MvPolynomial (Fin 2) ℝ) (m : Fin 2 →₀ ℕ)
    {T : Finset (Fin 2 →₀ ℕ)} (hT : p.support ⊆ T) :
    (diffPoly A u v u' v' p).coeff m
      = ∑ m' ∈ T, p.coeff m'
          * (substWeight (A : ℝ) (u : ℝ) (v : ℝ) m m'
            - substWeight (A : ℝ) (u' : ℝ) (v' : ℝ) m m') := by
  have hs : ∀ f g : MvPolynomial (Fin 2) ℝ, (f - g).coeff m = f.coeff m - g.coeff m :=
    fun _ _ => rfl
  rw [diffPoly, hs, coeff_substAffine _ _ _ _ _ hT, coeff_substAffine _ _ _ _ _ hT,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun m' _ => by ring

theorem isRat_weight_diff (A u v u' v' : ℤ) (m m' : Fin 2 →₀ ℕ) :
    IsRat (substWeight (A : ℝ) (u : ℝ) (v : ℝ) m m'
      - substWeight (A : ℝ) (u' : ℝ) (v' : ℝ) m m') :=
  (isRat_substWeight (isRat_intCast A) (isRat_intCast u) (isRat_intCast v) m m').sub
    (isRat_substWeight (isRat_intCast A) (isRat_intCast u') (isRat_intCast v') m m')

/-- Away from `m`, `m + e₀` and `m + e₁`, every term of the coefficient sum is
rational. -/
theorem isRat_diffPoly_term {p : MvPolynomial (Fin 2) ℝ} {l : ℕ}
    (hp : IrrDegLE p (l + 1)) (A u v u' v' : ℤ) {m m' : Fin 2 →₀ ℕ}
    (hdeg : l ≤ m 0 + m 1) (hm' : m' ≠ m)
    (h0 : m' ≠ m + Finsupp.single 0 1) (h1 : m' ≠ m + Finsupp.single 1 1) :
    IsRat (p.coeff m' * (substWeight (A : ℝ) (u : ℝ) (v : ℝ) m m'
      - substWeight (A : ℝ) (u' : ℝ) (v' : ℝ) m m')) := by
  by_cases hle : m 0 ≤ m' 0 ∧ m 1 ≤ m' 1
  · by_cases hbig : l + 1 < m' 0 + m' 1
    · exact (isRat_iff.2 (hp m' hbig)).mul (isRat_weight_diff A u v u' v' m m')
    · exfalso
      have hd : m' 0 + m' 1 ≤ m 0 + m 1 + 1 := by omega
      rcases eq_of_le_of_deg_le hle.1 hle.2 hd with he | he | he
      · exact hm' he
      · exact h0 he
      · exact h1 he
  · rw [substWeight_eq_zero _ _ _ hle, substWeight_eq_zero _ _ _ hle]
    simpa using isRat_zero

/-- Blueprint: the degree drop.  `diffPoly` has irrational degree at most `l`
when `p` has irrational degree at most `l + 1`. -/
theorem irrDegLE_diffPoly {p : MvPolynomial (Fin 2) ℝ} {l : ℕ}
    (hp : IrrDegLE p (l + 1)) (A u v u' v' : ℤ) :
    IrrDegLE (diffPoly A u v u' v' p) l := by
  classical
  intro m hm
  refine isRat_iff.1 ?_
  rw [coeff_diffPoly A u v u' v' p m (Finset.Subset.refl _)]
  refine IsRat.sum _ _ fun m' _ => ?_
  by_cases he : m' = m
  · subst he
    rw [substWeight_self, substWeight_self]
    simpa using isRat_zero
  · by_cases he0 : m' = m + Finsupp.single 0 1
    · subst he0
      exact (isRat_iff.2 (hp _ (by simp; omega))).mul (isRat_weight_diff A u v u' v' m _)
    · by_cases he1 : m' = m + Finsupp.single 1 1
      · subst he1
        exact (isRat_iff.2 (hp _ (by simp; omega))).mul (isRat_weight_diff A u v u' v' m _)
      · exact isRat_diffPoly_term hp A u v u' v' (by omega) he he0 he1

/-- Blueprint: the degree-`l` coefficients of the difference polynomial are
those of `A^{m₀} ∂_w p`, up to rationals. -/
theorem coeff_diffPoly_sub_isRat {p : MvPolynomial (Fin 2) ℝ} {l : ℕ}
    (hp : IrrDegLE p (l + 1)) (A u v u' v' : ℤ) {m : Fin 2 →₀ ℕ} (hm : m 0 + m 1 = l) :
    IsRat ((diffPoly A u v u' v' p).coeff m
      - (A : ℝ) ^ (m 0) * (dirDeriv (u - u', v - v') p).coeff m) := by
  classical
  have hne0 : m + Finsupp.single (0 : Fin 2) 1 ≠ m := by
    intro hc
    have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) hc
    simp at this
  have hne1 : m + Finsupp.single (1 : Fin 2) 1 ≠ m := by
    intro hc
    have := congrArg (fun f : Fin 2 →₀ ℕ => f 1) hc
    simp at this
  have hne01 : m + Finsupp.single (0 : Fin 2) 1 ≠ m + Finsupp.single (1 : Fin 2) 1 := by
    intro hc
    have := congrArg (fun f : Fin 2 →₀ ℕ => f 0) hc
    simp at this
  set S : Finset (Fin 2 →₀ ℕ) :=
    {m, m + Finsupp.single 0 1, m + Finsupp.single 1 1} with hSdef
  set T : Finset (Fin 2 →₀ ℕ) := S ∪ p.support with hTdef
  have hsub : p.support ⊆ T := Finset.subset_union_right
  have hST : S ⊆ T := Finset.subset_union_left
  have hmemS : ∀ m' : Fin 2 →₀ ℕ, m' ∈ S ↔
      (m' = m ∨ m' = m + Finsupp.single 0 1 ∨ m' = m + Finsupp.single 1 1) := by
    intro m'
    simp [hSdef]
  rw [coeff_diffPoly A u v u' v' p m hsub, ← Finset.sum_sdiff hST]
  have hrest : IsRat (∑ m' ∈ T \ S, p.coeff m'
      * (substWeight (A : ℝ) (u : ℝ) (v : ℝ) m m'
        - substWeight (A : ℝ) (u' : ℝ) (v' : ℝ) m m')) := by
    refine IsRat.sum _ _ fun m' hm' => ?_
    have hnot := (Finset.mem_sdiff.1 hm').2
    rw [hmemS] at hnot
    push Not at hnot
    exact isRat_diffPoly_term hp A u v u' v' (by omega) hnot.1 hnot.2.1 hnot.2.2
  have hSsum : (∑ m' ∈ S, p.coeff m'
      * (substWeight (A : ℝ) (u : ℝ) (v : ℝ) m m'
        - substWeight (A : ℝ) (u' : ℝ) (v' : ℝ) m m'))
      = (A : ℝ) ^ (m 0) * (dirDeriv (u - u', v - v') p).coeff m := by
    rw [hSdef, Finset.sum_insert (by simp [hne0.symm, hne1.symm]),
      Finset.sum_insert (by simp [hne01]), Finset.sum_singleton]
    rw [substWeight_self, substWeight_self, substWeight_add_zero, substWeight_add_zero,
      substWeight_add_one, substWeight_add_one, coeff_dirDeriv]
    push_cast
    ring
  rw [hSsum]
  simpa using hrest

/-! ### Counting the bad pairs -/

theorem sumDigits_le_of_lt_pow (hb : 1 < b) (ρ : ℕ) :
    ∀ n : ℕ, n < b ^ ρ → sumDigits b n ≤ (b - 1) * ρ := by
  induction ρ with
  | zero =>
    intro n hn
    simp only [pow_zero, Nat.lt_one_iff] at hn
    simp [hn, sumDigits]
  | succ k ih =>
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [sumDigits]
    · have hd : Nat.digits b n = n % b :: Nat.digits b (n / b) := Nat.digits_def' hb hpos
      have hs : sumDigits b n = n % b + sumDigits b (n / b) := by
        rw [sumDigits, hd, List.sum_cons]
        rfl
      have hdiv : n / b < b ^ k := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        calc n < b ^ (k + 1) := hn
          _ = b ^ k * b := by ring
      have hih := ih (n / b) hdiv
      have hmod : n % b ≤ b - 1 := by
        have := Nat.mod_lt n (show 0 < b by omega)
        omega
      have hexp : (b - 1) * (k + 1) = (b - 1) + (b - 1) * k := by ring
      omega

theorem card_filter_product {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (t : Finset β) (P : α → β → Prop) [∀ a c, Decidable (P a c)] :
    ((s ×ˢ t).filter (fun z => P z.1 z.2)).card = ∑ a ∈ s, (t.filter (P a)).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_product]

/-- A linear function of `ρ` is eventually dominated by `ε δ^ρ` when `δ ≥ 2`. -/
theorem exists_linear_le_pow {d : ℕ} (hd : 2 ≤ d) (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℕ, 1 ≤ ρ ∧ ((K : ℝ) * ρ + 1) ≤ ε * (d : ℝ) ^ ρ := by
  have hd1 : (1 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hr : (0 : ℝ) ≤ (d : ℝ)⁻¹ := by positivity
  have hr1 : (d : ℝ)⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    right; exact hd1
  have h1 : Tendsto (fun ρ : ℕ => (ρ : ℝ) * ((d : ℝ)⁻¹) ^ ρ) atTop (nhds 0) :=
    tendsto_self_mul_const_pow_of_lt_one hr hr1
  have h2 : Tendsto (fun ρ : ℕ => ((d : ℝ)⁻¹) ^ ρ) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1
  have h3 : Tendsto (fun ρ : ℕ => ((K : ℝ) * ρ + 1) / (d : ℝ) ^ ρ) atTop (nhds 0) := by
    have := (h1.const_mul (K : ℝ)).add h2
    rw [mul_zero, add_zero] at this
    refine this.congr fun ρ => ?_
    rw [div_eq_mul_inv, ← inv_pow]
    ring
  have h4 : ∀ᶠ ρ : ℕ in atTop, ((K : ℝ) * ρ + 1) / (d : ℝ) ^ ρ < ε :=
    Filter.Tendsto.eventually_lt_const hε h3
  obtain ⟨ρ, hρ1, hρ2⟩ := ((eventually_ge_atTop 1).and h4).exists
  refine ⟨ρ, hρ1, ?_⟩
  have hpow : (0 : ℝ) < (d : ℝ) ^ ρ := by positivity
  rw [div_lt_iff₀ hpow] at hρ2
  linarith

/-- The pairs `(j, j')` below `δ^ρ` on which the linear form
`c₁ κ + c₂ s_b∘κ` takes the same value. -/
def badPairs (b : ℕ) (D : Finset ℕ) (c : ℤ × ℤ) (ρ : ℕ) : Finset (ℕ × ℕ) :=
  (range (D.card ^ ρ) ×ˢ range (D.card ^ ρ)).filter
    (fun z : ℕ × ℕ => c.1 * (enum b D z.1 : ℤ) + c.2 * (sumDigits b (enum b D z.1) : ℤ)
      = c.1 * (enum b D z.2 : ℤ) + c.2 * (sumDigits b (enum b D z.2) : ℤ))

theorem mem_badPairs {c : ℤ × ℤ} {ρ : ℕ} {z : ℕ × ℕ} :
    z ∈ badPairs b D c ρ ↔ (z.1 < D.card ^ ρ ∧ z.2 < D.card ^ ρ) ∧
      c.1 * (enum b D z.1 : ℤ) + c.2 * (sumDigits b (enum b D z.1) : ℤ)
        = c.1 * (enum b D z.2 : ℤ) + c.2 * (sumDigits b (enum b D z.2) : ℤ) := by
  simp [badPairs, Finset.mem_filter, Finset.mem_product]

/-- When `c₁ ≠ 0`, a bad partner is determined by its digit sum, of which
there are at most `(b-1)ρ + 1` values. -/
theorem card_badPairs_le_of_fst_ne (h : Standing b D) {c : ℤ × ℤ} (hc1 : c.1 ≠ 0) (ρ : ℕ) :
    (badPairs b D c ρ).card ≤ D.card ^ ρ * ((b - 1) * ρ + 1) := by
  classical
  rw [badPairs, card_filter_product _ _ (fun j j' : ℕ =>
    c.1 * (enum b D j : ℤ) + c.2 * (sumDigits b (enum b D j) : ℤ)
      = c.1 * (enum b D j' : ℤ) + c.2 * (sumDigits b (enum b D j') : ℤ))]
  have hb : 1 < b := by have := h.three_le_base; omega
  have hbound : ∀ j ∈ range (D.card ^ ρ),
      ((range (D.card ^ ρ)).filter (fun j' : ℕ =>
        c.1 * (enum b D j : ℤ) + c.2 * (sumDigits b (enum b D j) : ℤ)
          = c.1 * (enum b D j' : ℤ) + c.2 * (sumDigits b (enum b D j') : ℤ))).card
        ≤ (b - 1) * ρ + 1 := by
    intro j _
    have := Finset.card_le_card_of_injOn (f := fun j' : ℕ => sumDigits b (enum b D j'))
      (s := (range (D.card ^ ρ)).filter (fun j' : ℕ =>
        c.1 * (enum b D j : ℤ) + c.2 * (sumDigits b (enum b D j) : ℤ)
          = c.1 * (enum b D j' : ℤ) + c.2 * (sumDigits b (enum b D j') : ℤ)))
      (t := range ((b - 1) * ρ + 1)) ?_ ?_
    · simpa using this
    · intro j' hj'
      simp only [Finset.mem_coe, Finset.mem_range]
      have hlt : j' < D.card ^ ρ :=
        Finset.mem_range.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hj')).1
      have h1 : enum b D j' < b ^ ρ := enum_lt_pow h hlt
      have := sumDigits_le_of_lt_pow (b := b) hb ρ _ h1
      omega
    · intro x hx y hy hxy
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx hy
      have hex : (enum b D x : ℤ) = (enum b D y : ℤ) := by
        have h1 := hx.2
        have h2 := hy.2
        have h3 : (sumDigits b (enum b D x) : ℤ) = (sumDigits b (enum b D y) : ℤ) := by
          exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) hxy
        have : c.1 * (enum b D x : ℤ) = c.1 * (enum b D y : ℤ) := by
          rw [h3] at h1
          omega
        exact mul_left_cancel₀ hc1 this
      have : enum b D x = enum b D y := by exact_mod_cast hex
      exact (enum_strictMono h).injective this
  calc (∑ j ∈ range (D.card ^ ρ), ((range (D.card ^ ρ)).filter (fun j' : ℕ =>
          c.1 * (enum b D j : ℤ) + c.2 * (sumDigits b (enum b D j) : ℤ)
            = c.1 * (enum b D j' : ℤ) + c.2 * (sumDigits b (enum b D j') : ℤ))).card)
      ≤ ∑ _j ∈ range (D.card ^ ρ), ((b - 1) * ρ + 1) := Finset.sum_le_sum hbound
    _ = D.card ^ ρ * ((b - 1) * ρ + 1) := by simp [mul_comm]

/-! ### The bad pairs when the linear form involves only the digit sum -/

theorem continuous_expc : Continuous expc := by
  unfold expc
  fun_prop

theorem continuous_expc_mul (c : ℝ) : Continuous (fun θ : ℝ => expc (c * θ)) :=
  continuous_expc.comp (continuous_const.mul continuous_id)

theorem continuous_Lhat (D : Finset ℕ) : Continuous (Lhat D) := by
  unfold Lhat
  exact continuous_const.mul (continuous_finset_sum _ fun d _ => continuous_expc_mul _)

theorem integrableOn_expc_mul (c : ℝ) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => expc (c * θ)) (Set.Ioc (0:ℝ) 1) :=
  (continuous_expc_mul c).integrableOn_Ioc

/-- Orthogonality of the characters `θ ↦ e(kθ)` on `[0,1]`. -/
theorem integral_expc_intCast_mul (k : ℤ) :
    ∫ θ in Set.Ioc (0:ℝ) 1, expc ((k : ℝ) * θ) = if k = 0 then 1 else 0 := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  by_cases hk : k = 0
  · subst hk
    simp
  · rw [if_neg hk]
    have hpi : (0:ℝ) < π := Real.pi_pos
    have hkR : (k : ℝ) ≠ 0 := Int.cast_ne_zero.2 hk
    have hcne : (((2 * π * (k : ℝ) : ℝ)) : ℂ) * Complex.I ≠ 0 := by
      refine mul_ne_zero ?_ Complex.I_ne_zero
      simp only [ne_eq, Complex.ofReal_eq_zero]
      intro hc
      rcases mul_eq_zero.1 hc with hc' | hc'
      · rcases mul_eq_zero.1 hc' with hc'' | hc''
        · norm_num at hc''
        · linarith
      · exact hkR hc'
    have hcongr : ∀ θ : ℝ,
        expc ((k : ℝ) * θ) = Complex.exp (((2 * π * (k : ℝ) : ℝ) : ℂ) * Complex.I * (θ : ℂ)) := by
      intro θ
      rw [expc]
      congr 1
      push_cast
      ring
    rw [intervalIntegral.integral_congr (fun θ _ => hcongr θ), integral_exp_mul_complex hcne]
    have h1 : Complex.exp (((2 * π * (k : ℝ) : ℝ) : ℂ) * Complex.I * ((1 : ℝ) : ℂ)) = 1 := by
      have he : (((2 * π * (k : ℝ) : ℝ)) : ℂ) * Complex.I * ((1 : ℝ) : ℂ)
          = ((2 * π * ((k : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [he]
      exact expc_intCast k
    have h0 : Complex.exp (((2 * π * (k : ℝ) : ℝ) : ℂ) * Complex.I * ((0 : ℝ) : ℂ)) = 1 := by
      simp
    rw [h1, h0, sub_self, zero_div]

/-- `∑_{j < δ^ρ} e(s_b(κ(j)) θ) = δ^ρ L̂(θ)^ρ`.  Specialisation of
`sum_range_pow_eq` to `α = 0`. -/
theorem sum_expc_sumDigits_eq (h : Standing b D) (θ : ℝ) (ρ : ℕ) :
    ∑ j ∈ range (D.card ^ ρ), expc ((sumDigits b (enum b D j) : ℝ) * θ)
      = (D.card : ℂ) ^ ρ * (Lhat D θ) ^ ρ := by
  have h2 : ∀ j ∈ range (D.card ^ ρ),
      expc ((sumDigits b (enum b D j) : ℝ) * θ) = expPhi b D 0 θ j := by
    intro j _
    rw [expPhi]
    congr 1
    ring
  rw [Finset.sum_congr rfl h2, sum_range_pow_eq h 0 θ ρ]
  congr 1
  rw [Finset.prod_congr rfl (fun c _ => by
    show Lhat D ((b : ℝ) ^ c * 0 + θ) = Lhat D θ
    congr 1
    ring), Finset.prod_const, Finset.card_range]

theorem badPairs_fst_zero (h : Standing b D) {c : ℤ × ℤ} (hc1 : c.1 = 0) (hc2 : c.2 ≠ 0) (ρ : ℕ) :
    badPairs b D c ρ
      = (range (D.card ^ ρ) ×ˢ range (D.card ^ ρ)).filter
          (fun z : ℕ × ℕ => sumDigits b (enum b D z.1) = sumDigits b (enum b D z.2)) := by
  rw [badPairs]
  refine Finset.filter_congr fun z _ => ?_
  rw [hc1]
  constructor
  · intro hh
    have h2 : c.2 * (sumDigits b (enum b D z.1) : ℤ)
        = c.2 * (sumDigits b (enum b D z.2) : ℤ) := by linarith [hh]
    exact_mod_cast mul_left_cancel₀ hc2 h2
  · intro hh
    rw [hh]
    ring

theorem card_badPairs_fst_zero (h : Standing b D) {c : ℤ × ℤ} (hc1 : c.1 = 0) (hc2 : c.2 ≠ 0)
    (ρ : ℕ) :
    ((badPairs b D c ρ).card : ℝ)
      = ((D.card : ℝ) ^ ρ) ^ 2 * ∫ θ in Set.Ioc (0:ℝ) 1, ‖Lhat D θ‖ ^ (2 * ρ) := by
  classical
  have e1 : ((badPairs b D c ρ).card : ℂ)
      = ∑ j ∈ range (D.card ^ ρ), ∑ j' ∈ range (D.card ^ ρ),
          (if sumDigits b (enum b D j) = sumDigits b (enum b D j') then (1:ℂ) else 0) := by
    rw [badPairs_fst_zero h hc1 hc2, card_filter_product _ _
      (fun j j' : ℕ => sumDigits b (enum b D j) = sumDigits b (enum b D j'))]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.card_filter]
    push_cast
    rfl
  have e2 : ∀ j j' : ℕ,
      (if sumDigits b (enum b D j) = sumDigits b (enum b D j') then (1:ℂ) else 0)
        = ∫ θ in Set.Ioc (0:ℝ) 1,
            expc ((((sumDigits b (enum b D j) : ℤ) - (sumDigits b (enum b D j') : ℤ) : ℤ) : ℝ) * θ) := by
    intro j j'
    rw [integral_expc_intCast_mul]
    by_cases hh : sumDigits b (enum b D j) = sumDigits b (enum b D j')
    · rw [if_pos hh, if_pos (by omega :
        ((sumDigits b (enum b D j) : ℤ) - (sumDigits b (enum b D j') : ℤ)) = 0)]
    · rw [if_neg hh, if_neg (by omega : ¬
        (((sumDigits b (enum b D j) : ℤ) - (sumDigits b (enum b D j') : ℤ)) = 0))]
  have hintg : ∀ j j' : ℕ, MeasureTheory.IntegrableOn
      (fun θ : ℝ => expc ((((sumDigits b (enum b D j) : ℤ)
        - (sumDigits b (enum b D j') : ℤ) : ℤ) : ℝ) * θ)) (Set.Ioc (0:ℝ) 1) :=
    fun _ _ => integrableOn_expc_mul _
  have e3 : (∑ j ∈ range (D.card ^ ρ), ∑ j' ∈ range (D.card ^ ρ),
        ∫ θ in Set.Ioc (0:ℝ) 1, expc ((((sumDigits b (enum b D j) : ℤ)
          - (sumDigits b (enum b D j') : ℤ) : ℤ) : ℝ) * θ))
      = ∫ θ in Set.Ioc (0:ℝ) 1, ∑ j ∈ range (D.card ^ ρ), ∑ j' ∈ range (D.card ^ ρ),
          expc ((((sumDigits b (enum b D j) : ℤ)
            - (sumDigits b (enum b D j') : ℤ) : ℤ) : ℝ) * θ) := by
    rw [MeasureTheory.integral_finset_sum _ (fun j _ =>
      MeasureTheory.integrable_finset_sum _ (fun j' _ => hintg j j'))]
    exact Finset.sum_congr rfl fun j _ =>
      (MeasureTheory.integral_finset_sum _ (fun j' _ => hintg j j')).symm
  have e4 : ∀ θ : ℝ, (∑ j ∈ range (D.card ^ ρ), ∑ j' ∈ range (D.card ^ ρ),
        expc ((((sumDigits b (enum b D j) : ℤ)
          - (sumDigits b (enum b D j') : ℤ) : ℤ) : ℝ) * θ))
      = (((((D.card : ℝ) ^ ρ) ^ 2 * ‖Lhat D θ‖ ^ (2 * ρ)) : ℝ) : ℂ) := by
    intro θ
    have hnorm := normSq_sum_expc (D.card ^ ρ) (fun j => (sumDigits b (enum b D j) : ℝ) * θ)
    have hcongr : ∀ j j' : ℕ, expc ((((sumDigits b (enum b D j) : ℤ)
          - (sumDigits b (enum b D j') : ℤ) : ℤ) : ℝ) * θ)
        = expc ((sumDigits b (enum b D j) : ℝ) * θ - (sumDigits b (enum b D j') : ℝ) * θ) := by
      intro j j'
      congr 1
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => hcongr j j')), ← hnorm]
    congr 1
    rw [sum_expc_sumDigits_eq h θ ρ, norm_mul, norm_pow, norm_pow, Complex.norm_natCast,
      mul_pow, show 2 * ρ = ρ * 2 by ring, pow_mul]
  have hcast : (((badPairs b D c ρ).card : ℝ) : ℂ)
      = ((((D.card : ℝ) ^ ρ) ^ 2 * ∫ θ in Set.Ioc (0:ℝ) 1, ‖Lhat D θ‖ ^ (2 * ρ) : ℝ) : ℂ) := by
    push_cast
    rw [e1, Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun j' _ => e2 j j')), e3]
    simp only [e4]
    rw [integral_complex_ofReal, MeasureTheory.integral_const_mul]
    push_cast
    ring
  exact_mod_cast hcast

/-- `∫₀¹ |L̂(θ)|^{2ρ} dθ → 0`: dominated convergence, using that
`|L̂(θ)| = 1` only on a countable set. -/
theorem tendsto_integral_Lhat_pow (h : Standing b D) :
    Tendsto (fun ρ : ℕ => ∫ θ in Set.Ioc (0:ℝ) 1, ‖Lhat D θ‖ ^ (2 * ρ)) atTop (nhds 0) := by
  have hDne : D.Nonempty := ⟨0, h.zero_mem⟩
  have hs : 0 < stepSize D := stepSize_pos h
  have hsR : ((stepSize D : ℕ) : ℝ) ≠ 0 := by positivity
  have hfin : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    constructor
    simp [Real.volume_Ioc]
  have hmeas : ∀ ρ : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => ‖Lhat D θ‖ ^ (2 * ρ))
      (MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)) := fun ρ =>
    (((continuous_Lhat D).norm).pow (2 * ρ)).aestronglyMeasurable
  have hbound : ∀ ρ : ℕ, ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)),
      ‖‖Lhat D θ‖ ^ (2 * ρ)‖ ≤ (1 : ℝ) := by
    intro ρ
    filter_upwards with θ
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_one₀ (norm_nonneg _) (norm_Lhat_le_one hDne θ)
  have hlim : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) 1)),
      Tendsto (fun ρ : ℕ => ‖Lhat D θ‖ ^ (2 * ρ)) atTop (nhds 0) := by
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_
      (Set.Countable.measure_zero
        (Set.countable_range (fun k : ℤ => (k : ℝ) / ((stepSize D : ℕ) : ℝ))) _)
    intro θ hθ
    simp only [Set.mem_setOf_eq] at hθ
    by_contra hnot
    refine hθ ?_
    have hne : ‖Lhat D θ‖ ≠ 1 := by
      intro he
      obtain ⟨k, hk⟩ := (abs_Lhat_eq_one_iff h.zero_mem θ).1 he
      exact hnot ⟨k, by field_simp; linarith [hk]⟩
    have hlt : ‖Lhat D θ‖ < 1 := lt_of_le_of_ne (norm_Lhat_le_one hDne θ) hne
    have h2 : ‖Lhat D θ‖ ^ 2 < 1 := by nlinarith [norm_nonneg (Lhat D θ)]
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) h2
    refine hp.congr fun ρ => ?_
    rw [← pow_mul]
  have hmain := MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun _ : ℝ => (1:ℝ)) hmeas (MeasureTheory.integrable_const 1) hbound hlim
  simpa using hmain

/-! ### From the difference polynomial back to the sequence -/

theorem IsRat.of_mul_left {r x : ℝ} (hr : IsRat r) (hr0 : r ≠ 0) (hrx : IsRat (r * x)) :
    IsRat x := by
  obtain ⟨a, ha⟩ := hr
  obtain ⟨c, hc⟩ := hrx
  have ha0 : (a : ℝ) ≠ 0 := by rw [← ha]; exact hr0
  have ha0' : a ≠ 0 := by
    intro hh
    apply ha0
    rw [hh]
    norm_num
  refine ⟨c / a, ?_⟩
  have hx : x = (r * x) / r := by field_simp
  rw [hx, hc, ha]
  push_cast
  ring

/-- The proportion of bad pairs can be made arbitrarily small. -/
theorem exists_rho_card_badPairs_le (h : Standing b D) {c : ℤ × ℤ} (hc : c ≠ 0) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ ρ : ℕ, 1 ≤ ρ ∧ ((badPairs b D c ρ).card : ℝ) ≤ ε * ((D.card : ℝ) ^ ρ) ^ 2 := by
  by_cases hc1 : c.1 = 0
  · have hc2 : c.2 ≠ 0 := by
      intro h2
      exact hc (Prod.ext hc1 h2)
    have hlim := tendsto_integral_Lhat_pow h
    obtain ⟨ρ, hρ1, hρ2⟩ :=
      ((eventually_ge_atTop 1).and (Filter.Tendsto.eventually_lt_const hε hlim)).exists
    refine ⟨ρ, hρ1, ?_⟩
    rw [card_badPairs_fst_zero h hc1 hc2]
    have hpos : (0:ℝ) < ((D.card : ℝ) ^ ρ) ^ 2 := by
      have : 0 < D.card := by have := h.two_le_card; omega
      positivity
    nlinarith [hρ2, hpos]
  · obtain ⟨ρ, hρ1, hρ2⟩ := exists_linear_le_pow (d := D.card) h.two_le_card (b - 1) hε
    refine ⟨ρ, hρ1, ?_⟩
    have hle := card_badPairs_le_of_fst_ne h hc1 ρ
    have hR : ((badPairs b D c ρ).card : ℝ)
        ≤ ((D.card : ℝ) ^ ρ) * (((b - 1 : ℕ) : ℝ) * ρ + 1) := by
      have := (Nat.cast_le (α := ℝ)).2 hle
      push_cast at this
      linarith
    have hpow : (0:ℝ) ≤ (D.card : ℝ) ^ ρ := by positivity
    nlinarith [hR, hρ2, hpow]

theorem polyEval_cantorSeq (q : MvPolynomial (Fin 2) ℝ) (n : ℕ) :
    polyEval q (cantorSeq b D n)
      = eval ![((enum b D n : ℕ) : ℝ), ((sumDigits b (enum b D n) : ℕ) : ℝ)] q := by
  rw [polyEval]
  congr 2
  funext i
  fin_cases i <;> simp [cantorSeq]

theorem polyEval_substAffine_cantorSeq (h : Standing b D) (q : MvPolynomial (Fin 2) ℝ)
    (ρ m : ℕ) {j : ℕ} (hj : j < D.card ^ ρ) :
    polyEval (substAffine (((b ^ ρ : ℕ) : ℤ) : ℝ) (((enum b D j : ℕ) : ℤ) : ℝ)
        (((sumDigits b (enum b D j) : ℕ) : ℤ) : ℝ) q) (cantorSeq b D m)
      = polyEval q (cantorSeq b D (D.card ^ ρ * m + j)) := by
  rw [polyEval_cantorSeq, polyEval_cantorSeq, eval_substAffine]
  congr 2
  funext i
  fin_cases i
  · simp only [Matrix.cons_val_zero]
    rw [enum_block' h ρ m hj]
    push_cast
    ring
  · simp only [Matrix.cons_val_one, Matrix.head_cons]
    rw [sumDigits_enum_block' h ρ m hj]
    push_cast
    ring

/-- The difference polynomial evaluates to the difference of the two shifted
values of `p` along the Cantor sequence. -/
theorem polyEval_diffPoly_cantorSeq (h : Standing b D) (q : MvPolynomial (Fin 2) ℝ)
    (ρ m : ℕ) {j j' : ℕ} (hj : j < D.card ^ ρ) (hj' : j' < D.card ^ ρ) :
    polyEval (diffPoly ((b ^ ρ : ℕ) : ℤ) ((enum b D j : ℕ) : ℤ)
        ((sumDigits b (enum b D j) : ℕ) : ℤ) ((enum b D j' : ℕ) : ℤ)
        ((sumDigits b (enum b D j') : ℕ) : ℤ) q) (cantorSeq b D m)
      = polyEval q (cantorSeq b D (D.card ^ ρ * m + j))
        - polyEval q (cantorSeq b D (D.card ^ ρ * m + j')) := by
  rw [diffPoly, polyEval, map_sub, ← polyEval, ← polyEval,
    polyEval_substAffine_cantorSeq h q ρ m hj, polyEval_substAffine_cantorSeq h q ρ m hj']

/-- The difference polynomial attached to a pair `(j, j')` of offsets inside a
block of length `δ^ρ`. -/
noncomputable def blockDiff (b : ℕ) (D : Finset ℕ) (p : MvPolynomial (Fin 2) ℝ)
    (ρ j j' : ℕ) : MvPolynomial (Fin 2) ℝ :=
  diffPoly ((b ^ ρ : ℕ) : ℤ) ((enum b D j : ℕ) : ℤ) ((sumDigits b (enum b D j) : ℕ) : ℤ)
    ((enum b D j' : ℕ) : ℤ) ((sumDigits b (enum b D j') : ℕ) : ℤ) p

theorem irrDegLE_blockDiff {p : MvPolynomial (Fin 2) ℝ} {l : ℕ} (hp1 : IrrDegLE p (l + 1))
    (ρ j j' : ℕ) : IrrDegLE (blockDiff b D p ρ j j') l :=
  irrDegLE_diffPoly hp1 _ _ _ _ _

theorem polyEval_blockDiff_cantorSeq (h : Standing b D) (p : MvPolynomial (Fin 2) ℝ)
    (ρ m : ℕ) {j j' : ℕ} (hj : j < D.card ^ ρ) (hj' : j' < D.card ^ ρ) :
    polyEval (blockDiff b D p ρ j j') (cantorSeq b D m)
      = polyEval p (cantorSeq b D (D.card ^ ρ * m + j))
        - polyEval p (cantorSeq b D (D.card ^ ρ * m + j')) :=
  polyEval_diffPoly_cantorSeq h p ρ m hj hj'

/-- A pair whose difference polynomial is not irrational is a bad pair. -/
theorem mem_badPairs_of_not_irrationalPoly (h : Standing b D) {l : ℕ} (hl : 1 ≤ l)
    {p : MvPolynomial (Fin 2) ℝ} (hp1 : IrrDegLE p (l + 1)) {c : ℤ × ℤ}
    (hcbad : ∀ w : ℤ × ℤ, (∀ m : Fin 2 →₀ ℕ, m 0 + m 1 = l →
        ¬ Irrational ((dirDeriv w p).coeff m)) → c.1 * w.1 + c.2 * w.2 = 0)
    (ρ : ℕ) {j j' : ℕ} (hj : j < D.card ^ ρ) (hj' : j' < D.card ^ ρ)
    (hnot : ¬ IsIrrationalPoly (blockDiff b D p ρ j j')) :
    ((j, j') : ℕ × ℕ) ∈ badPairs b D c ρ := by
  have hb : 0 < b := by have := h.three_le_base; omega
  have hApos : (0:ℝ) < (((b ^ ρ : ℕ) : ℤ) : ℝ) := by
    have : (0:ℝ) < ((b ^ ρ : ℕ) : ℝ) := by positivity
    push_cast at this ⊢
    exact this
  have hA : (((b ^ ρ : ℕ) : ℤ) : ℝ) ≠ 0 := ne_of_gt hApos
  have hnot' : ∀ m : Fin 2 →₀ ℕ, m ≠ 0 →
      ¬ Irrational ((blockDiff b D p ρ j j').coeff m) := by
    intro m hm
    rw [IsIrrationalPoly] at hnot
    push Not at hnot
    exact hnot m hm
  have hrat : ∀ m : Fin 2 →₀ ℕ, m 0 + m 1 = l →
      ¬ Irrational ((dirDeriv (((enum b D j : ℕ) : ℤ) - ((enum b D j' : ℕ) : ℤ),
        ((sumDigits b (enum b D j) : ℕ) : ℤ)
          - ((sumDigits b (enum b D j') : ℕ) : ℤ)) p).coeff m) := by
    intro m hm
    have hm0 : m ≠ 0 := by
      intro hc0
      rw [hc0] at hm
      simp only [Finsupp.coe_zero, Pi.zero_apply, add_zero] at hm
      omega
    have h1 : IsRat ((blockDiff b D p ρ j j').coeff m) := isRat_iff.2 (hnot' m hm0)
    have h2 := coeff_diffPoly_sub_isRat hp1 ((b ^ ρ : ℕ) : ℤ) ((enum b D j : ℕ) : ℤ)
      ((sumDigits b (enum b D j) : ℕ) : ℤ) ((enum b D j' : ℕ) : ℤ)
      ((sumDigits b (enum b D j') : ℕ) : ℤ) hm
    have h3 : IsRat ((((b ^ ρ : ℕ) : ℤ) : ℝ) ^ (m 0)
        * (dirDeriv (((enum b D j : ℕ) : ℤ) - ((enum b D j' : ℕ) : ℤ),
            ((sumDigits b (enum b D j) : ℕ) : ℤ)
              - ((sumDigits b (enum b D j') : ℕ) : ℤ)) p).coeff m) := by
      have h4 := h1.sub h2
      simpa [blockDiff] using h4
    exact isRat_iff.1
      (IsRat.of_mul_left ((isRat_intCast _).pow _) (pow_ne_zero _ hA) h3)
  have hzero := hcbad _ hrat
  rw [mem_badPairs]
  refine ⟨⟨hj, hj'⟩, ?_⟩
  simp only at hzero ⊢
  linear_combination hzero

/-! ### The induction step and the main theorem

The induction step follows the blueprint (`thm:UDstep`):

* split `[M, N)` into blocks of length `δ^ρ` (`window_block_split`), so that on
  a block the pair `(κ(δ^ρ m + j), s_b(κ(δ^ρ m + j)))` equals
  `(b^ρ κ(m) + κ(j), s_b(κ(m)) + s_b(κ(j)))` (`enum_block'`,
  `sumDigits_enum_block'`);
* apply Cauchy--Schwarz in the block index (`norm_sum_sq_le_card_mul`) and
  expand `|∑_j e(p(·))|²` as a double sum of differences
  (`normSq_sum_expc`), which replaces `p` by the difference polynomials
  `blockDiff b D p ρ j j'`;
* `irrDegLE_blockDiff` drops the irrational degree to `l`, and
  `coeff_diffPoly_sub_isRat` identifies the degree-`l` coefficients with those
  of `b^{ρ m₀} ∂_w p`, so by `badDirections` the inductive hypothesis applies
  unless `(j, j')` is *bad* (`mem_badPairs_of_not_irrationalPoly`);
* the proportion of bad pairs tends to `0`
  (`exists_rho_card_badPairs_le`): when `c₁ ≠ 0` a bad partner is determined by
  its digit sum, of which there are at most `(b-1)ρ + 1`; when `c₁ = 0` the
  count equals `δ^{2ρ} ∫₀¹ |L̂(θ)|^{2ρ} dθ`, which tends to `0` by
  `abs_Lhat_eq_one_iff` and dominated convergence.
-/

/-- Blueprint: `thm:UDstep`.  If the averaging conclusion holds for all
polynomials of irrational degree at most `l`, it holds for all polynomials of
irrational degree at most `l + 1`. -/
theorem UD_succ (h : Standing b D) {l : ℕ} (hl : 1 ≤ l)
    (ih : ∀ r : MvPolynomial (Fin 2) ℝ, IrrDegLE r l → IsIrrationalPoly r →
      UniformAvg (cantorSeq b D) r)
    {p : MvPolynomial (Fin 2) ℝ} (hp1 : IrrDegLE p (l + 1))
    (hp : IsIrrationalPoly p) :
    UniformAvg (cantorSeq b D) p := by
  classical
  by_cases hdrop : IrrDegLE p l
  · exact ih p hdrop hp
  obtain ⟨m₀, hm₀deg, hm₀irr⟩ :
      ∃ m₀ : Fin 2 →₀ ℕ, m₀ 0 + m₀ 1 = l + 1 ∧ Irrational (p.coeff m₀) := by
    rw [IrrDegLE] at hdrop
    push Not at hdrop
    obtain ⟨m₀, hlt, hirr⟩ := hdrop
    refine ⟨m₀, ?_, hirr⟩
    by_contra hne
    exact (hp1 m₀ (by omega)) hirr
  obtain ⟨c, hcne, hcbad⟩ := badDirections p (show 1 ≤ l + 1 by omega) hm₀deg hm₀irr
  simp only [Nat.add_sub_cancel] at hcbad
  intro ε hε
  have hcard : 0 < D.card := by have := h.two_le_card; omega
  obtain ⟨ρ, hρ1, hρ2⟩ :=
    exists_rho_card_badPairs_le h hcne (show (0:ℝ) < ε ^ 2 / 8 by positivity)
  have hΛpos : 0 < D.card ^ ρ := pow_pos hcard ρ
  have hΛR : (0:ℝ) < ((D.card ^ ρ : ℕ) : ℝ) := by exact_mod_cast hΛpos
  have hKex : ∀ z : ℕ × ℕ, ∃ K : ℕ, IsIrrationalPoly (blockDiff b D p ρ z.1 z.2) →
      ∀ M' N' : ℕ, M' + K ≤ N' →
        ‖((N' - M' : ℕ) : ℂ)⁻¹ * ∑ m ∈ Ico M' N',
          expc (polyEval (blockDiff b D p ρ z.1 z.2) (cantorSeq b D m))‖ < ε ^ 2 / 8 := by
    intro z
    by_cases hgood : IsIrrationalPoly (blockDiff b D p ρ z.1 z.2)
    · obtain ⟨K, hK⟩ := ih (blockDiff b D p ρ z.1 z.2) (irrDegLE_blockDiff hp1 ρ z.1 z.2)
        hgood (ε ^ 2 / 8) (by positivity)
      exact ⟨K, fun _ => hK⟩
    · exact ⟨0, fun hc => absurd hc hgood⟩
  choose KK hKK using hKex
  refine ⟨max (D.card ^ ρ * ((range (D.card ^ ρ) ×ˢ range (D.card ^ ρ)).sup (fun z => KK z) + 2))
    (⌈4 * ((D.card ^ ρ : ℕ) : ℝ) / ε⌉₊ + 1), ?_⟩
  intro M N hMN
  -- the window split
  have hf1 : ‖(∑ n ∈ Ico M N, expc (polyEval p (cantorSeq b D n)))
      - ∑ m ∈ Ico ((M + D.card ^ ρ - 1) / D.card ^ ρ) (N / D.card ^ ρ),
          ∑ j ∈ range (D.card ^ ρ),
            expc (polyEval p (cantorSeq b D (D.card ^ ρ * m + j)))‖
      ≤ 2 * ((D.card ^ ρ : ℕ) : ℝ) :=
    window_block_split hΛpos _ (fun n => le_of_eq (norm_expc _)) M N
  obtain ⟨hA, hB⟩ := ceil_div_bounds (q := D.card ^ ρ) (M := M) hΛpos
  obtain ⟨hC, hDD⟩ := floor_div_bounds (q := D.card ^ ρ) (N := N) hΛpos
  have hblk := block_count_le (q := D.card ^ ρ) (M := M) (N := N) hΛpos
  obtain ⟨M₁, hM₁⟩ : ∃ k, (M + D.card ^ ρ - 1) / D.card ^ ρ = k := ⟨_, rfl⟩
  obtain ⟨N₁, hN₁⟩ : ∃ k, N / D.card ^ ρ = k := ⟨_, rfl⟩
  rw [hM₁] at hA hB hf1 hblk
  rw [hN₁] at hC hDD hf1 hblk
  -- the numeric facts about the block range
  have hKs : D.card ^ ρ * ((range (D.card ^ ρ) ×ˢ range (D.card ^ ρ)).sup (fun z => KK z) + 2)
      ≤ max (D.card ^ ρ * ((range (D.card ^ ρ) ×ˢ range (D.card ^ ρ)).sup (fun z => KK z) + 2))
        (⌈4 * ((D.card ^ ρ : ℕ) : ℝ) / ε⌉₊ + 1) := le_max_left _ _
  have hCeil : ⌈4 * ((D.card ^ ρ : ℕ) : ℝ) / ε⌉₊ + 1
      ≤ max (D.card ^ ρ * ((range (D.card ^ ρ) ×ˢ range (D.card ^ ρ)).sup (fun z => KK z) + 2))
        (⌈4 * ((D.card ^ ρ : ℕ) : ℝ) / ε⌉₊ + 1) := le_max_right _ _
  have hgt : M₁ + (range (D.card ^ ρ) ×ˢ range (D.card ^ ρ)).sup (fun z => KK z) < N₁ := by
    have e1 : D.card ^ ρ * (M₁ + (range (D.card ^ ρ) ×ˢ range (D.card ^ ρ)).sup (fun z => KK z))
        = D.card ^ ρ * M₁
          + D.card ^ ρ * (range (D.card ^ ρ) ×ˢ range (D.card ^ ρ)).sup (fun z => KK z) := by
      ring
    have e2 : D.card ^ ρ * ((range (D.card ^ ρ) ×ˢ range (D.card ^ ρ)).sup (fun z => KK z) + 2)
        = D.card ^ ρ * (range (D.card ^ ρ) ×ˢ range (D.card ^ ρ)).sup (fun z => KK z)
          + D.card ^ ρ * 2 := by ring
    have e3 : D.card ^ ρ * 2 = D.card ^ ρ + D.card ^ ρ := by ring
    have hlt : D.card ^ ρ
        * (M₁ + (range (D.card ^ ρ) ×ˢ range (D.card ^ ρ)).sup (fun z => KK z))
        < D.card ^ ρ * N₁ := by omega
    exact Nat.lt_of_mul_lt_mul_left hlt
  have hMN₁ : M₁ ≤ N₁ := by omega
  have hdpos : 0 < N₁ - M₁ := by omega
  have hdposR : (0:ℝ) < ((N₁ - M₁ : ℕ) : ℝ) := by exact_mod_cast hdpos
  have hNMpos : 0 < N - M := by omega
  have hNMposR : (0:ℝ) < ((N - M : ℕ) : ℝ) := by exact_mod_cast hNMpos
  -- the differencing identity
  have hW : ∀ m : ℕ, ((‖∑ j ∈ range (D.card ^ ρ),
        expc (polyEval p (cantorSeq b D (D.card ^ ρ * m + j)))‖ : ℝ) : ℂ) ^ 2
      = ∑ j ∈ range (D.card ^ ρ), ∑ j' ∈ range (D.card ^ ρ),
          expc (polyEval (blockDiff b D p ρ j j') (cantorSeq b D m)) := by
    intro m
    rw [← Complex.ofReal_pow, normSq_sum_expc]
    exact Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun j' hj' => by
      rw [polyEval_blockDiff_cantorSeq h p ρ m (Finset.mem_range.1 hj) (Finset.mem_range.1 hj')]
  have hsumC : ((∑ m ∈ Ico M₁ N₁, ‖∑ j ∈ range (D.card ^ ρ),
        expc (polyEval p (cantorSeq b D (D.card ^ ρ * m + j)))‖ ^ 2 : ℝ) : ℂ)
      = ∑ j ∈ range (D.card ^ ρ), ∑ j' ∈ range (D.card ^ ρ), ∑ m ∈ Ico M₁ N₁,
          expc (polyEval (blockDiff b D p ρ j j') (cantorSeq b D m)) := by
    push_cast
    rw [Finset.sum_congr rfl (fun m _ => hW m), Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
  have hsumNonneg : (0:ℝ) ≤ ∑ m ∈ Ico M₁ N₁, ‖∑ j ∈ range (D.card ^ ρ),
      expc (polyEval p (cantorSeq b D (D.card ^ ρ * m + j)))‖ ^ 2 :=
    Finset.sum_nonneg fun m _ => by positivity
  have hsumLe : (∑ m ∈ Ico M₁ N₁, ‖∑ j ∈ range (D.card ^ ρ),
        expc (polyEval p (cantorSeq b D (D.card ^ ρ * m + j)))‖ ^ 2)
      ≤ ∑ j ∈ range (D.card ^ ρ), ∑ j' ∈ range (D.card ^ ρ),
          ‖∑ m ∈ Ico M₁ N₁,
            expc (polyEval (blockDiff b D p ρ j j') (cantorSeq b D m))‖ := by
    calc (∑ m ∈ Ico M₁ N₁, ‖∑ j ∈ range (D.card ^ ρ),
          expc (polyEval p (cantorSeq b D (D.card ^ ρ * m + j)))‖ ^ 2)
        = ‖((∑ m ∈ Ico M₁ N₁, ‖∑ j ∈ range (D.card ^ ρ),
            expc (polyEval p (cantorSeq b D (D.card ^ ρ * m + j)))‖ ^ 2 : ℝ) : ℂ)‖ := by
          rw [norm_ofReal_of_nonneg hsumNonneg]
      _ = ‖∑ j ∈ range (D.card ^ ρ), ∑ j' ∈ range (D.card ^ ρ), ∑ m ∈ Ico M₁ N₁,
            expc (polyEval (blockDiff b D p ρ j j') (cantorSeq b D m))‖ := by rw [hsumC]
      _ ≤ ∑ j ∈ range (D.card ^ ρ), ‖∑ j' ∈ range (D.card ^ ρ), ∑ m ∈ Ico M₁ N₁,
            expc (polyEval (blockDiff b D p ρ j j') (cantorSeq b D m))‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ range (D.card ^ ρ), ∑ j' ∈ range (D.card ^ ρ), ‖∑ m ∈ Ico M₁ N₁,
            expc (polyEval (blockDiff b D p ρ j j') (cantorSeq b D m))‖ :=
          Finset.sum_le_sum fun j _ => norm_sum_le _ _
  -- the good/bad dichotomy, termwise
  have hterm : ∀ z ∈ range (D.card ^ ρ) ×ˢ range (D.card ^ ρ),
      ‖∑ m ∈ Ico M₁ N₁, expc (polyEval (blockDiff b D p ρ z.1 z.2) (cantorSeq b D m))‖
        ≤ ((N₁ - M₁ : ℕ) : ℝ) * (ε ^ 2 / 8)
          + (if z ∈ badPairs b D c ρ then ((N₁ - M₁ : ℕ) : ℝ) else 0) := by
    intro z hz
    have hz1 : z.1 < D.card ^ ρ := Finset.mem_range.1 (Finset.mem_product.1 hz).1
    have hz2 : z.2 < D.card ^ ρ := Finset.mem_range.1 (Finset.mem_product.1 hz).2
    by_cases hgood : IsIrrationalPoly (blockDiff b D p ρ z.1 z.2)
    · have hKle : KK z ≤ (range (D.card ^ ρ) ×ˢ range (D.card ^ ρ)).sup (fun z => KK z) :=
        Finset.le_sup hz
      have hbd := hKK z hgood M₁ N₁ (by omega)
      rw [norm_mul, norm_inv, Complex.norm_natCast] at hbd
      have hlt : ‖∑ m ∈ Ico M₁ N₁,
          expc (polyEval (blockDiff b D p ρ z.1 z.2) (cantorSeq b D m))‖
          < ((N₁ - M₁ : ℕ) : ℝ) * (ε ^ 2 / 8) := by
        rw [inv_mul_eq_div, div_lt_iff₀ hdposR] at hbd
        linarith
      have hif : (0:ℝ) ≤ (if z ∈ badPairs b D c ρ then ((N₁ - M₁ : ℕ) : ℝ) else 0) := by
        split <;> positivity
      linarith
    · have hmem : z ∈ badPairs b D c ρ := by
        have := mem_badPairs_of_not_irrationalPoly h hl hp1 hcbad ρ hz1 hz2 hgood
        simpa using this
      rw [if_pos hmem]
      have htri : ‖∑ m ∈ Ico M₁ N₁,
          expc (polyEval (blockDiff b D p ρ z.1 z.2) (cantorSeq b D m))‖
          ≤ ((N₁ - M₁ : ℕ) : ℝ) := by
        calc ‖∑ m ∈ Ico M₁ N₁,
              expc (polyEval (blockDiff b D p ρ z.1 z.2) (cantorSeq b D m))‖
            ≤ ∑ m ∈ Ico M₁ N₁,
                ‖expc (polyEval (blockDiff b D p ρ z.1 z.2) (cantorSeq b D m))‖ :=
              norm_sum_le _ _
          _ = ((N₁ - M₁ : ℕ) : ℝ) := by simp [norm_expc]
      have : (0:ℝ) ≤ ((N₁ - M₁ : ℕ) : ℝ) * (ε ^ 2 / 8) := by positivity
      linarith
  -- summing the termwise bound
  have hcountbad : ((badPairs b D c ρ).card : ℝ) ≤ (ε ^ 2 / 8) * ((D.card ^ ρ : ℕ) : ℝ) ^ 2 := by
    have := hρ2
    push_cast at this ⊢
    linarith
  have htot : (∑ j ∈ range (D.card ^ ρ), ∑ j' ∈ range (D.card ^ ρ),
        ‖∑ m ∈ Ico M₁ N₁,
          expc (polyEval (blockDiff b D p ρ j j') (cantorSeq b D m))‖)
      ≤ ((N₁ - M₁ : ℕ) : ℝ) * (ε ^ 2 / 4) * ((D.card ^ ρ : ℕ) : ℝ) ^ 2 := by
    rw [← Finset.sum_product']
    calc (∑ z ∈ range (D.card ^ ρ) ×ˢ range (D.card ^ ρ),
          ‖∑ m ∈ Ico M₁ N₁,
            expc (polyEval (blockDiff b D p ρ z.1 z.2) (cantorSeq b D m))‖)
        ≤ ∑ z ∈ range (D.card ^ ρ) ×ˢ range (D.card ^ ρ),
            (((N₁ - M₁ : ℕ) : ℝ) * (ε ^ 2 / 8)
              + (if z ∈ badPairs b D c ρ then ((N₁ - M₁ : ℕ) : ℝ) else 0)) :=
          Finset.sum_le_sum hterm
      _ = ((D.card ^ ρ : ℕ) : ℝ) ^ 2 * (((N₁ - M₁ : ℕ) : ℝ) * (ε ^ 2 / 8))
            + ((((range (D.card ^ ρ) ×ˢ range (D.card ^ ρ)) ∩ badPairs b D c ρ).card : ℕ) : ℝ)
              * ((N₁ - M₁ : ℕ) : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_mem, Finset.sum_const,
            Finset.card_product, Finset.card_range]
          push_cast
          ring
      _ ≤ ((D.card ^ ρ : ℕ) : ℝ) ^ 2 * (((N₁ - M₁ : ℕ) : ℝ) * (ε ^ 2 / 8))
            + ((ε ^ 2 / 8) * ((D.card ^ ρ : ℕ) : ℝ) ^ 2) * ((N₁ - M₁ : ℕ) : ℝ) := by
          have hsub : (((range (D.card ^ ρ) ×ˢ range (D.card ^ ρ))
              ∩ badPairs b D c ρ).card : ℝ) ≤ ((badPairs b D c ρ).card : ℝ) := by
            exact_mod_cast Finset.card_le_card Finset.inter_subset_right
          nlinarith [hdposR, hsub, hcountbad]
      _ = ((N₁ - M₁ : ℕ) : ℝ) * (ε ^ 2 / 4) * ((D.card ^ ρ : ℕ) : ℝ) ^ 2 := by ring
  -- Cauchy--Schwarz
  have hCS : ‖∑ m ∈ Ico M₁ N₁, ∑ j ∈ range (D.card ^ ρ),
        expc (polyEval p (cantorSeq b D (D.card ^ ρ * m + j)))‖ ^ 2
      ≤ ((N₁ - M₁ : ℕ) : ℝ) * ∑ m ∈ Ico M₁ N₁, ‖∑ j ∈ range (D.card ^ ρ),
          expc (polyEval p (cantorSeq b D (D.card ^ ρ * m + j)))‖ ^ 2 := by
    have := norm_sum_sq_le_card_mul (Ico M₁ N₁)
      (fun m => ∑ j ∈ range (D.card ^ ρ),
        expc (polyEval p (cantorSeq b D (D.card ^ ρ * m + j))))
    simpa using this
  have hTsq : ‖∑ m ∈ Ico M₁ N₁, ∑ j ∈ range (D.card ^ ρ),
        expc (polyEval p (cantorSeq b D (D.card ^ ρ * m + j)))‖ ^ 2
      ≤ (((N₁ - M₁ : ℕ) : ℝ) * ((D.card ^ ρ : ℕ) : ℝ) * (ε / 2)) ^ 2 := by
    have h1 : (∑ m ∈ Ico M₁ N₁, ‖∑ j ∈ range (D.card ^ ρ),
        expc (polyEval p (cantorSeq b D (D.card ^ ρ * m + j)))‖ ^ 2)
        ≤ ((N₁ - M₁ : ℕ) : ℝ) * (ε ^ 2 / 4) * ((D.card ^ ρ : ℕ) : ℝ) ^ 2 :=
      le_trans hsumLe htot
    nlinarith [hCS, h1, hdposR, hΛR]
  have hT : ‖∑ m ∈ Ico M₁ N₁, ∑ j ∈ range (D.card ^ ρ),
        expc (polyEval p (cantorSeq b D (D.card ^ ρ * m + j)))‖
      ≤ ((N₁ - M₁ : ℕ) : ℝ) * ((D.card ^ ρ : ℕ) : ℝ) * (ε / 2) := by
    exact le_of_sq_le_sq (norm_nonneg _) (by positivity) hTsq
  -- the block count and the leftover
  have hblkR : ((D.card ^ ρ : ℕ) : ℝ) * ((N₁ - M₁ : ℕ) : ℝ) ≤ ((N - M : ℕ) : ℝ) := by
    exact_mod_cast hblk
  have hleft : 2 * ((D.card ^ ρ : ℕ) : ℝ) < ((N - M : ℕ) : ℝ) * (ε / 2) := by
    have hceil : (4 * ((D.card ^ ρ : ℕ) : ℝ) / ε) ≤ (⌈4 * ((D.card ^ ρ : ℕ) : ℝ) / ε⌉₊ : ℝ) :=
      Nat.le_ceil _
    have hge : ((⌈4 * ((D.card ^ ρ : ℕ) : ℝ) / ε⌉₊ : ℕ) : ℝ) + 1 ≤ ((N - M : ℕ) : ℝ) := by
      have : (⌈4 * ((D.card ^ ρ : ℕ) : ℝ) / ε⌉₊ : ℕ) + 1 ≤ N - M := by omega
      exact_mod_cast this
    have h4 : 4 * ((D.card ^ ρ : ℕ) : ℝ) / ε < ((N - M : ℕ) : ℝ) := by linarith
    rw [div_lt_iff₀ hε] at h4
    linarith
  -- conclude
  have hS : ‖∑ n ∈ Ico M N, expc (polyEval p (cantorSeq b D n))‖
      < ((N - M : ℕ) : ℝ) * ε := by
    have htri : ‖∑ n ∈ Ico M N, expc (polyEval p (cantorSeq b D n))‖
        ≤ ‖∑ m ∈ Ico M₁ N₁, ∑ j ∈ range (D.card ^ ρ),
            expc (polyEval p (cantorSeq b D (D.card ^ ρ * m + j)))‖
          + 2 * ((D.card ^ ρ : ℕ) : ℝ) := by
      have := norm_sub_norm_le (∑ n ∈ Ico M N, expc (polyEval p (cantorSeq b D n)))
        (∑ m ∈ Ico M₁ N₁, ∑ j ∈ range (D.card ^ ρ),
          expc (polyEval p (cantorSeq b D (D.card ^ ρ * m + j))))
      linarith [hf1, this]
    nlinarith [htri, hT, hblkR, hleft, hdposR, hΛR, hε]
  rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_eq_div, div_lt_iff₀ hNMposR]
  linarith [hS]

/-- The averaging conclusion for every polynomial of irrational degree at
most `l + 1`, by induction on `l`. -/
theorem UD_le (h : Standing b D) :
    ∀ l : ℕ, ∀ p : MvPolynomial (Fin 2) ℝ, IrrDegLE p (l + 1) → IsIrrationalPoly p →
      UniformAvg (cantorSeq b D) p := by
  intro l
  induction l with
  | zero => exact fun p hp1 hp => UD_one h hp1 hp
  | succ k ih => exact fun p hp1 hp => UD_succ h (by omega) ih hp1 hp

/-- Blueprint: `thm:polyUniform`, Theorem 4.3 of the paper.  The sequence
`n ↦ (κ(n), s_b(κ(n)))` is polynomially uniformly distributed. -/
theorem isPUDU (h : Standing b D) : IsPUDU (cantorSeq b D) := fun p hp =>
  UD_le h p.totalDegree p ((irrDegLE_totalDegree p).mono (Nat.le_succ _)) hp

end IntegerCantorSet
