/-
The key exponential sum.

Blueprint: `blueprint/src/content.tex`, Chapter 4 (`chap:expsum`); Lemma 4.7
of the paper.

The target of this file is `tendsto_expSum`: the averages of
`Φ(n) = e(κ(n) α + s_b(κ(n)) β)` over a window `M ≤ n < N` converge, and
converge to `0` unless the pair `(α, β)` is *exceptional*.

This file contains no `sorry`.
-/
import IntegerCantorSets.Structure

namespace IntegerCantorSet

open Finset Filter
open scoped Real

variable {b : ℕ} {D : Finset ℕ}

/-! ### The additive character `e(x) = exp(2 π i x)` -/

/-- `expc x = e(x) = exp(2 π i x)`. -/
noncomputable def expc (x : ℝ) : ℂ := Complex.exp ((2 * π * x : ℝ) * Complex.I)

@[simp] theorem expc_zero : expc 0 = 1 := by
  simp [expc]

theorem expc_add (x y : ℝ) : expc (x + y) = expc x * expc y := by
  rw [expc, expc, expc, ← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] theorem norm_expc (x : ℝ) : ‖expc x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem expc_ne_zero (x : ℝ) : expc x ≠ 0 := Complex.exp_ne_zero _

theorem expc_eq_one_iff {x : ℝ} : expc x = 1 ↔ ∃ k : ℤ, x = k := by
  rw [expc, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    have h1 : ((2 * π * x : ℝ) : ℂ) = (n : ℂ) * (2 * π) := by
      apply mul_right_cancel₀ hI
      rw [hn]; ring
    have h2 : (2 * π) * x = (2 * π) * (n : ℝ) := by
      have : (2 : ℝ) * π * x = (n : ℝ) * (2 * π) := by exact_mod_cast h1
      linarith
    have hpi : (2 : ℝ) * π ≠ 0 := by positivity
    exact mul_left_cancel₀ hpi h2
  · rintro ⟨k, rfl⟩
    exact ⟨k, by push_cast; ring⟩

theorem expc_zpow (k : ℤ) (x : ℝ) : expc ((k : ℝ) * x) = expc x ^ k := by
  rw [expc, expc, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

/-! ### Distance to the nearest integer -/

/-- `distInt x` is `‖x‖`, the distance from `x` to the nearest integer. -/
noncomputable def distInt (x : ℝ) : ℝ := |x - round x|

theorem distInt_nonneg (x : ℝ) : 0 ≤ distInt x := abs_nonneg _

theorem distInt_le_half (x : ℝ) : distInt x ≤ 1 / 2 := abs_sub_round x

theorem round_eq_of_abs_sub_lt {x : ℝ} {k : ℤ} (h : |x - k| < 1 / 2) : round x = k := by
  have h0 : round (x - (k : ℝ)) = 0 := by
    rw [round_eq_zero_iff, Set.mem_Ico]
    have := abs_lt.1 h
    constructor <;> linarith [this.1, this.2]
  rw [round_sub_intCast] at h0
  omega

theorem distInt_eq_of_abs_sub_lt {x : ℝ} {k : ℤ} (h : |x - k| < 1 / 2) :
    distInt x = |x - k| := by
  rw [distInt, round_eq_of_abs_sub_lt h]

theorem distInt_le (x : ℝ) (k : ℤ) : distInt x ≤ |x - k| := by
  rcases lt_or_ge |x - (k : ℝ)| (1 / 2) with hk | hk
  · exact le_of_eq (distInt_eq_of_abs_sub_lt hk)
  · exact le_trans (abs_sub_round x) hk

theorem distInt_eq_zero_iff {x : ℝ} : distInt x = 0 ↔ ∃ k : ℤ, x = k := by
  constructor
  · intro h
    exact ⟨round x, by have := abs_eq_zero.1 h; linarith [sub_eq_zero.1 this]⟩
  · rintro ⟨k, rfl⟩
    have := distInt_le ((k : ℝ)) k
    have := distInt_nonneg ((k : ℝ))
    simp at *
    linarith

theorem distInt_add_le (x y : ℝ) : distInt (x + y) ≤ distInt x + distInt y := by
  calc distInt (x + y) ≤ |(x + y) - ((round x + round y : ℤ) : ℝ)| := distInt_le _ _
    _ = |(x - (round x : ℝ)) + (y - (round y : ℝ))| := by push_cast; ring_nf
    _ ≤ |x - (round x : ℝ)| + |y - (round y : ℝ)| := abs_add_le _ _
    _ = distInt x + distInt y := rfl

theorem distInt_neg (x : ℝ) : distInt (-x) = distInt x := by
  refine le_antisymm ?_ ?_
  · calc distInt (-x) ≤ |(-x) - ((-round x : ℤ) : ℝ)| := distInt_le _ _
      _ = distInt x := by rw [distInt]; push_cast; rw [← abs_neg]; ring_nf
  · calc distInt x ≤ |x - ((-round (-x) : ℤ) : ℝ)| := distInt_le _ _
      _ = distInt (-x) := by rw [distInt]; push_cast; rw [← abs_neg]; ring_nf

@[simp] theorem distInt_add_int (x : ℝ) (k : ℤ) : distInt (x + k) = distInt x := by
  rw [distInt, distInt, round_add_intCast]
  push_cast
  ring_nf

theorem distInt_int_mul (k : ℤ) (x : ℝ) : distInt ((k : ℝ) * x) ≤ |(k : ℝ)| * distInt x := by
  calc distInt ((k : ℝ) * x) ≤ |(k : ℝ) * x - ((k * round x : ℤ) : ℝ)| := distInt_le _ _
    _ = |(k : ℝ)| * distInt x := by
        push_cast
        rw [← mul_sub, abs_mul]
        rfl

theorem distInt_sum_le {ι : Type*} (s : Finset ι) (g : ι → ℝ) :
    distInt (∑ i ∈ s, g i) ≤ ∑ i ∈ s, distInt (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [distInt]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact le_trans (distInt_add_le _ _) (by linarith)

theorem tendsto_zero_of_sq {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hsq : Tendsto (fun n => f n ^ 2) atTop (nhds 0)) : Tendsto f atTop (nhds 0) := by
  have h := hsq.sqrt
  rw [Real.sqrt_zero] at h
  exact h.congr fun n => Real.sqrt_sq (hf n)

theorem distInt_nat_mul {n : ℕ} {x : ℝ} (h : (n : ℝ) * distInt x < 1 / 2) :
    distInt ((n : ℝ) * x) = n * distInt x := by
  have hk : |((n : ℝ) * x) - (((n : ℤ) * round x : ℤ) : ℝ)| = (n : ℝ) * distInt x := by
    push_cast
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]
    rfl
  rw [distInt_eq_of_abs_sub_lt (k := (n : ℤ) * round x) (by rw [hk]; exact h), hk]

/-- `|1 - e(x)| = 2 sin(π‖x‖)`. -/
theorem norm_one_sub_expc (x : ℝ) :
    ‖1 - expc x‖ = 2 * Real.sin (π * distInt x) := by
  have hu : |x - (round x : ℝ)| ≤ 1 / 2 := abs_sub_round x
  have hdu : distInt x = |x - (round x : ℝ)| := rfl
  have hcos : Real.cos (2 * π * x) = Real.cos (2 * π * (x - (round x : ℝ))) := by
    have he : 2 * π * x = 2 * π * (x - (round x : ℝ)) + (round x : ℝ) * (2 * π) := by ring
    rw [he, Real.cos_add_int_mul_two_pi]
  have hre : (expc x).re = Real.cos (2 * π * x) := Complex.exp_ofReal_mul_I_re _
  have him : (expc x).im = Real.sin (2 * π * x) := Complex.exp_ofReal_mul_I_im _
  have hsq : ‖1 - expc x‖ ^ 2 = 2 - 2 * Real.cos (2 * π * x) := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, hre, him]
    nlinarith [Real.sin_sq_add_cos_sq (2 * π * x)]
  set u : ℝ := x - (round x : ℝ) with hudef
  have habs : |u| ≤ 1 / 2 := hu
  have hcos2 : Real.cos (2 * π * u) = 1 - 2 * Real.sin (π * u) ^ 2 := by
    have : 2 * π * u = 2 * (π * u) := by ring
    rw [this, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (π * u)]
  have hsin : Real.sin (π * u) ^ 2 = Real.sin (π * |u|) ^ 2 := by
    rcases abs_cases u with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]
    · rw [h1, mul_neg, Real.sin_neg]; ring
  have hnn : 0 ≤ Real.sin (π * |u|) := by
    apply Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le (abs_nonneg u))
    nlinarith [Real.pi_pos]
  have hfin : ‖1 - expc x‖ ^ 2 = (2 * Real.sin (π * |u|)) ^ 2 := by
    rw [hsq, hcos, hcos2, hsin]; ring
  rw [hdu]
  nlinarith [hfin, norm_nonneg (1 - expc x), hnn]

/-- Blueprint: the quantitative link `|1 - e(x)| ≥ 4‖x‖`. -/
theorem four_mul_distInt_le (x : ℝ) : 4 * distInt x ≤ ‖1 - expc x‖ := by
  rw [norm_one_sub_expc]
  have h1 : 0 ≤ π * distInt x := mul_nonneg Real.pi_pos.le (distInt_nonneg x)
  have h2 : π * distInt x ≤ π / 2 := by
    have := distInt_le_half x
    nlinarith [Real.pi_pos]
  have hs := Real.mul_le_sin h1 h2
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have heq : 2 / π * (π * distInt x) = 2 * distInt x := by field_simp
  rw [heq] at hs
  linarith

/-! ### Bézout for a finite set -/

/-- `gcd D` is an integer combination of the elements of `D`. -/
theorem exists_gcd_eq_sum (D : Finset ℕ) :
    ∃ f : ℕ → ℤ, (stepSize D : ℤ) = ∑ d ∈ D, f d * d := by
  classical
  induction D using Finset.induction with
  | empty => exact ⟨fun _ => 0, by simp [stepSize]⟩
  | insert a s ha ih =>
    obtain ⟨f, hf⟩ := ih
    set u : ℤ := Nat.gcdA a (stepSize s) with hu
    set v : ℤ := Nat.gcdB a (stepSize s) with hv
    set g : ℕ → ℤ := fun x => if x = a then u else v * f x with hgdef
    refine ⟨g, ?_⟩
    have hg : stepSize (insert a s) = Nat.gcd a (stepSize s) := by
      simp only [stepSize, Finset.gcd_insert]
      rfl
    have hb : (Nat.gcd a (stepSize s) : ℤ) = a * u + stepSize s * v :=
      Nat.gcd_eq_gcd_ab a (stepSize s)
    have hga : g a = u := by simp [hgdef]
    have hs : ∑ d ∈ s, g d * (d : ℤ) = v * ∑ d ∈ s, f d * d := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hne : d ≠ a := fun h => ha (h ▸ hd)
      simp only [hgdef, hne, ite_false]
      ring
    rw [Finset.sum_insert ha, hga, hs, ← hf, hg, hb]
    ring

/-! ### The single-digit character sum `L̂` -/

/-- `Lhat D θ = δ⁻¹ ∑_{d ∈ D} e(dθ)`, where `δ = |D|`.

Blueprint: `def:Lhat`. -/
noncomputable def Lhat (D : Finset ℕ) (θ : ℝ) : ℂ :=
  (D.card : ℂ)⁻¹ * ∑ d ∈ D, expc (d * θ)

theorem norm_Lhat_le_one (hD : D.Nonempty) (θ : ℝ) : ‖Lhat D θ‖ ≤ 1 := by
  have hc : (0 : ℝ) < D.card := by exact_mod_cast Finset.card_pos.2 hD
  have h1 : ‖∑ d ∈ D, expc ((d : ℝ) * θ)‖ ≤ (D.card : ℝ) := by
    calc ‖∑ d ∈ D, expc ((d : ℝ) * θ)‖ ≤ ∑ d ∈ D, ‖expc ((d : ℝ) * θ)‖ := norm_sum_le _ _
      _ = (D.card : ℝ) := by simp
  rw [Lhat, norm_mul, norm_inv, Complex.norm_natCast]
  calc (D.card : ℝ)⁻¹ * ‖∑ d ∈ D, expc ((d : ℝ) * θ)‖
      ≤ (D.card : ℝ)⁻¹ * (D.card : ℝ) := by
        exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hc)

theorem norm_prod_Lhat_le_one (hD : D.Nonempty) (g : ℕ → ℝ) (l : ℕ) :
    ‖∏ c ∈ range l, Lhat D (g c)‖ ≤ 1 := by
  induction l with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, norm_mul]
    have h1 := norm_Lhat_le_one hD (g k)
    nlinarith [ih, h1, norm_nonneg (∏ c ∈ range k, Lhat D (g c)),
      norm_nonneg (Lhat D (g k))]

/-- The quantitative defect estimate behind `abs_Lhat_eq_one_iff`. -/
theorem norm_Lhat_le (h0 : (0 : ℕ) ∈ D) {d : ℕ} (hd : d ∈ D) (θ : ℝ) :
    ‖Lhat D θ‖ ≤ 1 - ‖1 - expc (d * θ)‖ ^ 2 / (4 * D.card) := by
  classical
  have hD : D.Nonempty := ⟨0, h0⟩
  have hc : (0 : ℝ) < D.card := by exact_mod_cast Finset.card_pos.2 hD
  rcases eq_or_ne d 0 with rfl | hd0
  · simpa using norm_Lhat_le_one hD θ
  · set z : ℂ := expc ((d : ℝ) * θ) with hzdef
    have hz : ‖z‖ = 1 := norm_expc _
    have hznorm : z.re * z.re + z.im * z.im = 1 := by
      have := Complex.sq_norm z
      rw [hz, Complex.normSq_apply] at this
      linarith [this]
    have hw2 : ‖1 - z‖ ≤ 2 := by
      calc ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
        _ = 2 := by rw [hz]; norm_num
    have hpar : ‖1 + z‖ ^ 2 + ‖1 - z‖ ^ 2 = 4 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im]
      nlinarith [hznorm]
    have key : ‖1 + z‖ ≤ 2 - ‖1 - z‖ ^ 2 / 4 := by
      nlinarith [norm_nonneg (1 + z), norm_nonneg (1 - z), hpar, hw2,
        sq_nonneg (‖1 - z‖ ^ 2)]
    have hsub : ({0, d} : Finset ℕ) ⊆ D := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hsplit : ∑ e ∈ D, expc ((e : ℝ) * θ)
        = (∑ e ∈ D \ ({0, d} : Finset ℕ), expc ((e : ℝ) * θ)) + (1 + z) := by
      rw [← Finset.sum_sdiff hsub]
      congr 1
      rw [Finset.sum_pair (Ne.symm hd0)]
      simp [hzdef]
    have hcard : ((D \ ({0, d} : Finset ℕ)).card : ℝ) = (D.card : ℝ) - 2 := by
      have h2 : 2 ≤ D.card := by
        have := Finset.card_le_card hsub
        rwa [Finset.card_pair (Ne.symm hd0)] at this
      rw [Finset.card_sdiff_of_subset hsub, Finset.card_pair (Ne.symm hd0)]
      push_cast [Nat.cast_sub h2]
      ring
    have hrest : ‖∑ e ∈ D \ ({0, d} : Finset ℕ), expc ((e : ℝ) * θ)‖ ≤ (D.card : ℝ) - 2 := by
      calc ‖∑ e ∈ D \ ({0, d} : Finset ℕ), expc ((e : ℝ) * θ)‖
          ≤ ∑ e ∈ D \ ({0, d} : Finset ℕ), ‖expc ((e : ℝ) * θ)‖ := norm_sum_le _ _
        _ = ((D \ ({0, d} : Finset ℕ)).card : ℝ) := by simp
        _ = (D.card : ℝ) - 2 := hcard
    have hsum : ‖∑ e ∈ D, expc ((e : ℝ) * θ)‖ ≤ (D.card : ℝ) - ‖1 - z‖ ^ 2 / 4 := by
      rw [hsplit]
      calc ‖(∑ e ∈ D \ ({0, d} : Finset ℕ), expc ((e : ℝ) * θ)) + (1 + z)‖
          ≤ ‖∑ e ∈ D \ ({0, d} : Finset ℕ), expc ((e : ℝ) * θ)‖ + ‖1 + z‖ := norm_add_le _ _
        _ ≤ ((D.card : ℝ) - 2) + (2 - ‖1 - z‖ ^ 2 / 4) := add_le_add hrest key
        _ = (D.card : ℝ) - ‖1 - z‖ ^ 2 / 4 := by ring
    rw [Lhat, norm_mul, norm_inv, Complex.norm_natCast]
    rw [inv_mul_eq_div, div_le_iff₀ hc]
    have : (1 - ‖1 - z‖ ^ 2 / (4 * (D.card : ℝ))) * (D.card : ℝ)
        = (D.card : ℝ) - ‖1 - z‖ ^ 2 / 4 := by
      field_simp
    rw [this]
    exact hsum

theorem Lhat_eq_one (hD : D.Nonempty) {θ : ℝ} (h : ∃ k : ℤ, (stepSize D : ℝ) * θ = k) :
    Lhat D θ = 1 := by
  obtain ⟨k, hk⟩ := h
  have hone : ∀ d ∈ D, expc ((d : ℝ) * θ) = 1 := by
    intro d hd
    obtain ⟨m, rfl⟩ : stepSize D ∣ d := Finset.gcd_dvd hd
    rw [expc_eq_one_iff]
    refine ⟨m * k, ?_⟩
    have he : ((stepSize D * m : ℕ) : ℝ) * θ = (m : ℝ) * ((stepSize D : ℝ) * θ) := by
      push_cast; ring
    rw [he, hk]
    push_cast; ring
  have hcne : D.card ≠ 0 := by have := Finset.card_pos.2 hD; omega
  have hc : (D.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hcne
  rw [Lhat, Finset.sum_congr rfl hone]
  simp [hc]

/-- Blueprint: `lem:Lhat-abs-one`. -/
theorem abs_Lhat_eq_one_iff (h0 : (0 : ℕ) ∈ D) (θ : ℝ) :
    ‖Lhat D θ‖ = 1 ↔ ∃ k : ℤ, (stepSize D : ℝ) * θ = k := by
  have hD : D.Nonempty := ⟨0, h0⟩
  have hc : (0 : ℝ) < D.card := by exact_mod_cast Finset.card_pos.2 hD
  constructor
  · intro h1
    have hone : ∀ d ∈ D, ∃ k : ℤ, (d : ℝ) * θ = k := by
      intro d hd
      have hle := norm_Lhat_le h0 hd θ
      rw [h1] at hle
      have hpos : (0 : ℝ) < 4 * (D.card : ℝ) := by linarith
      have hz2 : ‖1 - expc ((d : ℝ) * θ)‖ ^ 2 ≤ 0 := by
        by_contra hcon
        have hcon' : 0 < ‖1 - expc ((d : ℝ) * θ)‖ ^ 2 := lt_of_not_ge hcon
        have : 0 < ‖1 - expc ((d : ℝ) * θ)‖ ^ 2 / (4 * (D.card : ℝ)) := by positivity
        linarith
      have hz0 : ‖1 - expc ((d : ℝ) * θ)‖ = 0 := by
        nlinarith [norm_nonneg (1 - expc ((d : ℝ) * θ))]
      rw [norm_eq_zero, sub_eq_zero] at hz0
      exact expc_eq_one_iff.1 hz0.symm
    choose! kk hkk using hone
    obtain ⟨f, hf⟩ := exists_gcd_eq_sum D
    refine ⟨∑ d ∈ D, f d * kk d, ?_⟩
    have hstep : (stepSize D : ℝ) = ∑ d ∈ D, (f d : ℝ) * (d : ℝ) := by
      have := congrArg (fun z : ℤ => (z : ℝ)) hf
      push_cast at this
      exact this
    calc (stepSize D : ℝ) * θ = (∑ d ∈ D, (f d : ℝ) * (d : ℝ)) * θ := by rw [hstep]
      _ = ∑ d ∈ D, (f d : ℝ) * ((d : ℝ) * θ) := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun d _ => by ring
      _ = ∑ d ∈ D, (f d : ℝ) * (kk d : ℝ) := by
          exact Finset.sum_congr rfl fun d hd => by rw [hkk d hd]
      _ = ((∑ d ∈ D, f d * kk d : ℤ) : ℝ) := by push_cast; ring
  · intro h
    rw [Lhat_eq_one hD h]
    simp

/-! ### The exponential sum over the Cantor set -/

/-- `Φ(n) = e(κ(n) α + s_b(κ(n)) β)`, the summand of Lemma 4.7. -/
noncomputable def expPhi (b : ℕ) (D : Finset ℕ) (α β : ℝ) (n : ℕ) : ℂ :=
  expc (enum b D n * α + sumDigits b (enum b D n) * β)

/-- `Ψ_i(m) = e(b^i κ(m) α + s_b(κ(m)) β)`, the summand of the outer sum in
`window_split`.  `Ψ_0 = Φ`. -/
noncomputable def expPsi (b : ℕ) (D : Finset ℕ) (α β : ℝ) (i m : ℕ) : ℂ :=
  expc ((b : ℝ) ^ i * enum b D m * α + sumDigits b (enum b D m) * β)

@[simp] theorem norm_expPhi (α β : ℝ) (n : ℕ) : ‖expPhi b D α β n‖ = 1 := by
  rw [expPhi, norm_expc]

@[simp] theorem norm_expPsi (α β : ℝ) (i n : ℕ) : ‖expPsi b D α β i n‖ = 1 := by
  rw [expPsi, norm_expc]

theorem expPsi_zero (α β : ℝ) (n : ℕ) : expPsi b D α β 0 n = expPhi b D α β n := by
  rw [expPsi, expPhi]
  norm_num

/-! ### Reindexing helpers -/

theorem sum_range_mul {M : Type*} [AddCommMonoid M] (A B : ℕ) (f : ℕ → M) :
    ∑ n ∈ range (A * B), f n = ∑ m ∈ range A, ∑ j ∈ range B, f (B * m + j) := by
  induction A with
  | zero => simp
  | succ k ih =>
    have hAB : (k + 1) * B = k * B + B := by ring
    rw [hAB, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by congr 1; ring

theorem sum_Ico_mul {M : Type*} [AddCommMonoid M] (B : ℕ) (f : ℕ → M) {Mi Ni : ℕ}
    (h : Mi ≤ Ni) :
    ∑ n ∈ Ico (B * Mi) (B * Ni), f n
      = ∑ m ∈ Ico Mi Ni, ∑ j ∈ range B, f (B * m + j) := by
  induction Ni, h using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have h1 : B * Mi ≤ B * n := Nat.mul_le_mul_left B hn
    have h2 : B * n ≤ B * (n + 1) := Nat.mul_le_mul_left B (by omega)
    rw [← Finset.sum_Ico_consecutive f h1 h2, ih, Finset.sum_Ico_succ_top hn]
    congr 1
    have hBn : B * (n + 1) = B * n + B := by ring
    rw [hBn, Finset.sum_Ico_eq_sum_range]
    simp

/-- The sorted enumeration `digitOf D` is a bijection `[0, δ) → D`. -/
theorem sum_range_card_digitOf {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∑ j ∈ range D.card, g (digitOf D j) = ∑ d ∈ D, g d := by
  refine Finset.sum_nbij (i := fun j => digitOf D j) ?_ ?_ ?_ ?_
  · intro j hj
    exact digitOf_mem (Finset.mem_range.1 hj)
  · intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases Nat.lt_or_ge i j with hlt | hge
    · exact absurd hij (ne_of_lt (digitOf_lt hlt hj))
    · have hlt : j < i := by omega
      exact absurd hij.symm (ne_of_lt (digitOf_lt hlt hi))
  · intro d hd
    obtain ⟨c, hc, hcd⟩ := exists_digitOf_eq (by simpa using hd)
    exact ⟨c, by simpa using hc, hcd⟩
  · intro j _
    rfl

/-! ### The block product -/

/-- Peeling off the least significant base `|D|` digit. -/
theorem expPhi_mul_add (h : Standing b D) (α β : ℝ) (m : ℕ) {j : ℕ} (hj : j < D.card) :
    expPhi b D α β (D.card * m + j)
      = expPhi b D ((b : ℝ) * α) β m * expc ((digitOf D j : ℝ) * (α + β)) := by
  have hb : 1 < b := by have := h.three_le_base; omega
  have he := enum_mul_add h m hj
  have hdb : digitOf D j < b := h.lt_base _ (digitOf_mem hj)
  have hs : sumDigits b (enum b D (D.card * m + j))
      = sumDigits b (enum b D m) + digitOf D j := by
    rw [he]; exact sumDigits_mul_add hb _ hdb
  rw [expPhi, expPhi, hs, he, ← expc_add]
  congr 1
  push_cast
  ring

/-- Blueprint: `lem:blockProduct`. -/
theorem blockProduct (h : Standing b D) (α β : ℝ) (l : ℕ) :
    ((D.card : ℂ) ^ l)⁻¹ * ∑ j ∈ range (D.card ^ l), expPhi b D α β j
      = ∏ c ∈ range l, Lhat D ((b : ℝ) ^ c * α + β) := by
  have hcard : 0 < D.card := by have := h.two_le_card; omega
  have hcne : (D.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  induction l generalizing α with
  | zero => simp [expPhi, sumDigits]
  | succ l ih =>
    have hpow : D.card ^ (l + 1) = D.card ^ l * D.card := by ring
    have hinner : ∀ m : ℕ, ∑ j ∈ range D.card, expPhi b D α β (D.card * m + j)
        = expPhi b D ((b : ℝ) * α) β m * ((D.card : ℂ) * Lhat D (α + β)) := by
      intro m
      rw [Finset.sum_congr rfl (fun j hj =>
        expPhi_mul_add h α β m (Finset.mem_range.1 hj)), ← Finset.mul_sum]
      congr 1
      rw [sum_range_card_digitOf (D := D) (fun d => expc ((d : ℝ) * (α + β))), Lhat]
      field_simp
      exact Finset.sum_congr rfl fun x _ => by rw [mul_comm]
    rw [hpow, sum_range_mul, Finset.sum_congr rfl (fun m _ => hinner m), ← Finset.sum_mul,
      Finset.prod_range_succ']
    have hbα : ∀ c : ℕ, (b : ℝ) ^ (c + 1) * α + β = (b : ℝ) ^ c * ((b : ℝ) * α) + β := by
      intro c; ring
    rw [Finset.prod_congr rfl (fun c _ => by rw [hbα c])]
    rw [← ih ((b : ℝ) * α)]
    field_simp
    ring

/-- The un-normalised form of `blockProduct`. -/
theorem sum_range_pow_eq (h : Standing b D) (α β : ℝ) (l : ℕ) :
    ∑ j ∈ range (D.card ^ l), expPhi b D α β j
      = (D.card : ℂ) ^ l * ∏ c ∈ range l, Lhat D ((b : ℝ) ^ c * α + β) := by
  have hcard : 0 < D.card := by have := h.two_le_card; omega
  have hcne : ((D.card : ℂ) ^ l) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  rw [← blockProduct h α β l]
  field_simp

/-! ### Window splitting -/

/-- `enum_block` with the (unnecessary) hypothesis `1 ≤ i` removed. -/
theorem enum_block' (h : Standing b D) (i m : ℕ) {j : ℕ} (hj : j < D.card ^ i) :
    enum b D (D.card ^ i * m + j) = b ^ i * enum b D m + enum b D j := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp only [pow_zero, Nat.lt_one_iff] at hj
    simp [hj]
  · exact enum_block h i m j hi hj

/-- `sumDigits_enum_block` with the hypothesis `1 ≤ i` removed. -/
theorem sumDigits_enum_block' (h : Standing b D) (i m : ℕ) {j : ℕ} (hj : j < D.card ^ i) :
    sumDigits b (enum b D (D.card ^ i * m + j))
      = sumDigits b (enum b D m) + sumDigits b (enum b D j) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp only [pow_zero, Nat.lt_one_iff] at hj
    simp [hj, sumDigits]
  · exact sumDigits_enum_block h i m j hi hj

/-- A single complete block of length `δ^i` contributes `Ψ_i(m) · δ^i P_i`. -/
theorem sum_block (h : Standing b D) (α β : ℝ) (i m : ℕ) :
    ∑ j ∈ range (D.card ^ i), expPhi b D α β (D.card ^ i * m + j)
      = expPsi b D α β i m
        * ((D.card : ℂ) ^ i * ∏ c ∈ range i, Lhat D ((b : ℝ) ^ c * α + β)) := by
  have key : ∀ j ∈ range (D.card ^ i),
      expPhi b D α β (D.card ^ i * m + j) = expPsi b D α β i m * expPhi b D α β j := by
    intro j hj
    have hj' : j < D.card ^ i := Finset.mem_range.1 hj
    rw [expPhi, expPhi, expPsi, ← expc_add, sumDigits_enum_block' h i m hj',
      enum_block' h i m hj']
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, sum_range_pow_eq h]

/-- `⌈M/q⌉ = (M + q - 1)/q` brackets `M`. -/
theorem ceil_div_bounds {q M : ℕ} (hq : 0 < q) :
    M ≤ q * ((M + q - 1) / q) ∧ q * ((M + q - 1) / q) < M + q := by
  have hdm := Nat.div_add_mod (M + q - 1) q
  have hmod : (M + q - 1) % q < q := Nat.mod_lt _ hq
  obtain ⟨X, hX⟩ : ∃ X, q * ((M + q - 1) / q) = X := ⟨_, rfl⟩
  rw [hX] at hdm ⊢
  omega

theorem floor_div_bounds {q N : ℕ} (hq : 0 < q) :
    q * (N / q) ≤ N ∧ N < q * (N / q) + q := by
  have hdm := Nat.div_add_mod N q
  have hmod : N % q < q := Nat.mod_lt _ hq
  obtain ⟨X, hX⟩ : ∃ X, q * (N / q) = X := ⟨_, rfl⟩
  rw [hX] at hdm ⊢
  omega

/-- Blueprint: `lem:windowSplit`.  The incomplete-block estimate: up to an
error of at most `2δ^i`, the window sum factors as `δ^i P_i` times the sum of
`Ψ_i` over the complete blocks `⌈M/δ^i⌉ ≤ m < ⌊N/δ^i⌋`. -/
theorem window_split (h : Standing b D) (α β : ℝ) (i M N : ℕ) :
    ‖(∑ n ∈ Ico M N, expPhi b D α β n)
        - ((D.card : ℂ) ^ i * ∏ c ∈ range i, Lhat D ((b : ℝ) ^ c * α + β))
          * ∑ m ∈ Ico ((M + D.card ^ i - 1) / D.card ^ i) (N / D.card ^ i),
              expPsi b D α β i m‖
      ≤ 2 * (D.card : ℝ) ^ i := by
  have hcard : 0 < D.card := by have := h.two_le_card; omega
  set P : ℂ := (D.card : ℂ) ^ i * ∏ c ∈ range i, Lhat D ((b : ℝ) ^ c * α + β) with hPdef
  have hblk : ∀ m, ∑ j ∈ range (D.card ^ i), expPhi b D α β (D.card ^ i * m + j)
      = expPsi b D α β i m * P := sum_block h α β i
  obtain ⟨q, hqdef⟩ : ∃ q, D.card ^ i = q := ⟨_, rfl⟩
  have hq : 0 < q := by rw [← hqdef]; exact pow_pos hcard i
  have hqcast : ((D.card : ℝ)) ^ i = (q : ℝ) := by rw [← hqdef]; push_cast; ring
  rw [hqdef] at hblk ⊢
  rw [hqcast]
  obtain ⟨hA, hB⟩ := ceil_div_bounds (q := q) (M := M) hq
  obtain ⟨hC, hDD⟩ := floor_div_bounds (q := q) (N := N) hq
  obtain ⟨Mi, hMi⟩ : ∃ k, (M + q - 1) / q = k := ⟨_, rfl⟩
  obtain ⟨Ni, hNi⟩ : ∃ k, N / q = k := ⟨_, rfl⟩
  rw [hMi] at hA hB ⊢
  rw [hNi] at hC hDD ⊢
  -- bound an incomplete stretch of fewer than `q` terms
  have hinc : ∀ x y : ℕ, y - x ≤ q → ‖∑ n ∈ Ico x y, expPhi b D α β n‖ ≤ (q : ℝ) := by
    intro x y hxy
    calc ‖∑ n ∈ Ico x y, expPhi b D α β n‖
        ≤ ∑ n ∈ Ico x y, ‖expPhi b D α β n‖ := norm_sum_le _ _
      _ = ((y - x : ℕ) : ℝ) := by simp
      _ ≤ (q : ℝ) := by exact_mod_cast hxy
  rcases le_or_gt Mi Ni with hle | hgt
  · have h1 : q * Mi ≤ q * Ni := Nat.mul_le_mul_left q hle
    have hmid : ∑ n ∈ Ico (q * Mi) (q * Ni), expPhi b D α β n
        = P * ∑ m ∈ Ico Mi Ni, expPsi b D α β i m := by
      rw [sum_Ico_mul q _ hle, Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by rw [hblk m]; ring
    have e2 : (∑ n ∈ Ico (q * Mi) (q * Ni), expPhi b D α β n)
        + (∑ n ∈ Ico (q * Ni) N, expPhi b D α β n)
        = ∑ n ∈ Ico (q * Mi) N, expPhi b D α β n :=
      Finset.sum_Ico_consecutive _ h1 hC
    have e1 : (∑ n ∈ Ico M (q * Mi), expPhi b D α β n)
        + (∑ n ∈ Ico (q * Mi) N, expPhi b D α β n)
        = ∑ n ∈ Ico M N, expPhi b D α β n :=
      Finset.sum_Ico_consecutive _ hA (le_trans h1 hC)
    have hdiff : (∑ n ∈ Ico M N, expPhi b D α β n)
        - P * ∑ m ∈ Ico Mi Ni, expPsi b D α β i m
        = (∑ n ∈ Ico M (q * Mi), expPhi b D α β n)
          + (∑ n ∈ Ico (q * Ni) N, expPhi b D α β n) := by
      rw [← e1, ← e2, ← hmid]; ring
    rw [hdiff]
    calc ‖(∑ n ∈ Ico M (q * Mi), expPhi b D α β n)
            + (∑ n ∈ Ico (q * Ni) N, expPhi b D α β n)‖
        ≤ ‖∑ n ∈ Ico M (q * Mi), expPhi b D α β n‖
            + ‖∑ n ∈ Ico (q * Ni) N, expPhi b D α β n‖ := norm_add_le _ _
      _ ≤ (q : ℝ) + (q : ℝ) := add_le_add (hinc _ _ (by omega)) (hinc _ _ (by omega))
      _ = 2 * (q : ℝ) := by ring
  · have hempty : Ico Mi Ni = (∅ : Finset ℕ) := Finset.Ico_eq_empty (by omega)
    have hstep : q * Ni + q ≤ q * Mi := by
      have hm := Nat.mul_le_mul_left q (show Ni + 1 ≤ Mi by omega)
      calc q * Ni + q = q * (Ni + 1) := by ring
        _ ≤ q * Mi := hm
    have hNM : N - M ≤ q := by
      obtain ⟨X, hX⟩ : ∃ X, q * Mi = X := ⟨_, rfl⟩
      obtain ⟨Y, hY⟩ : ∃ Y, q * Ni = Y := ⟨_, rfl⟩
      rw [hX] at hB hstep
      rw [hY] at hC hDD hstep
      omega
    rw [hempty]
    simp only [Finset.sum_empty, mul_zero, sub_zero]
    calc ‖∑ n ∈ Ico M N, expPhi b D α β n‖ ≤ (q : ℝ) := hinc _ _ hNM
      _ ≤ 2 * (q : ℝ) := by
          have : (0:ℝ) ≤ (q:ℝ) := by positivity
          linarith

/-! ### Exceptional pairs -/

/-- Blueprint: `def:exceptional`.  `(α, β)` is exceptional when there are
integers `a`, `r` and `t ≥ 0` with `sα ≡ a/(b-1) + r/b^t` and
`sβ ≡ -a/(b-1) (mod 1)`, where `s = s(D)`. -/
def Exceptional (b : ℕ) (D : Finset ℕ) (α β : ℝ) : Prop :=
  ∃ (a r : ℤ) (t : ℕ),
    (∃ k : ℤ, (stepSize D : ℝ) * α = (a : ℝ) / ((b : ℝ) - 1) + (r : ℝ) / (b : ℝ) ^ t + k) ∧
    (∃ k : ℤ, (stepSize D : ℝ) * β = -((a : ℝ) / ((b : ℝ) - 1)) + k)

/-- The arithmetic core of `exceptional_of_tendsto`, with no reference to `D`. -/
theorem escape_core (hb : 3 ≤ b) {x y : ℝ}
    (hlim : Tendsto (fun c : ℕ => distInt ((b : ℝ) ^ c * x + y)) atTop (nhds 0)) :
    ∃ (a r : ℤ) (t : ℕ),
      (∃ k : ℤ, x = (a : ℝ) / ((b : ℝ) - 1) + (r : ℝ) / (b : ℝ) ^ t + k) ∧
      (∃ k : ℤ, y = -((a : ℝ) / ((b : ℝ) - 1)) + k) ∧
      (∀ c, t ≤ c → ∃ k : ℤ, (b : ℝ) ^ c * x + y = k) := by
  have hb3 : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < (b : ℝ) := by linarith
  have hb1 : ((b : ℝ) - 1) ≠ 0 := by linarith
  have hbne : ((b : ℝ)) ≠ 0 := by linarith
  -- the difference sequence `b^c (b-1) x` also has `‖·‖ → 0`
  have hcomb : Tendsto
      (fun c : ℕ => distInt ((b : ℝ) ^ (c + 1) * x + y) + distInt ((b : ℝ) ^ c * x + y))
      atTop (nhds 0) := by
    have h1 : Tendsto (fun c : ℕ => distInt ((b : ℝ) ^ (c + 1) * x + y)) atTop (nhds 0) :=
      hlim.comp (tendsto_add_atTop_nat 1)
    simpa using h1.add hlim
  have hu : Tendsto (fun c : ℕ => distInt ((b : ℝ) ^ c * (((b : ℝ) - 1) * x)))
      atTop (nhds 0) := by
    refine squeeze_zero (fun c => distInt_nonneg _) (fun c => ?_) hcomb
    have he : (b : ℝ) ^ c * (((b : ℝ) - 1) * x)
        = ((b : ℝ) ^ (c + 1) * x + y) + (-((b : ℝ) ^ c * x + y)) := by ring
    rw [he]
    calc distInt (((b : ℝ) ^ (c + 1) * x + y) + (-((b : ℝ) ^ c * x + y)))
        ≤ distInt ((b : ℝ) ^ (c + 1) * x + y) + distInt (-((b : ℝ) ^ c * x + y)) :=
          distInt_add_le _ _
      _ = _ := by rw [distInt_neg]
  -- choose `c₀` beyond which the distance is below `1/(2b)`
  have hsmall : (0 : ℝ) < 1 / (2 * (b : ℝ)) := by positivity
  obtain ⟨t, ht⟩ := (eventually_atTop.1 (hu.eventually (gt_mem_nhds hsmall)))
  set v : ℝ := (b : ℝ) ^ t * (((b : ℝ) - 1) * x) with hvdef
  -- the amplification: `‖b^n v‖ = b^n ‖v‖`
  have hamp : ∀ n : ℕ, distInt ((b : ℝ) ^ n * v) = (b : ℝ) ^ n * distInt v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hvn : (b : ℝ) ^ n * v = (b : ℝ) ^ (t + n) * (((b : ℝ) - 1) * x) := by
        rw [hvdef, pow_add]; ring
      have hlt : distInt ((b : ℝ) ^ n * v) < 1 / (2 * (b : ℝ)) := by
        rw [hvn]; exact ht (t + n) (Nat.le_add_right _ _)
      have hbn : ((b : ℕ) : ℝ) * distInt ((b : ℝ) ^ n * v) < 1 / 2 := by
        rw [ih] at hlt ⊢
        calc (b : ℝ) * ((b : ℝ) ^ n * distInt v)
            < (b : ℝ) * (1 / (2 * (b : ℝ))) := by
              exact mul_lt_mul_of_pos_left hlt hbpos
          _ = 1 / 2 := by field_simp
      have hstep := distInt_nat_mul (n := b) (x := (b : ℝ) ^ n * v) hbn
      have he2 : (b : ℝ) ^ (n + 1) * v = ((b : ℕ) : ℝ) * ((b : ℝ) ^ n * v) := by
        rw [pow_succ]; ring
      rw [he2, hstep, ih, pow_succ]
      ring
  -- hence `‖v‖ = 0`
  have hw0 : distInt v = 0 := by
    by_contra hw
    have hwpos : 0 < distInt v := lt_of_le_of_ne (distInt_nonneg v) (Ne.symm hw)
    have hgo : Tendsto (fun n : ℕ => (b : ℝ) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by linarith)
    obtain ⟨n, hn⟩ := (hgo.eventually_gt_atTop ((1 / (2 * (b : ℝ))) / distInt v)).exists
    have h1 : 1 / (2 * (b : ℝ)) < (b : ℝ) ^ n * distInt v := by
      rw [div_lt_iff₀ hwpos] at hn
      linarith
    have h2 : distInt ((b : ℝ) ^ n * v) < 1 / (2 * (b : ℝ)) := by
      have hvn : (b : ℝ) ^ n * v = (b : ℝ) ^ (t + n) * (((b : ℝ) - 1) * x) := by
        rw [hvdef, pow_add]; ring
      rw [hvn]; exact ht (t + n) (Nat.le_add_right _ _)
    rw [hamp n] at h2
    linarith
  obtain ⟨K, hK⟩ := distInt_eq_zero_iff.1 hw0
  -- partial fractions
  have hco : IsCoprime ((b : ℤ) - 1) ((b : ℤ)) := ⟨-1, 1, by ring⟩
  obtain ⟨u₀, v₀, huv⟩ := hco.pow_right (n := t)
  refine ⟨K * v₀, K * u₀, t, ⟨0, ?_⟩, ?_⟩
  · have hKx : ((b : ℝ) - 1) * (b : ℝ) ^ t * x = (K : ℝ) := by
      rw [← hK, hvdef]; ring
    have huvR : (u₀ : ℝ) * ((b : ℝ) - 1) + (v₀ : ℝ) * (b : ℝ) ^ t = 1 := by
      have := congrArg (fun z : ℤ => (z : ℝ)) huv
      push_cast at this
      exact this
    have hbt : ((b : ℝ)) ^ t ≠ 0 := pow_ne_zero _ hbne
    push_cast
    field_simp
    linear_combination hKx - (K : ℝ) * huvR
  · -- `y` and the integrality for `c ≥ t`
    have hx : x = ((K * v₀ : ℤ) : ℝ) / ((b : ℝ) - 1) + ((K * u₀ : ℤ) : ℝ) / (b : ℝ) ^ t := by
      have hKx : ((b : ℝ) - 1) * (b : ℝ) ^ t * x = (K : ℝ) := by
        rw [← hK, hvdef]; ring
      have huvR : (u₀ : ℝ) * ((b : ℝ) - 1) + (v₀ : ℝ) * (b : ℝ) ^ t = 1 := by
        have := congrArg (fun z : ℤ => (z : ℝ)) huv
        push_cast at this
        exact this
      have hbt : ((b : ℝ)) ^ t ≠ 0 := pow_ne_zero _ hbne
      push_cast
      field_simp
      linear_combination hKx - (K : ℝ) * huvR
    set a : ℤ := K * v₀ with hadef
    set r : ℤ := K * u₀ with hrdef
    -- for `c ≥ t`, `b^c x - a/(b-1)` is an integer
    have hkey : ∀ c, t ≤ c → ∃ k : ℤ,
        (b : ℝ) ^ c * x = (a : ℝ) / ((b : ℝ) - 1) + (k : ℝ) := by
      intro c hc
      refine ⟨a * (∑ j ∈ range c, (b : ℤ) ^ j) + r * (b : ℤ) ^ (c - t), ?_⟩
      have hgeom : ((b : ℝ)) ^ c - 1 = ((b : ℝ) - 1) * (∑ j ∈ range c, (b : ℝ) ^ j) := by
        rw [mul_comm]
        exact (geom_sum_mul (b : ℝ) c).symm
      have hsplit : ((b : ℝ)) ^ c = (b : ℝ) ^ t * (b : ℝ) ^ (c - t) := by
        rw [← pow_add]
        congr 1
        omega
      have hbt : ((b : ℝ)) ^ t ≠ 0 := pow_ne_zero _ hbne
      rw [hx]
      push_cast
      field_simp
      linear_combination (a : ℝ) * (b : ℝ) ^ t * hgeom + (r : ℝ) * ((b : ℝ) - 1) * hsplit
    -- the distance is eventually constant, hence zero
    have hconst : ∀ c, t ≤ c →
        distInt ((b : ℝ) ^ c * x + y) = distInt ((a : ℝ) / ((b : ℝ) - 1) + y) := by
      intro c hc
      obtain ⟨k, hk⟩ := hkey c hc
      have : (b : ℝ) ^ c * x + y = ((a : ℝ) / ((b : ℝ) - 1) + y) + (k : ℝ) := by
        rw [hk]; ring
      rw [this, distInt_add_int]
    have hzero : distInt ((a : ℝ) / ((b : ℝ) - 1) + y) = 0 := by
      have hc1 : Tendsto (fun _ : ℕ => distInt ((a : ℝ) / ((b : ℝ) - 1) + y)) atTop
          (nhds (distInt ((a : ℝ) / ((b : ℝ) - 1) + y))) := tendsto_const_nhds
      have hc2 : Tendsto (fun _ : ℕ => distInt ((a : ℝ) / ((b : ℝ) - 1) + y)) atTop
          (nhds 0) := by
        refine hlim.congr' ?_
        filter_upwards [eventually_ge_atTop t] with c hc
        exact hconst c hc
      exact tendsto_nhds_unique hc1 hc2
    obtain ⟨k₀, hk₀⟩ := distInt_eq_zero_iff.1 hzero
    refine ⟨⟨k₀, by linarith [hk₀]⟩, ?_⟩
    intro c hc
    obtain ⟨k, hk⟩ := hkey c hc
    refine ⟨k + k₀, ?_⟩
    push_cast
    rw [hk]
    linarith [hk₀]

/-- Blueprint: `lem:escape`. -/
theorem exceptional_of_tendsto (hb : 3 ≤ b) {α β : ℝ}
    (hlim : Tendsto
      (fun c : ℕ => distInt ((stepSize D : ℝ) * ((b : ℝ) ^ c * α + β))) atTop (nhds 0)) :
    Exceptional b D α β ∧
      ∃ t : ℕ, ∀ c, t ≤ c → ∃ k : ℤ, (stepSize D : ℝ) * ((b : ℝ) ^ c * α + β) = k := by
  have hlim' : Tendsto
      (fun c : ℕ => distInt ((b : ℝ) ^ c * ((stepSize D : ℝ) * α) + (stepSize D : ℝ) * β))
      atTop (nhds 0) := by
    refine hlim.congr fun c => ?_
    congr 1
    ring
  obtain ⟨a, r, t, hx, hy, hint⟩ := escape_core (b := b) hb hlim'
  refine ⟨⟨a, r, t, hx, hy⟩, t, fun c hc => ?_⟩
  obtain ⟨k, hk⟩ := hint c hc
  exact ⟨k, by rw [← hk]; ring⟩

/-! ### The main theorem -/

/-- The number of complete blocks of length `q` inside `[M, N)` is at most
`(N-M)/q`. -/
theorem block_count_le {q M N : ℕ} (hq : 0 < q) :
    q * (N / q - (M + q - 1) / q) ≤ N - M := by
  obtain ⟨hA, hB⟩ := ceil_div_bounds (q := q) (M := M) hq
  obtain ⟨hC, hDD⟩ := floor_div_bounds (q := q) (N := N) hq
  obtain ⟨Mi, hMi⟩ : ∃ k, (M + q - 1) / q = k := ⟨_, rfl⟩
  obtain ⟨Ni, hNi⟩ : ∃ k, N / q = k := ⟨_, rfl⟩
  rw [hMi] at hA hB ⊢
  rw [hNi] at hC hDD ⊢
  rcases le_or_gt Mi Ni with hle | hgt
  · have hid : q * (Ni - Mi) + q * Mi = q * Ni := by
      rw [← Nat.mul_add]
      congr 1
      omega
    obtain ⟨X, hX⟩ : ∃ X, q * Mi = X := ⟨_, rfl⟩
    obtain ⟨Y, hY⟩ : ∃ Y, q * Ni = Y := ⟨_, rfl⟩
    obtain ⟨Z, hZ⟩ : ∃ Z, q * (Ni - Mi) = Z := ⟨_, rfl⟩
    rw [hX] at hA hB hid
    rw [hY] at hC hDD hid
    rw [hZ] at hid ⊢
    omega
  · have h0 : Ni - Mi = 0 := by omega
    rw [h0]
    simp

/-- The uniform window estimate: a small block product `P_i` bounds every
window average. -/
theorem norm_window_le (h : Standing b D) (α β : ℝ) (i : ℕ) {ε : ℝ}
    (hε : ‖∏ c ∈ range i, Lhat D ((b : ℝ) ^ c * α + β)‖ ≤ ε) (M N : ℕ) :
    ‖∑ n ∈ Ico M N, expPhi b D α β n‖
      ≤ ε * ((N - M : ℕ) : ℝ) + 2 * (D.card : ℝ) ^ i := by
  have hcard : 0 < D.card := by have := h.two_le_card; omega
  have hq : 0 < D.card ^ i := pow_pos hcard i
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) hε
  have hws := window_split h α β i M N
  have hT : ‖∑ m ∈ Ico ((M + D.card ^ i - 1) / D.card ^ i) (N / D.card ^ i),
      expPsi b D α β i m‖
      ≤ ((N / D.card ^ i - (M + D.card ^ i - 1) / D.card ^ i : ℕ) : ℝ) := by
    calc ‖∑ m ∈ Ico ((M + D.card ^ i - 1) / D.card ^ i) (N / D.card ^ i),
          expPsi b D α β i m‖
        ≤ ∑ m ∈ Ico ((M + D.card ^ i - 1) / D.card ^ i) (N / D.card ^ i),
            ‖expPsi b D α β i m‖ := norm_sum_le _ _
      _ = _ := by simp
  have hcount : (D.card : ℝ) ^ i
        * ((N / D.card ^ i - (M + D.card ^ i - 1) / D.card ^ i : ℕ) : ℝ)
      ≤ ((N - M : ℕ) : ℝ) := by
    have := block_count_le (q := D.card ^ i) (M := M) (N := N) hq
    have hc : ((D.card ^ i * (N / D.card ^ i - (M + D.card ^ i - 1) / D.card ^ i) : ℕ) : ℝ)
        ≤ ((N - M : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at hc
    exact hc
  have hPT : ‖((D.card : ℂ) ^ i * ∏ c ∈ range i, Lhat D ((b : ℝ) ^ c * α + β))
      * ∑ m ∈ Ico ((M + D.card ^ i - 1) / D.card ^ i) (N / D.card ^ i),
          expPsi b D α β i m‖ ≤ ε * ((N - M : ℕ) : ℝ) := by
    rw [norm_mul, norm_mul, Complex.norm_pow, Complex.norm_natCast]
    calc (D.card : ℝ) ^ i * ‖∏ c ∈ range i, Lhat D ((b : ℝ) ^ c * α + β)‖
          * ‖∑ m ∈ Ico ((M + D.card ^ i - 1) / D.card ^ i) (N / D.card ^ i),
              expPsi b D α β i m‖
        ≤ (D.card : ℝ) ^ i * ε
            * ((N / D.card ^ i - (M + D.card ^ i - 1) / D.card ^ i : ℕ) : ℝ) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hε (by positivity)) hT
            (norm_nonneg _) (by positivity)
      _ = ε * ((D.card : ℝ) ^ i
            * ((N / D.card ^ i - (M + D.card ^ i - 1) / D.card ^ i : ℕ) : ℝ)) := by ring
      _ ≤ ε * ((N - M : ℕ) : ℝ) := by
          exact mul_le_mul_of_nonneg_left hcount hε0
  calc ‖∑ n ∈ Ico M N, expPhi b D α β n‖
      = ‖((∑ n ∈ Ico M N, expPhi b D α β n)
            - ((D.card : ℂ) ^ i * ∏ c ∈ range i, Lhat D ((b : ℝ) ^ c * α + β))
              * ∑ m ∈ Ico ((M + D.card ^ i - 1) / D.card ^ i) (N / D.card ^ i),
                  expPsi b D α β i m)
          + (((D.card : ℂ) ^ i * ∏ c ∈ range i, Lhat D ((b : ℝ) ^ c * α + β))
              * ∑ m ∈ Ico ((M + D.card ^ i - 1) / D.card ^ i) (N / D.card ^ i),
                  expPsi b D α β i m)‖ := by ring_nf
    _ ≤ _ + _ := norm_add_le _ _
    _ ≤ 2 * (D.card : ℝ) ^ i + ε * ((N - M : ℕ) : ℝ) := add_le_add hws hPT
    _ = ε * ((N - M : ℕ) : ℝ) + 2 * (D.card : ℝ) ^ i := by ring

/-- If every `d ∈ D` has `d (b^c α + β) ∈ ℤ` for `c ≥ t`, then every element
of the Cantor set satisfies `b^c n α + s_b(n) β ∈ ℤ` for `c ≥ t`. -/
theorem exists_int_of_mem_cantorSet (h : Standing b D) {α β : ℝ} {t : ℕ}
    (hint : ∀ d ∈ D, ∀ c, t ≤ c → ∃ k : ℤ, (d : ℝ) * ((b : ℝ) ^ c * α + β) = k) :
    ∀ n ∈ cantorSet b D, ∀ c, t ≤ c →
      ∃ k : ℤ, (b : ℝ) ^ c * n * α + (sumDigits b n : ℝ) * β = k := by
  have hb : 1 < b := by have := h.three_le_base; omega
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn c hc
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · exact ⟨0, by simp [sumDigits]⟩
    · have hdig : Nat.digits b n = n % b :: Nat.digits b (n / b) := Nat.digits_def' hb hn0
      have hdmem : n % b ∈ D := hn _ (by rw [hdig]; exact List.mem_cons_self)
      have hmem : n / b ∈ cantorSet b D := fun d hd =>
        hn d (by rw [hdig]; exact List.mem_cons_of_mem _ hd)
      have hlt : n / b < n := Nat.div_lt_self hn0 hb
      obtain ⟨k1, hk1⟩ := ih _ hlt hmem (c + 1) (by omega)
      obtain ⟨k2, hk2⟩ := hint _ hdmem c hc
      refine ⟨k1 + k2, ?_⟩
      have hsd : sumDigits b n = n % b + sumDigits b (n / b) := by
        rw [sumDigits, hdig, List.sum_cons, sumDigits]
      have hn' : (n : ℝ) = (b : ℝ) * ((n / b : ℕ) : ℝ) + ((n % b : ℕ) : ℝ) := by
        have h0 := Nat.div_add_mod n b
        exact_mod_cast congrArg (fun m : ℕ => (m : ℝ)) h0.symm
      rw [hsd, hn']
      push_cast
      linear_combination hk1 + hk2

/-- Blueprint: `thm:irrational`, Lemma 4.7 of the paper.  The averages of `Φ`
over `[0, N)` converge; if `(α, β)` is not exceptional the limit is `0` and
the convergence is uniform over all windows `[M, N)` with `N - M` large. -/
theorem tendsto_expSum (h : Standing b D) (α β : ℝ) :
    ∃ L : ℂ,
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N, expPhi b D α β n) atTop (nhds L) ∧
      (¬ Exceptional b D α β →
        L = 0 ∧ ∀ ε > 0, ∃ K : ℕ, ∀ M N : ℕ, M + K ≤ N →
          ‖((N - M : ℕ) : ℂ)⁻¹ * ∑ n ∈ Ico M N, expPhi b D α β n‖ < ε) := by
  classical
  have hcard : 0 < D.card := by have := h.two_le_card; omega
  have hcardR : (0 : ℝ) < (D.card : ℝ) := by exact_mod_cast hcard
  have hDne : D.Nonempty := Finset.card_pos.1 hcard
  by_cases hsmallP : ∀ ε : ℝ, 0 < ε → ∃ i, ‖∏ c ∈ range i, Lhat D ((b : ℝ) ^ c * α + β)‖ < ε
  · -- the block products tend to `0`: the limit is `0`, uniformly over windows
    have huniform : ∀ ε > 0, ∃ K : ℕ, ∀ M N : ℕ, M + K ≤ N →
        ‖((N - M : ℕ) : ℂ)⁻¹ * ∑ n ∈ Ico M N, expPhi b D α β n‖ < ε := by
      intro ε hε
      obtain ⟨i, hi⟩ := hsmallP (ε / 2) (by linarith)
      obtain ⟨K0, hK0⟩ := exists_nat_gt (4 * (D.card : ℝ) ^ i / ε)
      refine ⟨K0 + 1, fun M N hMN => ?_⟩
      have hn : 0 < N - M := by omega
      have hnR : (0 : ℝ) < ((N - M : ℕ) : ℝ) := by exact_mod_cast hn
      have hbound := norm_window_le h α β i (le_of_lt hi) M N
      rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_eq_div, div_lt_iff₀ hnR]
      have hK0R : 4 * (D.card : ℝ) ^ i / ε < ((N - M : ℕ) : ℝ) := by
        have hle : (K0 : ℝ) ≤ ((N - M : ℕ) : ℝ) := by
          exact_mod_cast (by omega : K0 ≤ N - M)
        linarith
      rw [div_lt_iff₀ hε] at hK0R
      nlinarith [hbound, hK0R, hε, hnR]
    refine ⟨0, ?_, fun _ => ⟨rfl, huniform⟩⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨K, hK⟩ := huniform ε hε
    refine ⟨K, fun N hN => ?_⟩
    have hk := hK 0 N (by omega)
    rw [Nat.sub_zero] at hk
    rw [dist_eq_norm, sub_zero, Finset.range_eq_Ico]
    exact hk
  · -- the block products stay away from `0`
    push Not at hsmallP
    obtain ⟨ε₀, hε₀, hge⟩ := hsmallP
    set p : ℕ → ℝ := fun l => ‖∏ c ∈ range l, Lhat D ((b : ℝ) ^ c * α + β)‖ with hpdef
    have hpnn : ∀ l, 0 ≤ p l := fun l => norm_nonneg _
    have hpge : ∀ l, ε₀ ≤ p l := hge
    have hstep : ∀ l, p (l + 1) = p l * ‖Lhat D ((b : ℝ) ^ l * α + β)‖ := by
      intro l
      simp only [hpdef, Complex.norm_prod, Finset.prod_range_succ]
    have hanti : Antitone p := by
      refine antitone_nat_of_succ_le fun l => ?_
      rw [hstep l]
      nlinarith [norm_Lhat_le_one hDne ((b : ℝ) ^ l * α + β), hpnn l]
    have hbdd : BddBelow (Set.range p) := ⟨0, by rintro _ ⟨l, rfl⟩; exact hpnn l⟩
    have htend : Tendsto p atTop (nhds (⨅ l, p l)) := tendsto_atTop_ciInf hanti hbdd
    have hinfpos : 0 < ⨅ l, p l := lt_of_lt_of_le hε₀ (le_ciInf hpge)
    have htend1 : Tendsto (fun c => p (c + 1)) atTop (nhds (⨅ l, p l)) :=
      htend.comp (tendsto_add_atTop_nat 1)
    have hLto1 : Tendsto (fun c => ‖Lhat D ((b : ℝ) ^ c * α + β)‖) atTop (nhds 1) := by
      have hdiv := htend1.div htend (ne_of_gt hinfpos)
      rw [div_self (ne_of_gt hinfpos)] at hdiv
      refine hdiv.congr fun c => ?_
      have hpc : p c ≠ 0 := ne_of_gt (lt_of_lt_of_le hε₀ (hpge c))
      simp only [Pi.div_apply]
      rw [hstep c]
      field_simp
    -- every digit frequency approaches `ℤ`
    have hdig : ∀ d ∈ D, Tendsto (fun c : ℕ => distInt ((d : ℝ) * ((b : ℝ) ^ c * α + β)))
        atTop (nhds 0) := by
      intro d hd
      refine tendsto_zero_of_sq (fun c => distInt_nonneg _) ?_
      have hg : Tendsto
          (fun c : ℕ => (D.card : ℝ) * (1 - ‖Lhat D ((b : ℝ) ^ c * α + β)‖) / 4)
          atTop (nhds 0) := by
        have h1 : Tendsto
            (fun c : ℕ => (D.card : ℝ) * (1 - ‖Lhat D ((b : ℝ) ^ c * α + β)‖) / 4)
            atTop (nhds ((D.card : ℝ) * (1 - 1) / 4)) :=
          ((tendsto_const_nhds.sub hLto1).const_mul (D.card : ℝ)).div_const 4
        simpa using h1
      refine squeeze_zero (fun c => sq_nonneg _) (fun c => ?_) hg
      have h1 := norm_Lhat_le h.zero_mem hd ((b : ℝ) ^ c * α + β)
      have h2 := four_mul_distInt_le ((d : ℝ) * ((b : ℝ) ^ c * α + β))
      have h3 : (0 : ℝ) ≤ distInt ((d : ℝ) * ((b : ℝ) ^ c * α + β)) := distInt_nonneg _
      have h4 : (0 : ℝ) < 4 * (D.card : ℝ) := by linarith
      have hw2 : ‖1 - expc ((d : ℝ) * ((b : ℝ) ^ c * α + β))‖ ^ 2
          ≤ 4 * (D.card : ℝ) * (1 - ‖Lhat D ((b : ℝ) ^ c * α + β)‖) := by
        have hdiv : ‖1 - expc ((d : ℝ) * ((b : ℝ) ^ c * α + β))‖ ^ 2 / (4 * (D.card : ℝ))
            ≤ 1 - ‖Lhat D ((b : ℝ) ^ c * α + β)‖ := by linarith
        rw [div_le_iff₀ h4] at hdiv
        linarith
      nlinarith [h2, h3, hw2]
    -- Bézout transports this to the step size
    obtain ⟨f, hf⟩ := exists_gcd_eq_sum D
    have hstendsto : Tendsto
        (fun c : ℕ => distInt ((stepSize D : ℝ) * ((b : ℝ) ^ c * α + β))) atTop (nhds 0) := by
      have hgsum : Tendsto
          (fun c : ℕ => ∑ d ∈ D, |(f d : ℝ)| * distInt ((d : ℝ) * ((b : ℝ) ^ c * α + β)))
          atTop (nhds 0) := by
        have hzz : ∀ d ∈ D, Tendsto
            (fun c : ℕ => |(f d : ℝ)| * distInt ((d : ℝ) * ((b : ℝ) ^ c * α + β)))
            atTop (nhds 0) := by
          intro d hd
          have := (hdig d hd).const_mul (|(f d : ℝ)|)
          simpa using this
        have := tendsto_finsetSum D hzz
        simpa using this
      refine squeeze_zero (fun c => distInt_nonneg _) (fun c => ?_) hgsum
      have hstepeq : (stepSize D : ℝ) = ∑ d ∈ D, (f d : ℝ) * (d : ℝ) := by
        have := congrArg (fun z : ℤ => (z : ℝ)) hf
        push_cast at this
        exact this
      have hsum : (stepSize D : ℝ) * ((b : ℝ) ^ c * α + β)
          = ∑ d ∈ D, (f d : ℝ) * ((d : ℝ) * ((b : ℝ) ^ c * α + β)) := by
        rw [hstepeq, Finset.sum_mul]
        exact Finset.sum_congr rfl fun d _ => by ring
      rw [hsum]
      calc distInt (∑ d ∈ D, (f d : ℝ) * ((d : ℝ) * ((b : ℝ) ^ c * α + β)))
          ≤ ∑ d ∈ D, distInt ((f d : ℝ) * ((d : ℝ) * ((b : ℝ) ^ c * α + β))) :=
            distInt_sum_le _ _
        _ ≤ ∑ d ∈ D, |(f d : ℝ)| * distInt ((d : ℝ) * ((b : ℝ) ^ c * α + β)) :=
            Finset.sum_le_sum fun d _ => distInt_int_mul _ _
    obtain ⟨hexc, t, hint⟩ := exceptional_of_tendsto (D := D) h.three_le_base hstendsto
    refine ⟨∏ c ∈ range t, Lhat D ((b : ℝ) ^ c * α + β), ?_, fun hcon => absurd hexc hcon⟩
    -- from `c ≥ t` on every factor is `1`, and the inner averages are `1`
    have hintd : ∀ d ∈ D, ∀ c, t ≤ c → ∃ k : ℤ, (d : ℝ) * ((b : ℝ) ^ c * α + β) = k := by
      intro d hd c hc
      obtain ⟨m', hm'⟩ : stepSize D ∣ d := Finset.gcd_dvd hd
      obtain ⟨k, hk⟩ := hint c hc
      refine ⟨m' * k, ?_⟩
      have he : ((stepSize D * m' : ℕ) : ℝ) * ((b : ℝ) ^ c * α + β)
          = (m' : ℝ) * ((stepSize D : ℝ) * ((b : ℝ) ^ c * α + β)) := by push_cast; ring
      rw [hm', he, hk]
      push_cast
      ring
    have hPsi : ∀ m, expPsi b D α β t m = 1 := by
      intro m
      rw [expPsi, expc_eq_one_iff]
      exact exists_int_of_mem_cantorSet h hintd _ (enum_mem_cantorSet h m) t le_rfl
    have hPtnorm : ‖∏ c ∈ range t, Lhat D ((b : ℝ) ^ c * α + β)‖ ≤ 1 := by
      exact norm_prod_Lhat_le_one hDne (fun c => (b : ℝ) ^ c * α + β) t
    have hq : 0 < D.card ^ t := pow_pos hcard t
    have hws : ∀ N : ℕ, ‖(∑ n ∈ range N, expPhi b D α β n)
        - (N : ℂ) * ∏ c ∈ range t, Lhat D ((b : ℝ) ^ c * α + β)‖
        ≤ 3 * (D.card : ℝ) ^ t := by
      intro N
      have h0 := window_split h α β t 0 N
      have hMi : (0 + D.card ^ t - 1) / D.card ^ t = 0 := Nat.div_eq_of_lt (by omega)
      rw [hMi] at h0
      have hT : ∑ m ∈ Ico 0 (N / D.card ^ t), expPsi b D α β t m
          = ((N / D.card ^ t : ℕ) : ℂ) := by
        rw [Finset.sum_congr rfl (fun m _ => hPsi m)]
        simp
      rw [hT] at h0
      obtain ⟨hC, hDD⟩ := floor_div_bounds (q := D.card ^ t) (N := N) hq
      have hWcast : ((D.card : ℂ) ^ t) * ((N / D.card ^ t : ℕ) : ℂ)
          = ((D.card ^ t * (N / D.card ^ t) : ℕ) : ℂ) := by push_cast; ring
      have hgap : ‖((D.card ^ t * (N / D.card ^ t) : ℕ) : ℂ) - (N : ℂ)‖
          ≤ (D.card : ℝ) ^ t := by
        have hle : D.card ^ t * (N / D.card ^ t) ≤ N := hC
        have : ((D.card ^ t * (N / D.card ^ t) : ℕ) : ℂ) - (N : ℂ)
            = -(((N - D.card ^ t * (N / D.card ^ t) : ℕ) : ℂ)) := by
          have hcast : ((N - D.card ^ t * (N / D.card ^ t) : ℕ) : ℂ)
              = (N : ℂ) - ((D.card ^ t * (N / D.card ^ t) : ℕ) : ℂ) := by
            push_cast [Nat.cast_sub hle]
            ring
          rw [hcast]; ring
        rw [this, norm_neg, Complex.norm_natCast]
        have : N - D.card ^ t * (N / D.card ^ t) ≤ D.card ^ t := by omega
        calc ((N - D.card ^ t * (N / D.card ^ t) : ℕ) : ℝ) ≤ ((D.card ^ t : ℕ) : ℝ) := by
              exact_mod_cast this
          _ = (D.card : ℝ) ^ t := by push_cast; ring
      rw [Finset.range_eq_Ico]
      calc ‖(∑ n ∈ Ico 0 N, expPhi b D α β n)
              - (N : ℂ) * ∏ c ∈ range t, Lhat D ((b : ℝ) ^ c * α + β)‖
          = ‖((∑ n ∈ Ico 0 N, expPhi b D α β n)
                - ((D.card : ℂ) ^ t * ∏ c ∈ range t, Lhat D ((b : ℝ) ^ c * α + β))
                  * ((N / D.card ^ t : ℕ) : ℂ))
              + ((∏ c ∈ range t, Lhat D ((b : ℝ) ^ c * α + β))
                  * (((D.card ^ t * (N / D.card ^ t) : ℕ) : ℂ) - (N : ℂ)))‖ := by
            rw [← hWcast]; ring_nf
        _ ≤ _ + _ := norm_add_le _ _
        _ ≤ 2 * (D.card : ℝ) ^ t + 1 * (D.card : ℝ) ^ t := by
            refine add_le_add h0 ?_
            rw [norm_mul]
            exact mul_le_mul hPtnorm hgap (norm_nonneg _) (by norm_num)
        _ ≤ 3 * (D.card : ℝ) ^ t := by ring_nf; exact le_rfl
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_
      (tendsto_const_div_atTop_nhds_zero_nat (3 * (D.card : ℝ) ^ t))
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have hrw : (N : ℂ)⁻¹ * (∑ n ∈ range N, expPhi b D α β n)
        - ∏ c ∈ range t, Lhat D ((b : ℝ) ^ c * α + β)
        = (N : ℂ)⁻¹ * ((∑ n ∈ range N, expPhi b D α β n)
            - (N : ℂ) * ∏ c ∈ range t, Lhat D ((b : ℝ) ^ c * α + β)) := by
      rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hNC, one_mul]
    rw [hrw, norm_mul, norm_inv, Complex.norm_natCast]
    rw [inv_mul_eq_div, div_le_div_iff₀ hNR hNR]
    have := hws N
    nlinarith [this, hNR]

end IntegerCantorSet
