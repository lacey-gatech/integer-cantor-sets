/-
Signed digits and power savings.

Blueprint: `blueprint/src/content.tex`, Chapter 3, the section "Signed digits
and power savings"; §3.1 of the paper (Proposition 3.7).

In this file only, the digit set is allowed to contain negative integers, so
the Cantor set is a set of *integers*, `signedCantorSet b D : Set ℤ`.  The van
der Corput definitions of `VanDerCorput.lean` are applied, exactly as in the
paper, to the set of non-zero absolute values
`H = (natAbs '' signedCantorSet b D) \ {0} ⊆ ℕ`.  This needs no change to
`cosPoly`, `IsAdmissible` or `vdcConst`: a frequency enters only through
`cos (2π n x)`, and cosine is even, so the cosine polynomial genuinely sees
only `|n|`.

This file contains no `sorry`.
-/
import IntegerCantorSets.VanDerCorput

namespace IntegerCantorSet

open Finset

/-! ### The signed Cantor set -/

/-- The signed Cantor set: the integers `∑_{j < J} c_j b^j` whose digits `c_j`
all lie in `D`.  `D` is a finite set of (possibly negative) integers.

Blueprint: `def:signedCantorSet`. -/
def signedCantorSet (b : ℕ) (D : Finset ℤ) : Set ℤ :=
  {n | ∃ (J : ℕ) (c : ℕ → ℤ), (∀ j < J, c j ∈ D) ∧
    n = ∑ j ∈ Finset.range J, c j * (b : ℤ) ^ j}

/-- The standing assumption of §3.1: `R` is a complete residue system mod `b`
inside `(-b, b)` containing `0`, and `D ⊆ R` contains `0` with
`2 ≤ |D| < b`. -/
structure SignedStanding (b : ℕ) (R D : Finset ℤ) : Prop where
  three_le_base : 3 ≤ b
  /-- `R ⊆ (-b, b)`. -/
  residue_abs_lt : ∀ r ∈ R, |r| < (b : ℤ)
  residue_zero_mem : (0 : ℤ) ∈ R
  /-- `R` has `b` elements, pairwise incongruent: a complete residue system. -/
  residue_card : R.card = b
  residue_pairwise : ∀ r ∈ R, ∀ r' ∈ R, (b : ℤ) ∣ (r - r') → r = r'
  subset_residue : D ⊆ R
  zero_mem : (0 : ℤ) ∈ D
  two_le_card : 2 ≤ D.card
  card_lt_base : D.card < b

namespace SignedStanding

variable {b : ℕ} {R D : Finset ℤ}

theorem base_pos (h : SignedStanding b R D) : 0 < b := by
  have := h.three_le_base; omega

theorem abs_digit_lt (h : SignedStanding b R D) {d : ℤ} (hd : d ∈ D) : |d| < (b : ℤ) :=
  h.residue_abs_lt d (h.subset_residue hd)

/-- A digit divisible by the base is zero: this is where the complete residue
system is used. -/
theorem eq_zero_of_dvd (h : SignedStanding b R D) {d : ℤ} (hd : d ∈ D)
    (hdvd : (b : ℤ) ∣ d) : d = 0 :=
  h.residue_pairwise d (h.subset_residue hd) 0 h.residue_zero_mem (by simpa using hdvd)

end SignedStanding

/-! ### Uniqueness of the signed digit representation -/

/-- Uniqueness of the signed digit representation: two digit strings with
digits in a complete residue system `R` mod `b` that represent the same integer
agree.  Proved by induction on the least significant digit.

Blueprint: the uniqueness clause of `def:signedCantorSet`. -/
theorem signed_digits_unique {b : ℕ} {R : Finset ℤ} (hb : 0 < b)
    (hR : ∀ r ∈ R, ∀ r' ∈ R, (b : ℤ) ∣ (r - r') → r = r') :
    ∀ {J : ℕ} {c c' : ℕ → ℤ}, (∀ j < J, c j ∈ R) → (∀ j < J, c' j ∈ R) →
      (∑ j ∈ Finset.range J, c j * (b : ℤ) ^ j
        = ∑ j ∈ Finset.range J, c' j * (b : ℤ) ^ j) →
      ∀ j < J, c j = c' j := by
  have hb0 : (b : ℤ) ≠ 0 := by exact_mod_cast hb.ne'
  intro J
  induction J with
  | zero => intro c c' _ _ _ j hj; omega
  | succ n ih =>
    intro c c' hc hc' heq j hj
    have hpeel : ∀ f : ℕ → ℤ, ∑ i ∈ Finset.range n, f (i + 1) * (b : ℤ) ^ (i + 1)
        = (b : ℤ) * ∑ i ∈ Finset.range n, f (i + 1) * (b : ℤ) ^ i := by
      intro f
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [Finset.sum_range_succ', Finset.sum_range_succ', hpeel c, hpeel c'] at heq
    simp only [pow_zero, mul_one] at heq
    set A := ∑ i ∈ Finset.range n, c (i + 1) * (b : ℤ) ^ i with hA
    set A' := ∑ i ∈ Finset.range n, c' (i + 1) * (b : ℤ) ^ i with hA'
    -- the least significant digits agree, because they are congruent mod `b`
    have hdvd : (b : ℤ) ∣ (c 0 - c' 0) := ⟨A' - A, by linarith⟩
    have h0 : c 0 = c' 0 := hR _ (hc 0 (by omega)) _ (hc' 0 (by omega)) hdvd
    have hAA : A = A' := by
      have : (b : ℤ) * A = (b : ℤ) * A' := by rw [h0] at heq; linarith
      exact mul_left_cancel₀ hb0 this
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · exact h0
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      exact ih (c := fun i => c (i + 1)) (c' := fun i => c' (i + 1))
        (fun i hi => hc (i + 1) (by omega)) (fun i hi => hc' (i + 1) (by omega))
        (by rw [← hA, ← hA', hAA]) i (by omega)

/-- The special case of `signed_digits_unique` with `c' = 0`: a vanishing
signed digit sum has all digits zero. -/
theorem signed_digits_eq_zero {b : ℕ} {R : Finset ℤ} (hb : 0 < b)
    (hR : ∀ r ∈ R, ∀ r' ∈ R, (b : ℤ) ∣ (r - r') → r = r') (hR0 : (0 : ℤ) ∈ R)
    {J : ℕ} {c : ℕ → ℤ} (hc : ∀ j < J, c j ∈ R)
    (hsum : ∑ j ∈ Finset.range J, c j * (b : ℤ) ^ j = 0) :
    ∀ j < J, c j = 0 :=
  signed_digits_unique hb hR hc (fun _ _ => hR0) (by simpa using hsum)

/-! ### Elementary closure properties -/

theorem zero_mem_signedCantorSet (b : ℕ) (D : Finset ℤ) : (0 : ℤ) ∈ signedCantorSet b D :=
  ⟨0, fun _ => 0, by simp, by simp⟩

/-- Prepending a digit: if `z ∈ C` and `d ∈ D` then `d + b z ∈ C`. -/
theorem mem_signedCantorSet_cons {b : ℕ} {D : Finset ℤ} {d : ℤ} (hd : d ∈ D)
    {z : ℤ} (hz : z ∈ signedCantorSet b D) : d + (b : ℤ) * z ∈ signedCantorSet b D := by
  obtain ⟨J, c, hc, rfl⟩ := hz
  refine ⟨J + 1, fun j => if j = 0 then d else c (j - 1), ?_, ?_⟩
  · intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simpa using hd
    · have hj0 : j ≠ 0 := by omega
      simp only [hj0, if_false]
      exact hc (j - 1) (by omega)
  · rw [Finset.sum_range_succ']
    have hterm : ∀ i ∈ Finset.range J,
        (if i + 1 = 0 then d else c (i + 1 - 1)) * (b : ℤ) ^ (i + 1)
          = (b : ℤ) * (c i * (b : ℤ) ^ i) := by
      intro i _
      rw [if_neg (by omega : i + 1 ≠ 0)]
      simp only [Nat.add_sub_cancel]
      ring
    have hzero : ((fun j => if j = 0 then d else c (j - 1)) : ℕ → ℤ) 0 = d := rfl
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hzero]
    ring

/-! ### The block set `E_K = {∑_{j<K} s_j b^j : s_j ∈ S}` -/

open scoped Classical in
/-- `signedBlock b S K` is the set of integers `∑_{j<K} s_j b^j` with all
digits `s_j ∈ S`, built by the recursion `E_{K+1} = S + b · E_K`. -/
def signedBlock (b : ℕ) (S : Finset ℤ) : ℕ → Finset ℤ
  | 0 => {0}
  | K + 1 => (S ×ˢ signedBlock b S K).image (fun p => p.1 + (b : ℤ) * p.2)

theorem mem_signedBlock_succ {b : ℕ} {S : Finset ℤ} {K : ℕ} {x : ℤ} :
    x ∈ signedBlock b S (K + 1) ↔
      ∃ s ∈ S, ∃ e ∈ signedBlock b S K, x = s + (b : ℤ) * e := by
  classical
  simp only [signedBlock, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨s, e, ⟨hs, he⟩, rfl⟩; exact ⟨s, hs, e, he, rfl⟩
  · rintro ⟨s, hs, e, he, rfl⟩; exact ⟨s, e, ⟨hs, he⟩, rfl⟩

theorem signedBlock_nonempty {b : ℕ} {S : Finset ℤ} (hS : S.Nonempty) (K : ℕ) :
    (signedBlock b S K).Nonempty := by
  induction K with
  | zero => exact ⟨0, by simp [signedBlock]⟩
  | succ K ih =>
    obtain ⟨s, hs⟩ := hS
    obtain ⟨e, he⟩ := ih
    exact ⟨s + (b : ℤ) * e, mem_signedBlock_succ.2 ⟨s, hs, e, he, rfl⟩⟩

/-- `|E_K| = |S|^K`: the digit representation is unique. -/
theorem card_signedBlock {b : ℕ} {S : Finset ℤ} (hb : 0 < b)
    (hdvd : ∀ s ∈ S, ∀ t ∈ S, (b : ℤ) ∣ (s - t) → s = t) :
    ∀ K, (signedBlock b S K).card = S.card ^ K
  | 0 => by simp [signedBlock]
  | K + 1 => by
    classical
    have hb0 : (b : ℤ) ≠ 0 := by exact_mod_cast hb.ne'
    have hinj : Set.InjOn (fun p : ℤ × ℤ => p.1 + (b : ℤ) * p.2)
        (↑(S ×ˢ signedBlock b S K) : Set (ℤ × ℤ)) := by
      rintro ⟨s, e⟩ hp ⟨t, f⟩ hq hsum
      obtain ⟨hs, _⟩ := Finset.mem_product.1 (Finset.mem_coe.1 hp)
      obtain ⟨ht, _⟩ := Finset.mem_product.1 (Finset.mem_coe.1 hq)
      have hsum' : s + (b : ℤ) * e = t + (b : ℤ) * f := hsum
      have hst : s = t := hdvd s hs t ht ⟨f - e, by linarith⟩
      have hef : e = f := by
        refine mul_left_cancel₀ hb0 ?_
        rw [hst] at hsum'; linarith
      simp [hst, hef]
    show ((S ×ˢ signedBlock b S K).image (fun p => p.1 + (b : ℤ) * p.2)).card = _
    rw [Finset.card_image_of_injOn hinj, Finset.card_product,
      card_signedBlock hb hdvd K, pow_succ]
    ring

/-- Differences of elements of `E_K` lie in the signed Cantor set. -/
theorem sub_mem_signedCantorSet {b : ℕ} {D S : Finset ℤ}
    (hS : ∀ s ∈ S, ∀ t ∈ S, s - t ∈ D) :
    ∀ {K : ℕ} {x y : ℤ}, x ∈ signedBlock b S K → y ∈ signedBlock b S K →
      x - y ∈ signedCantorSet b D := by
  intro K
  induction K with
  | zero =>
    intro x y hx hy
    simp only [signedBlock, Finset.mem_singleton] at hx hy
    subst hx; subst hy
    simpa using zero_mem_signedCantorSet b D
  | succ K ih =>
    intro x y hx hy
    obtain ⟨s, hs, e, he, rfl⟩ := mem_signedBlock_succ.1 hx
    obtain ⟨t, ht, f, hf, rfl⟩ := mem_signedBlock_succ.1 hy
    have hkey : s + (b : ℤ) * e - (t + (b : ℤ) * f) = (s - t) + (b : ℤ) * (e - f) := by ring
    rw [hkey]
    exact mem_signedCantorSet_cons (hS s hs t ht) (ih he hf)

/-- Differences of elements of `E_K` are smaller than `b^K` in absolute value. -/
theorem abs_sub_signedBlock_lt {b : ℕ} {S : Finset ℤ} (hb : 0 < b)
    (hS : ∀ s ∈ S, ∀ t ∈ S, |s - t| < (b : ℤ)) :
    ∀ {K : ℕ} {x y : ℤ}, x ∈ signedBlock b S K → y ∈ signedBlock b S K →
      |x - y| < (b : ℤ) ^ K := by
  have hbZ : (0 : ℤ) < (b : ℤ) := by exact_mod_cast hb
  intro K
  induction K with
  | zero =>
    intro x y hx hy
    simp only [signedBlock, Finset.mem_singleton] at hx hy
    subst hx; subst hy
    simp
  | succ K ih =>
    intro x y hx hy
    obtain ⟨s, hs, e, he, rfl⟩ := mem_signedBlock_succ.1 hx
    obtain ⟨t, ht, f, hf, rfl⟩ := mem_signedBlock_succ.1 hy
    have hpowpos : (0 : ℤ) < (b : ℤ) ^ K := pow_pos hbZ K
    have h1 : |s - t| ≤ (b : ℤ) - 1 := by have := hS s hs t ht; omega
    have h2 : |e - f| ≤ (b : ℤ) ^ K - 1 := by have := ih he hf; omega
    have hkey : s + (b : ℤ) * e - (t + (b : ℤ) * f) = (s - t) + (b : ℤ) * (e - f) := by ring
    rw [hkey]
    have hstep : |(s - t) + (b : ℤ) * (e - f)| ≤ |s - t| + (b : ℤ) * |e - f| := by
      calc |(s - t) + (b : ℤ) * (e - f)| ≤ |s - t| + |(b : ℤ) * (e - f)| := abs_add_le _ _
        _ = |s - t| + (b : ℤ) * |e - f| := by rw [abs_mul, abs_of_pos hbZ]
    have hmul : (b : ℤ) * |e - f| ≤ (b : ℤ) * ((b : ℤ) ^ K - 1) :=
      mul_le_mul_of_nonneg_left h2 hbZ.le
    have : |(s - t) + (b : ℤ) * (e - f)| ≤ (b : ℤ) ^ (K + 1) - 1 := by
      have hexp : (b : ℤ) ^ (K + 1) = (b : ℤ) * (b : ℤ) ^ K := by ring
      rw [hexp]; linarith
    omega

/-! ### The power savings bound -/

/-- Proposition 3.7 along the sequence `N = b^K`: the Fejér kernel of the block
set `E_K`, which has `σ^K` elements, has constant term `σ^{-K}`.

This is `vdcConst_le_of_differences_mem` applied to the increasing enumeration
of `E_K` translated to start at `0`. -/
theorem vdcConst_signed_pow_le {b : ℕ} {R D S : Finset ℤ} (h : SignedStanding b R D)
    (hSD : ∀ s ∈ S, ∀ t ∈ S, s - t ∈ D) (hS : S.Nonempty) (K : ℕ) :
    vdcConst ((fun z : ℤ => z.natAbs) '' signedCantorSet b D \ {0}) (b ^ K)
      ≤ 1 / (S.card : ℝ) ^ K := by
  classical
  set H : Set ℕ := (fun z : ℤ => z.natAbs) '' signedCantorSet b D \ {0} with hH
  have hb : 0 < b := h.base_pos
  have hbZ : (0 : ℤ) < (b : ℤ) := by exact_mod_cast hb
  have hdvd : ∀ s ∈ S, ∀ t ∈ S, (b : ℤ) ∣ (s - t) → s = t := by
    intro s hs t ht hd
    have : s - t = 0 := h.eq_zero_of_dvd (hSD s hs t ht) hd
    omega
  have habs : ∀ s ∈ S, ∀ t ∈ S, |s - t| < (b : ℤ) := fun s hs t ht =>
    h.abs_digit_lt (hSD s hs t ht)
  set E : Finset ℤ := signedBlock b S K with hE
  have hEne : E.Nonempty := signedBlock_nonempty hS K
  have hEcard : E.card = S.card ^ K := card_signedBlock hb hdvd K
  set n : ℕ := S.card ^ K with hn
  have hnpos : 0 < n := pow_pos (Finset.card_pos.2 hS) K
  set m₀ : ℤ := E.min' hEne with hm₀
  set v : Fin n → ℤ := ⇑(E.orderEmbOfFin hEcard) with hv
  have hvmem : ∀ i : Fin n, v i ∈ E := fun i => Finset.orderEmbOfFin_mem E hEcard i
  have hvlt : ∀ i j : Fin n, i < j → v i < v j := fun i j hij =>
    (E.orderEmbOfFin hEcard).strictMono hij
  have hvge : ∀ i : Fin n, m₀ ≤ v i := fun i => E.min'_le _ (hvmem i)
  set u : ℕ → ℕ := fun i => if hi : i < n then (v ⟨i, hi⟩ - m₀).toNat else 0 with hu
  have hudef : ∀ (i : ℕ) (hi : i < n), u i = (v ⟨i, hi⟩ - m₀).toNat := by
    intro i hi; simp only [hu, dif_pos hi]
  -- the three hypotheses of the Fejér kernel lemma
  have hpair : ∀ (i j : ℕ) (hij : i < j) (hj : j < n),
      v ⟨i, by omega⟩ < v ⟨j, hj⟩ := by
    intro i j hij hj
    exact hvlt ⟨i, by omega⟩ ⟨j, hj⟩ (by simpa using hij)
  have hmono : ∀ i j : ℕ, i < j → j < n → u i < u j := by
    intro i j hij hj
    have hi : i < n := by omega
    rw [hudef i hi, hudef j hj]
    have h1 := hpair i j hij hj
    have h2 := hvge ⟨i, hi⟩
    omega
  have hsub : ∀ i j : ℕ, (hij : i < j) → (hj : j < n) →
      ((u j - u i : ℕ) : ℤ) = v ⟨j, hj⟩ - v ⟨i, by omega⟩ := by
    intro i j hij hj
    have hi : i < n := by omega
    rw [hudef i hi, hudef j hj]
    have h1 := hpair i j hij hj
    have h2 := hvge ⟨i, hi⟩
    omega
  have hmem : ∀ i j : ℕ, i < j → j < n → (u j - u i) ∈ H := by
    intro i j hij hj
    have hi : i < n := by omega
    have hC : v ⟨j, hj⟩ - v ⟨i, hi⟩ ∈ signedCantorSet b D :=
      sub_mem_signedCantorSet hSD (hvmem ⟨j, hj⟩) (hvmem ⟨i, hi⟩)
    have hcast := hsub i j hij hj
    have hne : u i < u j := hmono i j hij hj
    refine ⟨⟨v ⟨j, hj⟩ - v ⟨i, hi⟩, hC, ?_⟩, ?_⟩
    · have : ((v ⟨j, hj⟩ - v ⟨i, hi⟩).natAbs : ℤ) = ((u j - u i : ℕ) : ℤ) := by
        rw [hcast]; omega
      exact_mod_cast this
    · simp only [Set.mem_singleton_iff]
      omega
  have hlt : ∀ i j : ℕ, i < j → j < n → u j - u i < b ^ K := by
    intro i j hij hj
    have hi : i < n := by omega
    have hA : |v ⟨j, hj⟩ - v ⟨i, hi⟩| < (b : ℤ) ^ K :=
      abs_sub_signedBlock_lt hb habs (hvmem ⟨j, hj⟩) (hvmem ⟨i, hi⟩)
    have hcast := hsub i j hij hj
    have hpow : ((b ^ K : ℕ) : ℤ) = (b : ℤ) ^ K := by push_cast; ring
    have hA2 : v ⟨j, hj⟩ - v ⟨i, hi⟩ < (b : ℤ) ^ K := (abs_lt.1 hA).2
    have : ((u j - u i : ℕ) : ℤ) < ((b ^ K : ℕ) : ℤ) := by rw [hcast, hpow]; exact hA2
    exact_mod_cast this
  have := vdcConst_le_of_differences_mem H (b ^ K) n hnpos u hmono hmem hlt
  calc vdcConst H (b ^ K) ≤ 1 / (n : ℝ) := this
    _ = 1 / (S.card : ℝ) ^ K := by rw [hn]; push_cast; ring

/-- **Proposition 3.7** (power savings for signed digit sets).  If `S` is a
finite set of integers with `S - S ⊆ D` and `σ = |S| > 1`, then for `N ≥ b`,
`τ(C, N) ≤ σ N^{-log σ / log b}`.

Blueprint: `thm:powerSavings`. -/
theorem vdcConst_signed_le {b : ℕ} {R D S : Finset ℤ} (h : SignedStanding b R D)
    (hSD : ∀ s ∈ S, ∀ t ∈ S, s - t ∈ D) (hσ : 1 < S.card) {N : ℕ} (hN : b ≤ N) :
    vdcConst ((fun z : ℤ => z.natAbs) '' signedCantorSet b D \ {0}) N
      ≤ (S.card : ℝ) * (N : ℝ) ^ (-Real.log S.card / Real.log b) := by
  set H : Set ℕ := (fun z : ℤ => z.natAbs) '' signedCantorSet b D \ {0} with hH
  have hb3 := h.three_le_base
  have hb1 : 1 < b := by omega
  have hN0 : N ≠ 0 := by omega
  have hS : S.Nonempty := Finset.card_pos.1 (by omega)
  set k : ℕ := Nat.log b N with hk
  have hbk : b ^ k ≤ N := Nat.pow_log_le_self b hN0
  have hNlt : N < b ^ (k + 1) := Nat.lt_pow_succ_log_self hb1 N
  -- the bound at `N = b^k`, moved to `N` by antitonicity
  have h1 : vdcConst H N ≤ 1 / (S.card : ℝ) ^ k :=
    le_trans (vdcConst_antitone H hbk) (vdcConst_signed_pow_le h hSD hS k)
  -- the real estimate
  have hσR : (1 : ℝ) < (S.card : ℝ) := by exact_mod_cast hσ
  have hbR : (1 : ℝ) < (b : ℝ) := by exact_mod_cast hb1
  have hlogσ : 0 < Real.log (S.card : ℝ) := Real.log_pos hσR
  have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos hbR
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN0
  set c : ℝ := Real.log (S.card : ℝ) / Real.log (b : ℝ) with hc
  have hcpos : 0 < c := div_pos hlogσ hlogb
  have hcc : -Real.log (S.card : ℝ) / Real.log (b : ℝ) = -c := by rw [hc, neg_div]
  rw [hcc]
  have hlogN : Real.log (N : ℝ) ≤ ((k : ℝ) + 1) * Real.log (b : ℝ) := by
    have hle : (N : ℝ) ≤ (b : ℝ) ^ (k + 1) := by exact_mod_cast hNlt.le
    calc Real.log (N : ℝ) ≤ Real.log ((b : ℝ) ^ (k + 1)) := Real.log_le_log hNR hle
      _ = ((k : ℝ) + 1) * Real.log (b : ℝ) := by rw [Real.log_pow]; push_cast; ring
  have hexp : Real.exp (-(((k : ℝ) + 1) * Real.log (S.card : ℝ)))
      = ((S.card : ℝ) ^ (k + 1))⁻¹ := by
    rw [Real.exp_neg]
    congr 1
    rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, ← Real.log_pow]
    exact Real.exp_log (by positivity)
  have h3 : ((S.card : ℝ) ^ (k + 1))⁻¹ ≤ (N : ℝ) ^ (-c) := by
    rw [Real.rpow_def_of_pos hNR, ← hexp]
    refine Real.exp_le_exp.2 ?_
    have hmul : c * Real.log (N : ℝ) ≤ c * (((k : ℝ) + 1) * Real.log (b : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogN hcpos.le
    have heq : c * (((k : ℝ) + 1) * Real.log (b : ℝ))
        = ((k : ℝ) + 1) * Real.log (S.card : ℝ) := by
      rw [hc]; field_simp
    rw [heq] at hmul
    have hrw : Real.log (N : ℝ) * (-c) = -(c * Real.log (N : ℝ)) := by ring
    rw [hrw]
    linarith
  have h4 : 1 / (S.card : ℝ) ^ k = (S.card : ℝ) * ((S.card : ℝ) ^ (k + 1))⁻¹ := by
    have hσ0 : (S.card : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  calc vdcConst H N ≤ 1 / (S.card : ℝ) ^ k := h1
    _ = (S.card : ℝ) * ((S.card : ℝ) ^ (k + 1))⁻¹ := h4
    _ ≤ (S.card : ℝ) * (N : ℝ) ^ (-c) := mul_le_mul_of_nonneg_left h3 (by positivity)

/-! ### The concrete example of §3.1 -/

/-- The example given in §3.1: `b = 5`, `R_5 = {-2,-1,0,1,2}`, `D = {-1,0,1}`
and `S = {0,1}`.  It witnesses that `SignedStanding` together with the
hypotheses of `vdcConst_signed_le` is not vacuous, and gives a Cantor set with
a power saving of order `log 2 / log 5`. -/
theorem vdcConst_signed_le_example {N : ℕ} (hN : 5 ≤ N) :
    vdcConst ((fun z : ℤ => z.natAbs) '' signedCantorSet 5 {-1, 0, 1} \ {0}) N
      ≤ 2 * (N : ℝ) ^ (-Real.log 2 / Real.log 5) := by
  have h : SignedStanding 5 {-2, -1, 0, 1, 2} {-1, 0, 1} := by constructor <;> decide
  have hSD : ∀ s ∈ ({0, 1} : Finset ℤ), ∀ t ∈ ({0, 1} : Finset ℤ),
      s - t ∈ ({-1, 0, 1} : Finset ℤ) := by decide
  have hσ : 1 < ({0, 1} : Finset ℤ).card := by decide
  have hc2 : ({0, 1} : Finset ℤ).card = 2 := by decide
  have hmain := vdcConst_signed_le h hSD hσ hN
  rw [hc2] at hmain
  norm_num at hmain
  exact hmain

end IntegerCantorSet
