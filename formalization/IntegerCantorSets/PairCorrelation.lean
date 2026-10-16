/-
Metric pair correlation: the additive energy of the initial blocks of an
integer Cantor set.

Blueprint: `blueprint/src/content.tex`, Chapter `chap:paircorr`.

The target of this file is `additiveEnergy_pow` (`lem:noCarry`): if every digit
of `D` is at most `⌊(b-1)/2⌋`, then adding two elements of `C(b,D) ∩ [0, b^ℓ)`
produces no carries, and consequently `E(C(b,D) ∩ [0,b^ℓ)) = E(D)^ℓ`.

`HasPairCorrelation` (`def:pairCorrelation`) is recorded here too.  Its only
consumer, `thm:pairCorrelation`, rests on Aistleitner--Larcher--Lewko, which is
not a formalization target, so this file is a leaf.

This file contains no `sorry`.
-/
import IntegerCantorSets.ExpSum

namespace IntegerCantorSet

open Finset Filter

variable {b : ℕ} {D : Finset ℕ}

/-! ### Poissonian pair correlation -/

/-- A sequence `θ` has *Poissonian pair correlation* if for every `s > 0`,
`N⁻¹ #{0 ≤ j ≠ k < N : ‖θ j - θ k‖ < s / N} → 2 s`, where `‖·‖` is `distInt`,
the distance to the nearest integer.

Blueprint: `def:pairCorrelation`. -/
def HasPairCorrelation (θ : ℕ → ℝ) : Prop :=
  ∀ s : ℝ, 0 < s →
    Tendsto (fun N : ℕ =>
        ({p : ℕ × ℕ | p.1 < N ∧ p.2 < N ∧ p.1 ≠ p.2 ∧
            distInt (θ p.1 - θ p.2) < s / N}.ncard : ℝ) / N)
      atTop (nhds (2 * s))

/-! ### Additive energy

Mathlib's `Finset.addEnergy s t` is
`#{q ∈ (s ×ˢ s) ×ˢ t ×ˢ t | q.1.1 + q.2.1 = q.1.2 + q.2.2}`, so with `s = t = A`
it counts exactly the quadruples `(x, z, y, w) ∈ A⁴` with `x + y = z + w`: the
conventions agree with the blueprint's, and nothing needs reproving.  The
blueprint's `additiveEnergy` is therefore a thin wrapper, kept only because the
blueprint names it. -/

/-- The additive energy `E(A) = #{(x,y,z,w) ∈ A⁴ : x + y = z + w}`, Mathlib's
`Finset.addEnergy A A`.

Blueprint: `def:additiveEnergy`. -/
abbrev additiveEnergy (A : Finset ℕ) : ℕ := Finset.addEnergy A A

theorem additiveEnergy_eq_card (A : Finset ℕ) :
    additiveEnergy A
      = #{q ∈ (A ×ˢ A) ×ˢ A ×ˢ A | q.1.1 + q.2.1 = q.1.2 + q.2.2} := rfl

@[simp] theorem additiveEnergy_singleton (a : ℕ) : additiveEnergy {a} = 1 := by
  simp [additiveEnergy_eq_card, Finset.filter_singleton]

/-! ### No carries

The whole of `lem:noCarry` rests on one observation about a single digit
position, `noCarry_add_eq_iff`: once two low digits cannot sum past `b - 1`,
the high and low parts of a sum of two numbers do not interact. -/

/-- Base `b` splitting is unique below the base. -/
theorem eq_of_base_add {u r u' r' : ℕ} (hr : r < b) (hr' : r' < b)
    (hq : b * u + r = b * u' + r') : u = u' ∧ r = r' := by
  have hb : 0 < b := lt_of_le_of_lt (Nat.zero_le r) hr
  have hrr : r = r' := by
    have hmod := congrArg (· % b) hq
    simpa [Nat.mul_add_mod, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hr'] using hmod
  exact ⟨Nat.eq_of_mul_eq_mul_left hb (by omega), hrr⟩

/-- **No carries.**  If the two low digits sum to less than the base on either
side, then `(b x + d) + (b y + e) = (b x' + d') + (b y' + e')` holds exactly
when the high parts and the low parts agree separately: the digit positions do
not interact.

Blueprint: `lem:noCarry`, the digit-level observation. -/
theorem noCarry_add_eq_iff {x y x' y' d e d' e' : ℕ}
    (hde : d + e < b) (hde' : d' + e' < b) :
    (b * x + d) + (b * y + e) = (b * x' + d') + (b * y' + e')
      ↔ x + y = x' + y' ∧ d + e = d' + e' := by
  have hL : (b * x + d) + (b * y + e) = b * (x + y) + (d + e) := by ring
  have hR : (b * x' + d') + (b * y' + e') = b * (x' + y') + (d' + e') := by ring
  rw [hL, hR]
  refine ⟨fun hq => eq_of_base_add hde hde' hq, ?_⟩
  rintro ⟨h1, h2⟩
  rw [h1, h2]

/-- The digit hypothesis of `lem:noCarry`, `D ⊆ {0, …, ⌊(b-1)/2⌋}`, is exactly
what makes any two digits sum to less than the base. -/
theorem add_lt_base_of_le_half (hb : 3 ≤ b) {d e : ℕ}
    (hd : d ≤ (b - 1) / 2) (he : e ≤ (b - 1) / 2) : d + e < b := by omega

/-- **Additive energy factors across a digit position.**  If every pair of
elements of `S` sums to less than `b`, then adding two elements of `b · A + S`
produces no carry out of the low digit, and `E(b · A + S) = E(A) · E(S)`. -/
theorem additiveEnergy_image_base (A S : Finset ℕ)
    (hS : ∀ d ∈ S, ∀ e ∈ S, d + e < b) :
    additiveEnergy ((A ×ˢ S).image fun p => b * p.1 + p.2)
      = additiveEnergy A * additiveEnergy S := by
  have hlt : ∀ d ∈ S, d < b := fun d hd =>
    lt_of_le_of_lt (Nat.le_add_right d d) (hS d hd d hd)
  have hmemB : ∀ k : ℕ,
      k ∈ (A ×ˢ S).image (fun p => b * p.1 + p.2) ↔ ∃ x ∈ A, ∃ d ∈ S, b * x + d = k := by
    intro k
    simp only [Finset.mem_image, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨x, d, ⟨hx, hd⟩, rfl⟩; exact ⟨x, hx, d, hd, rfl⟩
    · rintro ⟨x, hx, d, hd, rfl⟩; exact ⟨x, d, ⟨hx, hd⟩, rfl⟩
  rw [additiveEnergy_eq_card, additiveEnergy_eq_card, additiveEnergy_eq_card,
    ← Finset.card_product]
  refine (Finset.card_nbij
      (fun q : ((ℕ × ℕ) × ℕ × ℕ) × (ℕ × ℕ) × ℕ × ℕ =>
        ((b * q.1.1.1 + q.2.1.1, b * q.1.1.2 + q.2.1.2),
          (b * q.1.2.1 + q.2.2.1, b * q.1.2.2 + q.2.2.2)))
      ?_ ?_ ?_).symm
  · rintro ⟨⟨⟨x₁, x₂⟩, y₁, y₂⟩, ⟨d₁, d₂⟩, e₁, e₂⟩ hq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_product] at hq
    obtain ⟨⟨⟨⟨hx₁, hx₂⟩, hy₁, hy₂⟩, hA⟩, ⟨⟨hd₁, hd₂⟩, he₁, he₂⟩, hSq⟩ := hq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨⟨hmemB _ |>.2 ⟨x₁, hx₁, d₁, hd₁, rfl⟩, hmemB _ |>.2 ⟨x₂, hx₂, d₂, hd₂, rfl⟩⟩,
      hmemB _ |>.2 ⟨y₁, hy₁, e₁, he₁, rfl⟩, hmemB _ |>.2 ⟨y₂, hy₂, e₂, he₂, rfl⟩⟩, ?_⟩
    exact (noCarry_add_eq_iff (hS _ hd₁ _ he₁) (hS _ hd₂ _ he₂)).2 ⟨hA, hSq⟩
  · intro p hp p' hp' heq
    obtain ⟨⟨⟨x₁, x₂⟩, y₁, y₂⟩, ⟨d₁, d₂⟩, e₁, e₂⟩ := p
    obtain ⟨⟨⟨x₁', x₂'⟩, y₁', y₂'⟩, ⟨d₁', d₂'⟩, e₁', e₂'⟩ := p'
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_product] at hp hp'
    obtain ⟨-, ⟨⟨hd₁, hd₂⟩, he₁, he₂⟩, -⟩ := hp
    obtain ⟨-, ⟨⟨hd₁', hd₂'⟩, he₁', he₂'⟩, -⟩ := hp'
    simp only [Prod.mk.injEq] at heq
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := heq
    obtain ⟨rfl, rfl⟩ := eq_of_base_add (hlt _ hd₁) (hlt _ hd₁') h1
    obtain ⟨rfl, rfl⟩ := eq_of_base_add (hlt _ hd₂) (hlt _ hd₂') h2
    obtain ⟨rfl, rfl⟩ := eq_of_base_add (hlt _ he₁) (hlt _ he₁') h3
    obtain ⟨rfl, rfl⟩ := eq_of_base_add (hlt _ he₂) (hlt _ he₂') h4
    rfl
  · rintro ⟨⟨u₁, u₂⟩, v₁, v₂⟩ hq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hq
    obtain ⟨⟨⟨hu₁, hu₂⟩, hv₁, hv₂⟩, hsum⟩ := hq
    obtain ⟨x₁, hx₁, d₁, hd₁, rfl⟩ := (hmemB _).1 hu₁
    obtain ⟨x₂, hx₂, d₂, hd₂, rfl⟩ := (hmemB _).1 hu₂
    obtain ⟨y₁, hy₁, e₁, he₁, rfl⟩ := (hmemB _).1 hv₁
    obtain ⟨y₂, hy₂, e₂, he₂, rfl⟩ := (hmemB _).1 hv₂
    obtain ⟨hA, hSq⟩ :=
      (noCarry_add_eq_iff (hS _ hd₁ _ he₁) (hS _ hd₂ _ he₂)).1 hsum
    refine ⟨(((x₁, x₂), y₁, y₂), ((d₁, d₂), e₁, e₂)), ?_, rfl⟩
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_product]
    exact ⟨⟨⟨⟨hx₁, hx₂⟩, hy₁, hy₂⟩, hA⟩, ⟨⟨hd₁, hd₂⟩, he₁, he₂⟩, hSq⟩

/-! ### The initial blocks of the Cantor set -/

/-- The initial block `C(b,D) ∩ [0, b^ℓ)` as a `Finset`: the first `|D|^ℓ`
values of the enumeration.  `coe_cantorBlock` identifies the two descriptions,
via `enum_image_Iio` (`lem:enum-initial`). -/
def cantorBlock (b : ℕ) (D : Finset ℕ) (l : ℕ) : Finset ℕ :=
  (Finset.range (D.card ^ l)).image (enum b D)

theorem coe_cantorBlock (h : Standing b D) (l : ℕ) :
    (cantorBlock b D l : Set ℕ) = cantorSet b D ∩ Set.Iio (b ^ l) := by
  rw [cantorBlock, Finset.coe_image, Finset.coe_range, ← enum_image_Iio h]

@[simp] theorem cantorBlock_zero : cantorBlock b D 0 = {0} := by
  simp [cantorBlock]

/-- The digit recursion for the blocks: `C ∩ [0, b^{ℓ+1}) = b · (C ∩ [0,b^ℓ)) + D`. -/
theorem cantorBlock_succ (h : Standing b D) (l : ℕ) :
    cantorBlock b D (l + 1)
      = (cantorBlock b D l ×ˢ D).image (fun p => b * p.1 + p.2) := by
  have hcard : 1 < D.card := by have := h.two_le_card; omega
  ext k
  simp only [cantorBlock, Finset.mem_image, Finset.mem_range, Finset.mem_product,
    Prod.exists]
  constructor
  · rintro ⟨n, hn, rfl⟩
    refine ⟨enum b D (n / D.card), digitOf D (n % D.card),
      ⟨⟨n / D.card, ?_, rfl⟩, digitOf_mem (Nat.mod_lt _ (by omega))⟩, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul (by omega)]
      calc n < D.card ^ (l + 1) := hn
        _ = D.card ^ l * D.card := by ring
    · exact (enum_div_mod h n).symm
  · rintro ⟨x, d, ⟨⟨m, hm, rfl⟩, hd⟩, rfl⟩
    obtain ⟨j, hj, rfl⟩ := exists_digitOf_eq hd
    refine ⟨D.card * m + j, ?_, enum_mul_add h m hj⟩
    calc D.card * m + j < D.card * m + D.card := by omega
      _ = D.card * (m + 1) := by ring
      _ ≤ D.card * D.card ^ l := Nat.mul_le_mul le_rfl (by omega)
      _ = D.card ^ (l + 1) := by ring

/-- The no-carry phenomenon in its digit-sum form: on an initial block, the
base `b` digit sum is additive, which says exactly that no carry occurs. -/
theorem sumDigits_add_cantorBlock (h : Standing b D) (hD : ∀ d ∈ D, d ≤ (b - 1) / 2) :
    ∀ (l x y : ℕ), x ∈ cantorBlock b D l → y ∈ cantorBlock b D l →
      sumDigits b (x + y) = sumDigits b x + sumDigits b y := by
  have hb : 1 < b := by have := h.three_le_base; omega
  intro l
  induction l with
  | zero =>
    intro x y hx hy
    simp only [cantorBlock_zero, Finset.mem_singleton] at hx hy
    subst hx; subst hy
    simp [sumDigits]
  | succ k ih =>
    intro x y hx hy
    rw [cantorBlock_succ h, Finset.mem_image] at hx hy
    obtain ⟨⟨x', d⟩, hxm, rfl⟩ := hx
    obtain ⟨⟨y', e⟩, hym, rfl⟩ := hy
    dsimp only at hxm hym ⊢
    rw [Finset.mem_product] at hxm hym
    obtain ⟨hx', hd⟩ := hxm
    obtain ⟨hy', he⟩ := hym
    have hde : d + e < b := add_lt_base_of_le_half h.three_le_base (hD d hd) (hD e he)
    have hsplit : b * x' + d + (b * y' + e) = b * (x' + y') + (d + e) := by ring
    rw [hsplit, sumDigits_mul_add hb _ hde, sumDigits_mul_add hb _ (by omega : d < b),
      sumDigits_mul_add hb _ (by omega : e < b), ih x' y' hx' hy']
    omega

/-- **Lemma `lem:noCarry`.**  If every digit of `D` is at most `⌊(b-1)/2⌋`, then
adding two elements of `C(b,D) ∩ [0, b^ℓ)` produces no carries, and consequently
`E(C(b,D) ∩ [0, b^ℓ)) = E(D)^ℓ`.

Blueprint: `lem:noCarry`. -/
theorem additiveEnergy_pow (h : Standing b D) (hD : ∀ d ∈ D, d ≤ (b - 1) / 2) (l : ℕ) :
    additiveEnergy (cantorBlock b D l) = additiveEnergy D ^ l := by
  induction l with
  | zero => simp
  | succ k ih =>
    rw [cantorBlock_succ h,
      additiveEnergy_image_base _ _ (fun d hd e he =>
        add_lt_base_of_le_half h.three_le_base (hD d hd) (hD e he)),
      ih, pow_succ]

end IntegerCantorSet
