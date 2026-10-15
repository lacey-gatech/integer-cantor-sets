/-
Structure theory of integer Cantor sets: the enumeration theorem.

Blueprint: `blueprint/src/content.tex`, Chapter 2, Sections "Elementary
properties of the digit substitution" through "Divisibility".
-/
import IntegerCantorSets.Defs

namespace IntegerCantorSet

open Finset

variable {b : ℕ} {D : Finset ℕ}

/-- `0` lies in every integer Cantor set. -/
theorem zero_mem_cantorSet : (0 : ℕ) ∈ cantorSet b D := by
  simp [cantorSet]

/-! ### Elementary properties of the digit substitution -/

/-- Blueprint: `lem:digitOf-zero`. -/
theorem digitOf_zero (h : Standing b D) : digitOf D 0 = 0 := by
  have hcard : 0 < D.card := by have := h.two_le_card; omega
  have hne : D.Nonempty := Finset.card_pos.1 hcard
  have hlen : 0 < (D.sort (· ≤ ·)).length := by rw [Finset.length_sort]; exact hcard
  have key : digitOf D 0 = D.min' hne := by
    rw [digitOf, List.getD_eq_getElem _ _ hlen]
    exact Finset.sorted_zero_eq_min'
  rw [key]
  exact Nat.le_zero.1 (Finset.min'_le _ _ h.zero_mem)

/-- Blueprint: `lem:digitOf-mem`. -/
theorem digitOf_mem {i : ℕ} (hi : i < D.card) : digitOf D i ∈ D := by
  have hlen : (D.sort (· ≤ ·)).length = D.card := Finset.length_sort _
  have hi' : i < (D.sort (· ≤ ·)).length := by omega
  rw [digitOf, List.getD_eq_getElem _ _ hi']
  exact (Finset.mem_sort _).1 (List.getElem_mem hi')

/-- The working form of `digitOf_strictMonoOn`: the sorted list of `D` is
strictly increasing. -/
theorem digitOf_lt {i j : ℕ} (hij : i < j) (hj : j < D.card) :
    digitOf D i < digitOf D j := by
  have hlen : (D.sort (· ≤ ·)).length = D.card := Finset.length_sort _
  have hj' : j < (D.sort (· ≤ ·)).length := by omega
  have hi' : i < (D.sort (· ≤ ·)).length := by omega
  rw [digitOf, digitOf, List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hj']
  exact List.pairwise_iff_getElem.1 (Finset.sortedLT_sort D).pairwise i j hi' hj' hij

/-- Blueprint: `lem:digitOf-strictMono`. -/
theorem digitOf_strictMonoOn :
    Set.InjOn (digitOf D) (Set.Iio D.card) ∧
      ∀ i j, i < j → j < D.card → digitOf D i < digitOf D j := by
  refine ⟨?_, fun i j hij hj => digitOf_lt hij hj⟩
  intro i hi j hj hEq
  simp only [Set.mem_Iio] at hi hj
  rcases lt_trichotomy i j with h1 | h1 | h1
  · exact absurd hEq (Nat.ne_of_lt (digitOf_lt h1 hj))
  · exact h1
  · exact absurd hEq.symm (Nat.ne_of_lt (digitOf_lt h1 hi))

/-- Blueprint: `lem:digitOf-ne-zero`.  This is the lemma that makes `0 ∈ D`
load-bearing: it is what lets `Nat.digits_ofDigits` apply in `digits_enum`. -/
theorem digitOf_ne_zero (h : Standing b D) {i : ℕ} (hi : 0 < i) (hi' : i < D.card) :
    digitOf D i ≠ 0 := by
  have h1 := digitOf_lt hi hi'
  rw [digitOf_zero h] at h1
  omega

/-- Every element of `D` is `digitOf D c` for some `c < |D|`; by
`digitOf_strictMonoOn` that `c` is unique. -/
theorem exists_digitOf_eq {d : ℕ} (hd : d ∈ D) : ∃ c < D.card, digitOf D c = d := by
  have hmem : d ∈ D.sort (· ≤ ·) := (Finset.mem_sort _).2 hd
  obtain ⟨c, hc, hcd⟩ := List.getElem_of_mem hmem
  refine ⟨c, ?_, ?_⟩
  · rw [← Finset.length_sort (· ≤ ·) (s := D)]; exact hc
  · rw [digitOf, List.getD_eq_getElem _ _ hc]; exact hcd

/-! ### The recursion satisfied by `enum`

`enum` reads one base `|D|` digit at a time; everything below is derived from
`enum_mul_add`, which is the single-digit step. -/

/-- On a single base `|D|` digit, `enum` *is* the digit substitution. -/
theorem enum_of_lt_card (h : Standing b D) {j : ℕ} (hj : j < D.card) :
    enum b D j = digitOf D j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp [enum, digitOf_zero h]
  · rw [enum, Nat.digits_of_lt _ _ (by omega) hj]
    simp

/-- The basic recursion for `enum`: appending the base `|D|` digit `j` to `m`
appends the base `b` digit `digitOf D j` to `enum b D m`. -/
theorem enum_mul_add (h : Standing b D) (m : ℕ) {j : ℕ} (hj : j < D.card) :
    enum b D (D.card * m + j) = b * enum b D m + digitOf D j := by
  have hcard : 1 < D.card := by have := h.two_le_card; omega
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 : enum b D 0 = 0 := by simp [enum]
    simp [h0, enum_of_lt_card h hj]
  · have hpos : 0 < D.card * m + j := by
      have : 0 < D.card * m := Nat.mul_pos (by omega) hm
      omega
    have hmod : (D.card * m + j) % D.card = j := by
      rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hj
    have hdiv : (D.card * m + j) / D.card = m := by
      rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj]; omega
    rw [enum, Nat.digits_def' hcard hpos, hmod, hdiv, List.map_cons, Nat.ofDigits_cons, enum]
    ring

/-- `enum_mul_add` in division form. -/
theorem enum_div_mod (h : Standing b D) (n : ℕ) :
    enum b D n = b * enum b D (n / D.card) + digitOf D (n % D.card) := by
  have hcard : 1 < D.card := by have := h.two_le_card; omega
  conv_lhs => rw [← Nat.div_add_mod n D.card]
  exact enum_mul_add h _ (Nat.mod_lt _ (by omega))

/-! ### The enumeration theorem -/

/-- Blueprint: `lem:digits-enum`.  The base `b` digits of `enum b D n` are the
base `|D|` digits of `n` with `c` replaced by `digitOf D c`. -/
theorem digits_enum (h : Standing b D) (n : ℕ) :
    Nat.digits b (enum b D n) = (Nat.digits D.card n).map (digitOf D) := by
  have hb : 1 < b := by have := h.three_le_base; omega
  have hcard : 1 < D.card := by have := h.two_le_card; omega
  rw [enum]
  refine Nat.digits_ofDigits b hb _ ?_ ?_
  · intro l hl
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hl
    exact h.lt_base _ (digitOf_mem (Nat.digits_lt_base hcard hc))
  · intro hne
    have hne' : Nat.digits D.card n ≠ [] := by simpa using hne
    have hn0 : n ≠ 0 := by
      intro h0; rw [h0] at hne'; simp at hne'
    have hlast : ((Nat.digits D.card n).map (digitOf D)).getLast hne
        = digitOf D ((Nat.digits D.card n).getLast hne') := by
      simp [List.getLast_eq_getElem]
    rw [hlast]
    refine digitOf_ne_zero h ?_ ?_
    · have := Nat.getLast_digit_ne_zero D.card hn0
      omega
    · exact Nat.digits_lt_base hcard (List.getLast_mem hne')

/-- Blueprint: `lem:enum-mem`. -/
theorem enum_mem_cantorSet (h : Standing b D) (n : ℕ) :
    enum b D n ∈ cantorSet b D := by
  have hcard : 1 < D.card := by have := h.two_le_card; omega
  intro d hd
  rw [digits_enum h] at hd
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
  exact digitOf_mem (Nat.digits_lt_base hcard hc)

@[simp] theorem enum_zero : enum b D 0 = 0 := by
  simp [enum]

/-- Blueprint: `lem:enum-strictMono`. -/
theorem enum_strictMono (h : Standing b D) : StrictMono (enum b D) := by
  have hcard : 1 < D.card := by have := h.two_le_card; omega
  have key : ∀ m n, n < m → enum b D n < enum b D m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro n hnm
      have hm : 0 < m := by omega
      have hrn := enum_div_mod h n
      have hrm := enum_div_mod h m
      rcases lt_or_eq_of_le (Nat.div_le_div_right (le_of_lt hnm) : n / D.card ≤ m / D.card)
        with hlt | heq
      · -- the base `|D|` digit lists of `n` and `m` differ above position `0`
        have hmlt : m / D.card < m := Nat.div_lt_self hm hcard
        have hAB := ih _ hmlt _ hlt
        have hd : digitOf D (n % D.card) < b :=
          h.lt_base _ (digitOf_mem (Nat.mod_lt _ (by omega)))
        have hstep : b * enum b D (n / D.card) + b ≤ b * enum b D (m / D.card) := by
          calc b * enum b D (n / D.card) + b = b * (enum b D (n / D.card) + 1) := by ring
            _ ≤ b * enum b D (m / D.card) := Nat.mul_le_mul le_rfl (by omega)
        omega
      · -- same quotient, so the last digits decide, and `digitOf` is increasing
        have h1 := Nat.div_add_mod n D.card
        have h2 := Nat.div_add_mod m D.card
        have hmodlt : n % D.card < m % D.card := by
          rw [heq] at h1
          omega
        have hdd := digitOf_lt hmodlt (Nat.mod_lt _ (by omega))
        rw [heq] at hrn
        omega
  exact fun n m hnm => key m n hnm

/-- Blueprint: `thm:enum-bij`.  Proposition 2.5(i) of the paper: `enum` is the
increasing enumeration of the Cantor set. -/
theorem range_enum (h : Standing b D) : Set.range (enum b D) = cantorSet b D := by
  have hb : 1 < b := by have := h.three_le_base; omega
  have hcard : 1 < D.card := by have := h.two_le_card; omega
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨n, rfl⟩
    exact enum_mem_cantorSet h n
  · intro k hk
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact ⟨0, by simp⟩
      · have hdig : Nat.digits b k = k % b :: Nat.digits b (k / b) := Nat.digits_def' hb hk0
        have hmemD : k % b ∈ D := hk _ (by rw [hdig]; exact List.mem_cons_self)
        have htail : k / b ∈ cantorSet b D := by
          intro d hd
          exact hk d (by rw [hdig]; exact List.mem_cons_of_mem _ hd)
        obtain ⟨m, hm⟩ := ih (k / b) (Nat.div_lt_self hk0 hb) htail
        obtain ⟨c, hc, hcd⟩ := exists_digitOf_eq hmemD
        refine ⟨D.card * m + c, ?_⟩
        rw [enum_mul_add h _ hc, hm, hcd]
        exact Nat.div_add_mod k b

/-! ### The block structure -/

/-- Blueprint: `lem:enum-block`.  Proposition 2.5(ii) of the paper. -/
theorem enum_block (h : Standing b D) (i m j : ℕ) (hi : 1 ≤ i) (hj : j < D.card ^ i) :
    enum b D (D.card ^ i * m + j) = b ^ i * enum b D m + enum b D j := by
  have hcard : 1 < D.card := by have := h.two_le_card; omega
  -- the hypothesis `1 ≤ i` is not needed: the case `i = 0` is `j = 0`
  have key : ∀ i j : ℕ, j < D.card ^ i →
      enum b D (D.card ^ i * m + j) = b ^ i * enum b D m + enum b D j := by
    intro i
    induction i with
    | zero =>
      intro j hj
      have : j = 0 := by simpa using hj
      simp [this]
    | succ k ih =>
      intro j hj
      have hj' : j / D.card < D.card ^ k := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        calc j < D.card ^ (k + 1) := hj
          _ = D.card ^ k * D.card := by ring
      have hjmod : j % D.card < D.card := Nat.mod_lt _ (by omega)
      have hkey : D.card ^ (k + 1) * m + j
          = D.card * (D.card ^ k * m + j / D.card) + j % D.card := by
        calc D.card ^ (k + 1) * m + j
            = D.card ^ (k + 1) * m + (D.card * (j / D.card) + j % D.card) := by
              rw [Nat.div_add_mod]
          _ = D.card * (D.card ^ k * m + j / D.card) + j % D.card := by ring
      rw [hkey, enum_mul_add h _ hjmod, ih _ hj']
      have hjeq : enum b D j = b * enum b D (j / D.card) + digitOf D (j % D.card) :=
        enum_div_mod h j
      rw [hjeq]
      ring
  exact key i j hj

/-- Blueprint: `lem:growth`.  Used in the pair correlation chapter. -/
theorem enum_lt_pow (h : Standing b D) {n l : ℕ} (hn : n < D.card ^ l) :
    enum b D n < b ^ l := by
  have hcard : 1 < D.card := by have := h.two_le_card; omega
  have hb : 1 < b := by have := h.three_le_base; omega
  have key : ∀ l n : ℕ, n < D.card ^ l → enum b D n < b ^ l := by
    intro l
    induction l with
    | zero =>
      intro n hn
      have : n = 0 := by simpa using hn
      simp [this]
    | succ k ih =>
      intro n hn
      have hdlt : n / D.card < D.card ^ k := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        calc n < D.card ^ (k + 1) := hn
          _ = D.card ^ k * D.card := by ring
      have hA := ih _ hdlt
      have hd : digitOf D (n % D.card) < b :=
        h.lt_base _ (digitOf_mem (Nat.mod_lt _ (by omega)))
      have hrec := enum_div_mod h n
      have hstep : b * enum b D (n / D.card) + b ≤ b * b ^ k := by
        calc b * enum b D (n / D.card) + b = b * (enum b D (n / D.card) + 1) := by ring
          _ ≤ b * b ^ k := Nat.mul_le_mul le_rfl (by omega)
      have hpow : b ^ (k + 1) = b * b ^ k := by ring
      omega
  exact key l n hn

/-- `enum` carries the `|D|`-adic scale to the `b`-adic one from below as well:
`b ^ l ≤ enum b D (|D| ^ l)`.  This is what pins down the initial segments. -/
theorem pow_le_enum (h : Standing b D) (l : ℕ) : b ^ l ≤ enum b D (D.card ^ l) := by
  have hcard : 1 < D.card := by have := h.two_le_card; omega
  induction l with
  | zero =>
    have h1 : enum b D 1 = digitOf D 1 := enum_of_lt_card h (by omega)
    have h2 : digitOf D 1 ≠ 0 := digitOf_ne_zero h (by omega) (by omega)
    simp only [pow_zero] at *
    omega
  | succ k ih =>
    have key : D.card ^ (k + 1) = D.card * D.card ^ k + 0 := by ring
    rw [key, enum_mul_add h _ (by omega), digitOf_zero h]
    calc b ^ (k + 1) = b * b ^ k := by ring
      _ ≤ b * enum b D (D.card ^ k) := Nat.mul_le_mul le_rfl ih
      _ = b * enum b D (D.card ^ k) + 0 := by ring

/-- Sums of digits add across a single base `b` digit. -/
theorem sumDigits_mul_add (hb : 1 < b) (x : ℕ) {d : ℕ} (hd : d < b) :
    sumDigits b (b * x + d) = sumDigits b x + d := by
  rcases Nat.eq_zero_or_pos (b * x + d) with heq | hpos
  · have hx : x = 0 := by
      rcases Nat.eq_zero_or_pos x with h0 | h0
      · exact h0
      · exfalso; have := Nat.mul_pos (show 0 < b by omega) h0; omega
    have hd0 : d = 0 := by omega
    simp [hx, hd0, sumDigits]
  · have hmod : (b * x + d) % b = d := by
      rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hd
    have hdiv : (b * x + d) / b = x := by
      rw [Nat.mul_add_div (by omega), Nat.div_eq_of_lt hd]; omega
    rw [sumDigits, Nat.digits_def' hb hpos, hmod, hdiv, List.sum_cons, sumDigits]
    omega

/-- Sums of digits add across a block: if `Y < b ^ i` then the base `b` digits
of `b ^ i * X + Y` are those of `Y` followed by those of `X`. -/
theorem sumDigits_pow_mul_add (hb : 1 < b) {i X Y : ℕ} (hY : Y < b ^ i) :
    sumDigits b (b ^ i * X + Y) = sumDigits b X + sumDigits b Y := by
  have key : ∀ i Y : ℕ, Y < b ^ i →
      sumDigits b (b ^ i * X + Y) = sumDigits b X + sumDigits b Y := by
    intro i
    induction i with
    | zero =>
      intro Y hY
      have : Y = 0 := by simpa using hY
      simp [this, sumDigits]
    | succ k ih =>
      intro Y hY
      have hYd : Y / b < b ^ k := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        calc Y < b ^ (k + 1) := hY
          _ = b ^ k * b := by ring
      have hkey : b ^ (k + 1) * X + Y = b * (b ^ k * X + Y / b) + Y % b := by
        calc b ^ (k + 1) * X + Y = b ^ (k + 1) * X + (b * (Y / b) + Y % b) := by
              rw [Nat.div_add_mod]
          _ = b * (b ^ k * X + Y / b) + Y % b := by ring
      have hYsplit : sumDigits b Y = sumDigits b (Y / b) + Y % b := by
        conv_lhs => rw [← Nat.div_add_mod Y b]
        exact sumDigits_mul_add hb _ (Nat.mod_lt _ (by omega))
      rw [hkey, sumDigits_mul_add hb _ (Nat.mod_lt _ (by omega)), ih _ hYd, hYsplit]
      omega
  exact key i Y hY

/-- Blueprint: `lem:sumDigits-enum-block`. -/
theorem sumDigits_enum_block (h : Standing b D) (i m j : ℕ) (hi : 1 ≤ i)
    (hj : j < D.card ^ i) :
    sumDigits b (enum b D (D.card ^ i * m + j))
      = sumDigits b (enum b D m) + sumDigits b (enum b D j) := by
  rw [enum_block h i m j hi hj]
  exact sumDigits_pow_mul_add (by have := h.three_le_base; omega) (enum_lt_pow h hj)

/-- Blueprint: `lem:enum-initial`.  The first `|D| ^ ℓ` elements of the Cantor
set are exactly its elements below `b ^ ℓ`. -/
theorem enum_image_Iio (h : Standing b D) (l : ℕ) :
    enum b D '' (Set.Iio (D.card ^ l)) = cantorSet b D ∩ Set.Iio (b ^ l) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨n, hn, rfl⟩
    exact ⟨enum_mem_cantorSet h n, enum_lt_pow h hn⟩
  · rintro k ⟨hk, hklt⟩
    obtain ⟨n, rfl⟩ : k ∈ Set.range (enum b D) := by rw [range_enum h]; exact hk
    refine ⟨n, ?_, rfl⟩
    simp only [Set.mem_Iio]
    by_contra hcon
    simp only [not_lt] at hcon
    have h1 : enum b D (D.card ^ l) ≤ enum b D n := (enum_strictMono h).monotone hcon
    have h2 := pow_le_enum h l
    simp only [Set.mem_Iio] at hklt
    omega

/-! ### Divisibility -/

/-- A common divisor of all the digits divides the number they represent. -/
theorem dvd_ofDigits {s c : ℕ} {L : List ℕ} (hL : ∀ d ∈ L, s ∣ d) :
    s ∣ Nat.ofDigits c L := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [Nat.ofDigits_cons]
    refine Nat.dvd_add ?_ (Dvd.dvd.mul_left (ih fun d hd => hL d (List.mem_cons_of_mem _ hd)) c)
    simpa using hL a List.mem_cons_self

/-- Blueprint: `lem:stepSize-dvd`, first half. -/
theorem stepSize_dvd (h : Standing b D) {k : ℕ} (hk : k ∈ cantorSet b D) :
    stepSize D ∣ k := by
  conv_rhs => rw [← Nat.ofDigits_digits b k]
  exact dvd_ofDigits fun d hd => Finset.gcd_dvd (hk d hd)

/-- Blueprint: `lem:stepSize-dvd`, second half. -/
theorem stepSize_dvd_sumDigits (h : Standing b D) {k : ℕ} (hk : k ∈ cantorSet b D) :
    stepSize D ∣ sumDigits b k := by
  rw [sumDigits]
  exact List.dvd_sum fun d hd => Finset.gcd_dvd (hk d hd)

/-- Blueprint: `lem:b-sub-one-dvd`.  `k ≡ s_b k [MOD b - 1]`, from Mathlib's
`Nat.modEq_digits_sum`. -/
theorem modEq_sumDigits (hb : 3 ≤ b) (n : ℕ) : n ≡ sumDigits b n [MOD b - 1] := by
  have hb1 : b % (b - 1) = 1 := by
    have h : b = (b - 1) + 1 := by omega
    calc b % (b - 1) = ((b - 1) + 1) % (b - 1) := by rw [← h]
    _ = 1 % (b - 1) := Nat.add_mod_left _ _
    _ = 1 := Nat.mod_eq_of_lt (by omega)
  exact Nat.modEq_digits_sum (b - 1) b hb1 n

end IntegerCantorSet
