/-
Definitions for the formalization of
"Integer Cantor Sets: Arithmetic Combinatorial Properties"
by Burgin, Fragkos, Lacey, Mena and Reguera.

Blueprint: `blueprint/src/content.tex`, Chapter 2.
-/
import Mathlib

namespace IntegerCantorSet

open Finset

/-- The integer Cantor set with base `b` and digit set `D`: the naturals all of
whose base `b` digits lie in `D`.

Note `0 ∈ cantorSet b D` always, since `Nat.digits b 0 = []`.

Blueprint: `def:cantorSet`. -/
def cantorSet (b : ℕ) (D : Finset ℕ) : Set ℕ :=
  {n | ∀ d ∈ Nat.digits b n, d ∈ D}

/-- The standing assumption of the paper: `b ≥ 3`, `D ⊆ {0,...,b-1}`, `0 ∈ D`,
and `2 ≤ |D| < b`.

Blueprint: `def:standing`. -/
structure Standing (b : ℕ) (D : Finset ℕ) : Prop where
  three_le_base : 3 ≤ b
  lt_base : ∀ d ∈ D, d < b
  zero_mem : 0 ∈ D
  two_le_card : 2 ≤ D.card
  card_lt_base : D.card < b

/-- The base `b` sum of digits function.

Blueprint: `def:sumDigits`. -/
def sumDigits (b n : ℕ) : ℕ := (Nat.digits b n).sum

/-- The step size `s = gcd D`.  Under the standing assumption this is the
largest `s` with `D` contained in an arithmetic progression of step `s`,
because `0 ∈ D`.

Blueprint: `def:stepSize`. -/
def stepSize (D : Finset ℕ) : ℕ := D.gcd id

/-- `digitOf D i` is the `i`-th smallest element of `D`, with junk value `0`
for `i ≥ D.card`.

Blueprint: `def:digitOf`. -/
def digitOf (D : Finset ℕ) (i : ℕ) : ℕ := (D.sort (· ≤ ·)).getD i 0

/-- The increasing enumeration `κ` of `cantorSet b D`: read `n` in base `|D|`
and replace each digit `c` by `digitOf D c`.

That this really is the increasing enumeration is `range_enum`, and it is
exactly where `0 ∈ D` is used.

Blueprint: `def:enum`. -/
def enum (b : ℕ) (D : Finset ℕ) (n : ℕ) : ℕ :=
  Nat.ofDigits b ((Nat.digits D.card n).map (digitOf D))

end IntegerCantorSet
