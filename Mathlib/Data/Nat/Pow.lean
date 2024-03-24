/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Algebra.GroupPower.Order

#align_import data.nat.pow from "leanprover-community/mathlib"@"3e00d81bdcbf77c8188bbd18f5524ddc3ed8cac6"

/-! # `Nat.pow`

Results on the power operation on natural numbers.
-/


namespace Nat
variable {m n x y : ℕ}

/-! ### `pow` -/

-- Porting note: the next two lemmas have moved into `Std`.
-- TODO: Rename `Nat.pow_le_pow_of_le_left` to `Nat.pow_le_pow_left`, protect it, remove the alias
-- TODO: Rename `Nat.pow_le_pow_of_le_right` to `Nat.pow_le_pow_right`, protect it, remove the alias

-- The global `pow_le_pow_left` needs an extra hypothesis `0 ≤ x`.

#align nat.pow_le_pow_of_le_left Nat.pow_le_pow_left
#align nat.pow_le_pow_of_le_right Nat.pow_le_pow_right

#align nat.pow_lt_pow_of_lt_right pow_lt_pow_right
#align nat.pow_lt_pow_succ Nat.pow_lt_pow_succ

#align nat.pow_right_strict_mono pow_right_strictMono
#align nat.pow_le_iff_lt_right pow_le_pow_iff_right
#align nat.pow_lt_iff_lt_right pow_lt_pow_iff_right

protected lemma pow_right_injective (hx : 2 ≤ x) : Function.Injective (x ^ ·) :=
  StrictMono.injective (pow_right_strictMono hx)
#align nat.pow_right_injective Nat.pow_right_injective

/-- See also `pow_left_strictMonoOn`. -/
protected theorem pow_left_strictMono (hn : n ≠ 0) : StrictMono (. ^ n : ℕ → ℕ) :=
  fun _ _ h ↦ Nat.pow_lt_pow_left h hn
#align nat.pow_left_strict_mono Nat.pow_left_strictMono

theorem mul_lt_mul_pow_succ {n a q : ℕ} (a0 : 0 < a) (q1 : 1 < q) : n * q < a * q ^ (n + 1) := by
  rw [Nat.pow_succ, ← mul_assoc, mul_lt_mul_right (zero_lt_one.trans q1)]
  exact lt_mul_of_one_le_of_lt (Nat.succ_le_iff.mpr a0) (Nat.lt_pow_self q1 n)
#align nat.mul_lt_mul_pow_succ Nat.mul_lt_mul_pow_succ

theorem _root_.StrictMono.nat_pow {n : ℕ} (hn : n ≠ 0) {f : ℕ → ℕ} (hf : StrictMono f) :
    StrictMono fun m => f m ^ n :=
  (Nat.pow_left_strictMono hn).comp hf
#align strict_mono.nat_pow StrictMono.nat_pow

protected theorem pow_le_pow_iff_left (hm : m ≠ 0) : x ^ m ≤ y ^ m ↔ x ≤ y :=
  pow_le_pow_iff_left (zero_le _) (zero_le _) hm
#align nat.pow_le_iff_le_left Nat.pow_le_pow_iff_left

protected theorem pow_lt_pow_iff_left (hm : m ≠ 0) : x ^ m < y ^ m ↔ x < y :=
  pow_lt_pow_iff_left (zero_le _) (zero_le _) hm
#align nat.pow_lt_iff_lt_left Nat.pow_lt_pow_iff_left

theorem pow_left_injective (hm : m ≠ 0) : Function.Injective fun x : ℕ => x ^ m :=
  (Nat.pow_left_strictMono hm).injective
#align nat.pow_left_injective Nat.pow_left_injective

theorem sq_sub_sq (a b : ℕ) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by
  rw [sq, sq]
  exact Nat.mul_self_sub_mul_self_eq a b
#align nat.sq_sub_sq Nat.sq_sub_sq

alias pow_two_sub_pow_two := sq_sub_sq
#align nat.pow_two_sub_pow_two Nat.pow_two_sub_pow_two

/-! ### `pow` and `mod` / `dvd` -/


theorem pow_mod (a b n : ℕ) : a ^ b % n = (a % n) ^ b % n := by
  induction' b with b ih
  rfl; simp [pow_succ, Nat.mul_mod, ih]
#align nat.pow_mod Nat.pow_mod

#align nat.mod_pow_succ Nat.mod_pow_succ
#align nat.pow_dvd_pow_iff_pow_le_pow Nat.pow_dvd_pow_iff_pow_le_pow
#align nat.pow_dvd_pow_iff_le_right Nat.pow_dvd_pow_iff_le_right
#align nat.pow_dvd_pow_iff_le_right' Nat.pow_dvd_pow_iff_le_right'

theorem not_pos_pow_dvd : ∀ {p k : ℕ} (_ : 1 < p) (_ : 1 < k), ¬p ^ k ∣ p
  | succ p, succ k, hp, hk, h =>
    have : succ p * succ p ^ k ∣ succ p * 1 := by simpa [pow_succ'] using h
    have : succ p ^ k ∣ 1 := Nat.dvd_of_mul_dvd_mul_left (succ_pos _) this
    have he : succ p ^ k = 1 := eq_one_of_dvd_one this
    have : k < succ p ^ k := lt_pow_self hp k
    have : k < 1 := by rwa [he] at this
    have : k = 0 := Nat.eq_zero_of_le_zero <| le_of_lt_succ this
    have : 1 < 1 := by rwa [this] at hk
    absurd this (by decide)
#align nat.not_pos_pow_dvd Nat.not_pos_pow_dvd

#align nat.pow_dvd_of_le_of_pow_dvd Nat.pow_dvd_of_le_of_pow_dvd
#align nat.dvd_of_pow_dvd Nat.dvd_of_pow_dvd
#align nat.pow_div Nat.pow_div

theorem lt_of_pow_dvd_right {p i n : ℕ} (hn : n ≠ 0) (hp : 2 ≤ p) (h : p ^ i ∣ n) : i < n := by
  rw [← pow_lt_pow_iff_right (succ_le_iff.1 hp)]
  exact lt_of_le_of_lt (le_of_dvd hn.bot_lt h) (lt_pow_self (succ_le_iff.mp hp) n)
#align nat.lt_of_pow_dvd_right Nat.lt_of_pow_dvd_right

end Nat

/-!
### Deprecated lemmas

Those lemmas have been deprecated on 2023-12-23.
-/

@[deprecated] alias Nat.pow_lt_pow_of_lt_left := Nat.pow_lt_pow_left
@[deprecated] alias Nat.pow_le_iff_le_left := Nat.pow_le_pow_iff_left
@[deprecated] alias Nat.pow_lt_pow_of_lt_right := pow_lt_pow_right
@[deprecated] protected alias Nat.pow_right_strictMono := pow_right_strictMono
@[deprecated] alias Nat.pow_le_iff_le_right := pow_le_pow_iff_right
@[deprecated] alias Nat.pow_lt_iff_lt_right := pow_lt_pow_iff_right

assert_not_exists Set.range
