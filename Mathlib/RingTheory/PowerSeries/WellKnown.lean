/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Fangming Li
-/
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.NatAntidiagonal

#align_import ring_theory.power_series.well_known from "leanprover-community/mathlib"@"8199f6717c150a7fe91c4534175f4cf99725978f"

/-!
# Definition of well-known power series

In this file we define the following power series:

* `PowerSeries.invUnitsSub`: given `u : Rˣ`, this is the series for `1 / (u - x)`.
  It is given by `∑ n, x ^ n /ₚ u ^ (n + 1)`.

* `PowerSeries.sin`, `PowerSeries.cos`, `PowerSeries.exp` : power series for sin, cosine, and
  exponential functions.
-/


namespace PowerSeries

section Ring

variable {R S : Type*} [Ring R] [Ring S]

/-- The power series for `1 / (u - x)`. -/
def invUnitsSub (u : Rˣ) : PowerSeries R :=
  mk fun n => 1 /ₚ u ^ (n + 1)
#align power_series.inv_units_sub PowerSeries.invUnitsSub

@[simp]
theorem coeff_invUnitsSub (u : Rˣ) (n : ℕ) : coeff R n (invUnitsSub u) = 1 /ₚ u ^ (n + 1) :=
  coeff_mk _ _
#align power_series.coeff_inv_units_sub PowerSeries.coeff_invUnitsSub

@[simp]
theorem constantCoeff_invUnitsSub (u : Rˣ) : constantCoeff R (invUnitsSub u) = 1 /ₚ u := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_invUnitsSub, zero_add, pow_one]
#align power_series.constant_coeff_inv_units_sub PowerSeries.constantCoeff_invUnitsSub

@[simp]
theorem invUnitsSub_mul_X (u : Rˣ) : invUnitsSub u * X = invUnitsSub u * C R u - 1 := by
  ext (_ | n)
  · simp
  · simp [n.succ_ne_zero, pow_succ]
set_option linter.uppercaseLean3 false in
#align power_series.inv_units_sub_mul_X PowerSeries.invUnitsSub_mul_X

@[simp]
theorem invUnitsSub_mul_sub (u : Rˣ) : invUnitsSub u * (C R u - X) = 1 := by
  simp [mul_sub, sub_sub_cancel]
#align power_series.inv_units_sub_mul_sub PowerSeries.invUnitsSub_mul_sub

theorem map_invUnitsSub (f : R →+* S) (u : Rˣ) :
    map f (invUnitsSub u) = invUnitsSub (Units.map (f : R →* S) u) := by
  ext
  simp only [← map_pow, coeff_map, coeff_invUnitsSub, one_divp]
  rfl

#align power_series.map_inv_units_sub PowerSeries.map_invUnitsSub

/-- Give `d : ℕ`. The power series for `1 / ((1 - x) ^ (d + 1))`. -/
def invOneSubPow (d : ℕ) : PowerSeries R :=
  mk fun n => Nat.choose (d + n) d

theorem invOneSubPow_zero_eq_invUnitsSub_one : invOneSubPow 0 = invUnitsSub (1 : Rˣ) := by
  rw [invOneSubPow, invUnitsSub]
  simp only [zero_add, Nat.choose_zero_right, Nat.cast_one, one_pow, divp_one]

theorem one_sub_inv_eq_invOneSubPow_zero {k : Type _} [Field k] :
    (1 - X : PowerSeries k)⁻¹ = invOneSubPow 0 := Eq.symm <| by
  rw [@eq_inv_iff_mul_eq_one k _ (invOneSubPow 0) (1 - X) <| show (constantCoeff k)
  (1 - X) ≠ 0 by simp only [map_sub, map_one, constantCoeff_X, sub_zero, ne_eq, one_ne_zero,
  not_false_eq_true], invOneSubPow_zero_eq_invUnitsSub_one]; exact invUnitsSub_mul_sub 1

theorem one_sub_inv {k : Type _} [Field k] :
    (1 - X : PowerSeries k)⁻¹ = mk fun (_ : ℕ) => 1 := by
  rw [one_sub_inv_eq_invOneSubPow_zero, invOneSubPow]
  simp only [zero_add, Nat.choose_zero_right, Nat.cast_one]

theorem one_sub_inv_pow_eq {k : Type _} [Field k] (d : ℕ) :
    (1 - X)⁻¹ ^ (d + 1) = (mk fun (n : ℕ) => Nat.choose (d + n) d : PowerSeries k) := by
  induction' d with d hd
  · simp only [Nat.zero_eq, zero_add, pow_one, Nat.choose_zero_right, Nat.cast_one]
    exact one_sub_inv
  · ring_nf; rw [hd, one_sub_inv, ext_iff]; exact λ n ↦ by
      rw [coeff_mul]; simp only [coeff_mk, one_mul]; rw [Nat.succ_add, Nat.choose_succ_succ,
      ← Finset.sum_antidiagonal_choose_add]; exact (Nat.cast_sum (Finset.antidiagonal n) fun x
      ↦ Nat.choose (d + x.2) d).symm

theorem one_sub_inv_pow_eq_invOneSubPow {k : Type _} [Field k] (d : ℕ) :
    (1 - X)⁻¹ ^ (d + 1) = (invOneSubPow d : PowerSeries k) := by
  rw [one_sub_inv_pow_eq]; rfl

theorem one_sub_pow_inv_eq {k : Type _} [Field k] (d : ℕ) :
    ((1 - X) ^ (d + 1))⁻¹ = (mk fun (n : ℕ) => Nat.choose (d + n) d : PowerSeries k) := by
  rw [← one_sub_inv_pow_eq, pow_inv_eq_inv_pow]

theorem one_sub_pow_inv_eq_invOneSubPow {k : Type _} [Field k] (d : ℕ) :
    ((1 - X) ^ (d + 1))⁻¹ = (invOneSubPow d : PowerSeries k) := by
  rw [one_sub_pow_inv_eq]; rfl

theorem invOneSubPow_mul_one_sub_pow {k : Type _} [Field k] (d : ℕ) :
    (invOneSubPow d : PowerSeries k) * ((1 - X) ^ (d + 1)) = 1 := by
  rw [← one_sub_pow_inv_eq_invOneSubPow]; simp only [map_pow, map_sub, map_one, constantCoeff_X,
  sub_zero, one_pow, ne_eq, one_ne_zero, not_false_eq_true, PowerSeries.inv_mul_cancel]

end Ring

section Field

variable (A A' : Type*) [Ring A] [Ring A'] [Algebra ℚ A] [Algebra ℚ A']

open Nat

/-- Power series for the exponential function at zero. -/
def exp : PowerSeries A :=
  mk fun n => algebraMap ℚ A (1 / n !)
#align power_series.exp PowerSeries.exp

/-- Power series for the sine function at zero. -/
def sin : PowerSeries A :=
  mk fun n => if Even n then 0 else algebraMap ℚ A ((-1) ^ (n / 2) / n !)
#align power_series.sin PowerSeries.sin

/-- Power series for the cosine function at zero. -/
def cos : PowerSeries A :=
  mk fun n => if Even n then algebraMap ℚ A ((-1) ^ (n / 2) / n !) else 0
#align power_series.cos PowerSeries.cos

variable {A A'} [Ring A] [Ring A'] [Algebra ℚ A] [Algebra ℚ A'] (n : ℕ) (f : A →+* A')

@[simp]
theorem coeff_exp : coeff A n (exp A) = algebraMap ℚ A (1 / n !) :=
  coeff_mk _ _
#align power_series.coeff_exp PowerSeries.coeff_exp

@[simp]
theorem constantCoeff_exp : constantCoeff A (exp A) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_exp]
  simp
#align power_series.constant_coeff_exp PowerSeries.constantCoeff_exp

set_option linter.deprecated false in
@[simp]
theorem coeff_sin_bit0 : coeff A (bit0 n) (sin A) = 0 := by
  rw [sin, coeff_mk, if_pos (even_bit0 n)]
#align power_series.coeff_sin_bit0 PowerSeries.coeff_sin_bit0

set_option linter.deprecated false in
@[simp]
theorem coeff_sin_bit1 : coeff A (bit1 n) (sin A) = (-1) ^ n * coeff A (bit1 n) (exp A) := by
  rw [sin, coeff_mk, if_neg n.not_even_bit1, Nat.bit1_div_two, ← mul_one_div, map_mul, map_pow,
    map_neg, map_one, coeff_exp]
#align power_series.coeff_sin_bit1 PowerSeries.coeff_sin_bit1

set_option linter.deprecated false in
@[simp]
theorem coeff_cos_bit0 : coeff A (bit0 n) (cos A) = (-1) ^ n * coeff A (bit0 n) (exp A) := by
  rw [cos, coeff_mk, if_pos (even_bit0 n), Nat.bit0_div_two, ← mul_one_div, map_mul, map_pow,
    map_neg, map_one, coeff_exp]
#align power_series.coeff_cos_bit0 PowerSeries.coeff_cos_bit0

set_option linter.deprecated false in
@[simp]
theorem coeff_cos_bit1 : coeff A (bit1 n) (cos A) = 0 := by
  rw [cos, coeff_mk, if_neg n.not_even_bit1]
#align power_series.coeff_cos_bit1 PowerSeries.coeff_cos_bit1

@[simp]
theorem map_exp : map (f : A →+* A') (exp A) = exp A' := by
  ext
  simp
#align power_series.map_exp PowerSeries.map_exp

@[simp]
theorem map_sin : map f (sin A) = sin A' := by
  ext
  simp [sin, apply_ite f]
#align power_series.map_sin PowerSeries.map_sin

@[simp]
theorem map_cos : map f (cos A) = cos A' := by
  ext
  simp [cos, apply_ite f]
#align power_series.map_cos PowerSeries.map_cos

end Field

open RingHom

open Finset Nat

variable {A : Type*} [CommRing A]

/-- Shows that $e^{aX} * e^{bX} = e^{(a + b)X}$ -/
theorem exp_mul_exp_eq_exp_add [Algebra ℚ A] (a b : A) :
    rescale a (exp A) * rescale b (exp A) = rescale (a + b) (exp A) := by
  ext n
  simp only [coeff_mul, exp, rescale, coeff_mk, MonoidHom.coe_mk, OneHom.coe_mk, coe_mk,
    factorial, Nat.sum_antidiagonal_eq_sum_range_succ_mk, add_pow, sum_mul]
  apply sum_congr rfl
  rintro x hx
  suffices
    a ^ x * b ^ (n - x) *
        (algebraMap ℚ A (1 / ↑x.factorial) * algebraMap ℚ A (1 / ↑(n - x).factorial)) =
      a ^ x * b ^ (n - x) * (↑(n.choose x) * (algebraMap ℚ A) (1 / ↑n.factorial))
    by convert this using 1 <;> ring
  congr 1
  rw [← map_natCast (algebraMap ℚ A) (n.choose x), ← map_mul, ← map_mul]
  refine' RingHom.congr_arg _ _
  rw [mul_one_div (↑(n.choose x) : ℚ), one_div_mul_one_div]
  symm
  rw [div_eq_iff, div_mul_eq_mul_div, one_mul, choose_eq_factorial_div_factorial]
  norm_cast
  rw [cast_div_charZero]
  · apply factorial_mul_factorial_dvd_factorial (mem_range_succ_iff.1 hx)
  · apply mem_range_succ_iff.1 hx
  · rintro h
    apply factorial_ne_zero n
    rw [cast_eq_zero.1 h]
#align power_series.exp_mul_exp_eq_exp_add PowerSeries.exp_mul_exp_eq_exp_add

/-- Shows that $e^{x} * e^{-x} = 1$ -/
theorem exp_mul_exp_neg_eq_one [Algebra ℚ A] : exp A * evalNegHom (exp A) = 1 := by
  convert exp_mul_exp_eq_exp_add (1 : A) (-1) <;> simp
#align power_series.exp_mul_exp_neg_eq_one PowerSeries.exp_mul_exp_neg_eq_one

/-- Shows that $(e^{X})^k = e^{kX}$. -/
theorem exp_pow_eq_rescale_exp [Algebra ℚ A] (k : ℕ) : exp A ^ k = rescale (k : A) (exp A) := by
  induction' k with k h
  · simp only [rescale_zero, constantCoeff_exp, Function.comp_apply, map_one, cast_zero, zero_eq,
      pow_zero (exp A), coe_comp]
  · simpa only [succ_eq_add_one, cast_add, ← exp_mul_exp_eq_exp_add (k : A), ← h, cast_one,
    id_apply, rescale_one] using pow_succ' (exp A) k
#align power_series.exp_pow_eq_rescale_exp PowerSeries.exp_pow_eq_rescale_exp

/-- Shows that
$\sum_{k = 0}^{n - 1} (e^{X})^k = \sum_{p = 0}^{\infty} \sum_{k = 0}^{n - 1} \frac{k^p}{p!}X^p$. -/
theorem exp_pow_sum [Algebra ℚ A] (n : ℕ) :
    ((Finset.range n).sum fun k => exp A ^ k) =
      PowerSeries.mk fun p => (Finset.range n).sum
        fun k => (k ^ p : A) * algebraMap ℚ A p.factorial⁻¹ := by
  simp only [exp_pow_eq_rescale_exp, rescale]
  ext
  simp only [one_div, coeff_mk, cast_pow, coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    coeff_exp, factorial, map_sum]
#align power_series.exp_pow_sum PowerSeries.exp_pow_sum

end PowerSeries
