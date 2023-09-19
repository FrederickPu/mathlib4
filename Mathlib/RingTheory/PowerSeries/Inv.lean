/-
Copyright (c) 2023 Richard M. Hill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard M. Hill
-/
import Mathlib.RingTheory.PowerSeries.Comp
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
In this file we prove, for a commutative ring `R`, that
a power series `f : R⟦X⟧` is a unit if and only if its constant term
is a unit.

## Main result

- `PowerSeries.isUnit_iff` : a power series is a unit iff its
                                constant term is a unit.

(To be moved to `PowerSeries.WellKnown`.)
-/

open PowerSeries BigOperators Polynomial


-- variable {R} [CommRing R]

namespace PowerSeries


/--The power series `∑ (a * X) ^ n`.-/
-- def geometricSeries (a : R) := mk fun n ↦ a^n

-- theorem one_sub_smul_X_mul_geometric_series_eq_one {a} :
--     ((1: R⟦X⟧) - a • X) * geometricSeries a = 1 := by
--   ext n
--   rw [sub_mul, map_sub, smul_mul_assoc, map_smul,
--     one_mul, smul_eq_mul, coeff_one]
--   cases n with
--   | zero =>
--     rw [geometricSeries, coeff_mk, pow_zero,
--       coeff_zero_eq_constantCoeff, map_mul, constantCoeff_X,
--       zero_mul, mul_zero, sub_zero, if_pos rfl]
--   | succ n =>
--     rw [geometricSeries, coeff_mk, if_neg n.succ_ne_zero,
--       pow_succ, coeff_succ_X_mul, coeff_mk, sub_self]

-- theorem one_add_smul_X_mul_geometric_series_eq_one {a} :
--     ((1 : R⟦X⟧) + a • X) * geometricSeries (-a) = 1 := by
--   have := one_sub_smul_X_mul_geometric_series_eq_one (a := -a)
--   rwa [neg_smul, sub_neg_eq_add] at this

-- theorem C_unit_add_X_mul_inv_smul_geometricSeries_eq_one (a : Rˣ) :
--     (C R a + X : R⟦X⟧) * (a.inv • geometricSeries (-a.inv)) = 1 := by
--   rw [smul_eq_C_mul, ←mul_assoc, add_mul, ←map_mul, Units.inv_eq_val_inv, Units.mul_inv,
--     map_one, mul_comm X, ←smul_eq_C_mul]
--   apply one_add_smul_X_mul_geometric_series_eq_one

-- theorem isUnit_C_unit_add_X (a : Rˣ) : IsUnit (C R a + X) := by
--   set inverse := mk (λ n ↦ (-a)^n)
--   apply isUnit_of_mul_eq_one
--   apply C_unit_add_X_mul_inv_smul_geometricSeries_eq_one

-- private lemma constantCoeff_sub_C_self {f} : constantCoeff R (f - C R (constantCoeff R f)) = 0 := by
--   rw [map_sub, constantCoeff_C, sub_self]

-- private lemma eq_C_add_X_comp (f) :
--   f = (C R (constantCoeff R f) + X) ∘ᶠ (f - C R (constantCoeff R f)) := by
--   rw [add_comp, X_comp, C_comp, add_sub_cancel'_right]
--   all_goals
--     exact hasComp_of_constantCoeff_eq_zero constantCoeff_sub_C_self



@[simp] theorem isUnit_iff {R} [CommRing R] {f} : (IsUnit f) ↔ IsUnit (constantCoeff R f) := by
  constructor
  · intro hf
    obtain ⟨g,hg⟩ := hf
    apply isUnit_of_mul_eq_one (b := constantCoeff R g.inv)
    rw [←hg, ←map_mul, Units.inv_eq_val_inv, Units.mul_inv, map_one]
  · intro hf
    obtain ⟨a : Rˣ,ha⟩ := hf
    have hf : f = (C R a - X) ∘ᶠ (C R a - f)
    · rw [sub_comp C_hasComp X_hasComp, C_comp, X_comp, sub_sub_cancel]
    have := invUnitsSub_mul_sub a
    have : f * (invUnitsSub a) ∘ᶠ (C R a - f) = 1
    · nth_rw 1 [hf]
      rw [←mul_comp, mul_comm, invUnitsSub_mul_sub, one_comp] <;>
      · apply hasComp_of_constantCoeff_eq_zero
        rw [map_sub, constantCoeff_C, ha, sub_self]
    apply isUnit_of_mul_eq_one (h := this)

end PowerSeries
