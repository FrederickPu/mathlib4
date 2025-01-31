/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import Mathlib.Algebra.Group.Int
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Basic

#align_import data.int.basic from "leanprover-community/mathlib"@"00d163e35035c3577c1c79fa53b68de17781ffc1"

/-!
# The integers are a ring

This file contains the commutative ring instance on `ℤ`.

See note [foundational algebra order theory].
-/

namespace Int

instance instCommRingInt : CommRing ℤ where
  __ := instAddCommGroup
  __ := instCommSemigroupInt
  zero_mul := Int.zero_mul
  mul_zero := Int.mul_zero
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
  mul_one := Int.mul_one
  one_mul := Int.one_mul
  npow n x := x ^ n
  npow_zero _ := rfl
  npow_succ _ _ := rfl
  natCast := (·)
  natCast_zero := rfl
  natCast_succ _ := rfl
  intCast := (·)
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl

@[simp, norm_cast]
lemma cast_mul {α : Type*} [NonAssocRing α] : ∀ m n, ((m * n : ℤ) : α) = m * n := fun m => by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · induction m with
    | zero => simp
    | succ m ih => simp_all [add_mul]
  · induction m with
    | zero => simp
    | succ m ih => simp_all [add_mul]
#align int.cast_mul Int.cast_mulₓ -- dubious translation, type involves HasLiftT

@[simp, norm_cast] lemma cast_pow {R : Type*} [Ring R] (n : ℤ) (m : ℕ) :
    ↑(n ^ m) = (n ^ m : R) := by
  induction' m with m ih <;> simp [_root_.pow_succ, *]
#align int.cast_pow Int.cast_pow

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances like `Int.normedCommRing` being used to construct
these instances non-computably.
-/

instance instCommSemiring : CommSemiring ℤ := by infer_instance
instance instSemiring     : Semiring ℤ     := by infer_instance
instance instRingInt      : Ring ℤ         := by infer_instance
instance instDistrib      : Distrib ℤ      := by infer_instance

/-! ### Miscellaneous lemmas -/

lemma cast_Nat_cast {n : ℕ} {R : Type*} [AddGroupWithOne R] :
    (Int.cast (Nat.cast n) : R) = Nat.cast n :=
  Int.cast_natCast _

end Int

assert_not_exists Set.range
