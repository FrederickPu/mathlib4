/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Bitwise

#align_import data.nat.order.basic from "leanprover-community/mathlib"@"3ed3f98a1e836241990d3d308f1577e434977130"


/-!
# The natural numbers as a linearly ordered commutative semiring

We also have a variety of lemmas which have been deferred from `Data.Nat.Basic` because it is
easier to prove them with this ordered semiring instance available.

### TODO

Move most of the theorems to `Data.Nat.Defs` by modifying their proofs.
-/


universe u v

namespace Nat
variable {m n : ℕ}

/-! ### instances -/

instance orderBot : OrderBot ℕ where
  bot := 0
  bot_le := Nat.zero_le
#align nat.order_bot Nat.orderBot

instance linearOrderedCommSemiring : LinearOrderedCommSemiring ℕ :=
  { Nat.commSemiring, Nat.linearOrder with
    lt := Nat.lt, add_le_add_left := @Nat.add_le_add_left,
    le_of_add_le_add_left := @Nat.le_of_add_le_add_left,
    zero_le_one := Nat.le_of_lt (Nat.zero_lt_succ 0),
    mul_lt_mul_of_pos_left := @Nat.mul_lt_mul_of_pos_left,
    mul_lt_mul_of_pos_right := @Nat.mul_lt_mul_of_pos_right,
    exists_pair_ne := ⟨0, 1, ne_of_lt Nat.zero_lt_one⟩ }

instance linearOrderedCommMonoidWithZero : LinearOrderedCommMonoidWithZero ℕ :=
  { Nat.linearOrderedCommSemiring, (inferInstance : CommMonoidWithZero ℕ) with
    mul_le_mul_left := fun _ _ h c => Nat.mul_le_mul_left c h }

/-! Extra instances to short-circuit type class resolution and ensure computability -/


-- Not using `inferInstance` avoids `Classical.choice` in the following two
instance linearOrderedSemiring : LinearOrderedSemiring ℕ :=
  inferInstance

instance strictOrderedSemiring : StrictOrderedSemiring ℕ :=
  inferInstance

instance strictOrderedCommSemiring : StrictOrderedCommSemiring ℕ :=
  inferInstance

instance orderedSemiring : OrderedSemiring ℕ :=
  StrictOrderedSemiring.toOrderedSemiring'

instance orderedCommSemiring : OrderedCommSemiring ℕ :=
  StrictOrderedCommSemiring.toOrderedCommSemiring'

instance linearOrderedCancelAddCommMonoid : LinearOrderedCancelAddCommMonoid ℕ :=
  inferInstance

instance canonicallyOrderedCommSemiring : CanonicallyOrderedCommSemiring ℕ :=
  { Nat.nontrivial, Nat.orderBot, (inferInstance : OrderedAddCommMonoid ℕ),
    (inferInstance : LinearOrderedSemiring ℕ), (inferInstance : CommSemiring ℕ) with
    exists_add_of_le := fun {_ _} h => (Nat.le.dest h).imp fun _ => Eq.symm,
    le_self_add := Nat.le_add_right,
    eq_zero_or_eq_zero_of_mul_eq_zero := Nat.eq_zero_of_mul_eq_zero }

instance canonicallyLinearOrderedAddCommMonoid : CanonicallyLinearOrderedAddCommMonoid ℕ :=
  { (inferInstance : CanonicallyOrderedAddCommMonoid ℕ), Nat.linearOrder with }

variable {m n k l : ℕ}

/-! ### Equalities and inequalities involving zero and one -/

theorem _root_.NeZero.one_le [NeZero n] : 1 ≤ n := one_le_iff_ne_zero.mpr (NeZero.ne n)

/-! ### `sub`

Most lemmas come from the `OrderedSub` instance on `ℕ`. -/


instance : OrderedSub ℕ := by
  constructor
  intro m n k
  induction' n with n ih generalizing k
  · simp
  · simp only [sub_succ, pred_le_iff, ih, succ_add, add_succ]

/-! ### `bit0` and `bit1` -/
section Bit

set_option linter.deprecated false

protected theorem bit0_le {n m : ℕ} (h : n ≤ m) : bit0 n ≤ bit0 m :=
  add_le_add h h
#align nat.bit0_le Nat.bit0_le

protected theorem bit1_le {n m : ℕ} (h : n ≤ m) : bit1 n ≤ bit1 m :=
  succ_le_succ (add_le_add h h)
#align nat.bit1_le Nat.bit1_le

theorem bit_le : ∀ (b : Bool) {m n : ℕ}, m ≤ n → bit b m ≤ bit b n
  | true, _, _, h => Nat.bit1_le h
  | false, _, _, h => Nat.bit0_le h
#align nat.bit_le Nat.bit_le

theorem bit0_le_bit : ∀ (b) {m n : ℕ}, m ≤ n → bit0 m ≤ bit b n
  | true, _, _, h => le_of_lt <| Nat.bit0_lt_bit1 h
  | false, _, _, h => Nat.bit0_le h
#align nat.bit0_le_bit Nat.bit0_le_bit

theorem bit_le_bit1 : ∀ (b) {m n : ℕ}, m ≤ n → bit b m ≤ bit1 n
  | false, _, _, h => le_of_lt <| Nat.bit0_lt_bit1 h
  | true, _, _, h => Nat.bit1_le h
#align nat.bit_le_bit1 Nat.bit_le_bit1

theorem bit_lt_bit0 : ∀ (b) {m n : ℕ}, m < n → bit b m < bit0 n
  | true, _, _, h => Nat.bit1_lt_bit0 h
  | false, _, _, h => Nat.bit0_lt h
#align nat.bit_lt_bit0 Nat.bit_lt_bit0

theorem bit_lt_bit (a b) (h : m < n) : bit a m < bit b n :=
  lt_of_lt_of_le (bit_lt_bit0 _ h) (bit0_le_bit _ le_rfl)
#align nat.bit_lt_bit Nat.bit_lt_bit

@[simp]
theorem bit0_le_bit1_iff : bit0 m ≤ bit1 n ↔ m ≤ n :=
  ⟨fun h => by
    rwa [← Nat.lt_succ_iff, n.bit1_eq_succ_bit0,
    ← n.bit0_succ_eq, bit0_lt_bit0, Nat.lt_succ_iff] at h,
    fun h => le_of_lt (Nat.bit0_lt_bit1 h)⟩
#align nat.bit0_le_bit1_iff Nat.bit0_le_bit1_iff

@[simp]
theorem bit0_lt_bit1_iff : bit0 m < bit1 n ↔ m ≤ n :=
  ⟨fun h => bit0_le_bit1_iff.1 (le_of_lt h), Nat.bit0_lt_bit1⟩
#align nat.bit0_lt_bit1_iff Nat.bit0_lt_bit1_iff

@[simp]
theorem bit1_le_bit0_iff : bit1 m ≤ bit0 n ↔ m < n :=
  ⟨fun h => by rwa [m.bit1_eq_succ_bit0, succ_le_iff, bit0_lt_bit0] at h, fun h =>
    le_of_lt (Nat.bit1_lt_bit0 h)⟩
#align nat.bit1_le_bit0_iff Nat.bit1_le_bit0_iff

@[simp]
theorem bit1_lt_bit0_iff : bit1 m < bit0 n ↔ m < n :=
  ⟨fun h => bit1_le_bit0_iff.1 (le_of_lt h), Nat.bit1_lt_bit0⟩
#align nat.bit1_lt_bit0_iff Nat.bit1_lt_bit0_iff

-- Porting note: temporarily porting only needed portions
/-
@[simp]
theorem one_le_bit0_iff : 1 ≤ bit0 n ↔ 0 < n := by
  convert bit1_le_bit0_iff
  rfl
#align nat.one_le_bit0_iff Nat.one_le_bit0_iff

@[simp]
theorem one_lt_bit0_iff : 1 < bit0 n ↔ 1 ≤ n := by
  convert bit1_lt_bit0_iff
  rfl
#align nat.one_lt_bit0_iff Nat.one_lt_bit0_iff

@[simp]
theorem bit_le_bit_iff : ∀ {b : Bool}, bit b m ≤ bit b n ↔ m ≤ n
  | false => bit0_le_bit0
  | true => bit1_le_bit1
#align nat.bit_le_bit_iff Nat.bit_le_bit_iff

@[simp]
theorem bit_lt_bit_iff : ∀ {b : Bool}, bit b m < bit b n ↔ m < n
  | false => bit0_lt_bit0
  | true => bit1_lt_bit1
#align nat.bit_lt_bit_iff Nat.bit_lt_bit_iff

@[simp]
theorem bit_le_bit1_iff : ∀ {b : Bool}, bit b m ≤ bit1 n ↔ m ≤ n
  | false => bit0_le_bit1_iff
  | true => bit1_le_bit1
#align nat.bit_le_bit1_iff Nat.bit_le_bit1_iff
-/

end Bit

end Nat
