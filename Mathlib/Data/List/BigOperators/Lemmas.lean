/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Sébastien Gouëzel, Alex J. Best
-/
import Mathlib.Algebra.BigOperators.List.Order
import Mathlib.Algebra.Group.Opposite
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Algebra.GroupWithZero.Commute
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Data.Int.Units

#align_import data.list.big_operators.lemmas from "leanprover-community/mathlib"@"f694c7dead66f5d4c80f446c796a5aad14707f0e"

/-! # Lemmas about `List.sum` and `List.prod` requiring extra algebra imports -/


open MulOpposite List

variable {ι α M N P M₀ G R : Type*}

namespace Commute

theorem list_sum_right [NonUnitalNonAssocSemiring R] (a : R) (l : List R)
    (h : ∀ b ∈ l, Commute a b) : Commute a l.sum := by
  induction' l with x xs ih
  · exact Commute.zero_right _
  · rw [List.sum_cons]
    exact (h _ <| mem_cons_self _ _).add_right (ih fun j hj => h _ <| mem_cons_of_mem _ hj)
#align commute.list_sum_right Commute.list_sum_right

theorem list_sum_left [NonUnitalNonAssocSemiring R] (b : R) (l : List R)
    (h : ∀ a ∈ l, Commute a b) : Commute l.sum b :=
  ((Commute.list_sum_right _ _) fun _x hx => (h _ hx).symm).symm
#align commute.list_sum_left Commute.list_sum_left

end Commute

namespace List

@[to_additive]
theorem prod_eq_one_iff [CanonicallyOrderedCommMonoid M] (l : List M) :
    l.prod = 1 ↔ ∀ x ∈ l, x = (1 : M) :=
  ⟨all_one_of_le_one_le_of_prod_eq_one fun _ _ => one_le _, fun h => by
    rw [List.eq_replicate.2 ⟨_, h⟩, prod_replicate, one_pow]; exact (length l); rfl⟩
#align list.prod_eq_one_iff List.prod_eq_one_iff
#align list.sum_eq_zero_iff List.sum_eq_zero_iff

section Monoid
variable [Monoid α]

@[simp] lemma prod_map_neg [HasDistribNeg α] (l : List α) :
    (l.map Neg.neg).prod = (-1) ^ l.length * l.prod := by
  induction l <;> simp [*, pow_succ, ((Commute.neg_one_left _).pow_left _).left_comm]
#align list.prod_map_neg List.prod_map_neg

@[to_additive]
theorem prod_isUnit : ∀ {L : List α}, (∀ m ∈ L, IsUnit m) → IsUnit L.prod
  | [], _ => by simp
  | h :: t, u => by
    simp only [List.prod_cons]
    exact IsUnit.mul (u h (mem_cons_self h t)) (prod_isUnit fun m mt => u m (mem_cons_of_mem h mt))
#align list.prod_is_unit List.prod_isUnit
#align list.sum_is_add_unit List.sum_isAddUnit

end Monoid

section CommMonoid
variable [CommMonoid α]

@[to_additive]
theorem prod_isUnit_iff {α : Type*} [CommMonoid α] {L : List α} :
    IsUnit L.prod ↔ ∀ m ∈ L, IsUnit m := by
  refine' ⟨fun h => _, prod_isUnit⟩
  induction' L with m L ih
  · exact fun m' h' => False.elim (not_mem_nil m' h')
  rw [prod_cons, IsUnit.mul_iff] at h
  exact fun m' h' => Or.elim (eq_or_mem_of_mem_cons h') (fun H => H.substr h.1) fun H => ih h.2 _ H
#align list.prod_is_unit_iff List.prod_isUnit_iff
#align list.sum_is_add_unit_iff List.sum_isAddUnit_iff

end CommMonoid

/-- If a product of integers is `-1`, then at least one factor must be `-1`. -/
theorem neg_one_mem_of_prod_eq_neg_one {l : List ℤ} (h : l.prod = -1) : (-1 : ℤ) ∈ l := by
  obtain ⟨x, h₁, h₂⟩ := exists_mem_ne_one_of_prod_ne_one (ne_of_eq_of_ne h (by decide))
  exact
    Or.resolve_left
        (Int.isUnit_iff.mp
          (prod_isUnit_iff.mp (h.symm ▸ IsUnit.neg isUnit_one : IsUnit l.prod) x h₁))
        h₂ ▸
      h₁
#align list.neg_one_mem_of_prod_eq_neg_one List.neg_one_mem_of_prod_eq_neg_one

/-- If all elements in a list are bounded below by `1`, then the length of the list is bounded
by the sum of the elements. -/
theorem length_le_sum_of_one_le (L : List ℕ) (h : ∀ i ∈ L, 1 ≤ i) : L.length ≤ L.sum := by
  induction' L with j L IH h; · simp
  rw [sum_cons, length, add_comm]
  exact Nat.add_le_add (h _ (mem_cons_self _ _)) (IH fun i hi => h i (mem_cons.2 (Or.inr hi)))
#align list.length_le_sum_of_one_le List.length_le_sum_of_one_le

theorem dvd_prod [CommMonoid M] {a} {l : List M} (ha : a ∈ l) : a ∣ l.prod := by
  let ⟨s, t, h⟩ := append_of_mem ha
  rw [h, prod_append, prod_cons, mul_left_comm]
  exact dvd_mul_right _ _
#align list.dvd_prod List.dvd_prod

theorem dvd_sum [NonUnitalSemiring R] {a} {l : List R} (h : ∀ x ∈ l, a ∣ x) : a ∣ l.sum := by
  induction' l with x l ih
  · exact dvd_zero _
  · rw [List.sum_cons]
    exact dvd_add (h _ (mem_cons_self _ _)) (ih fun x hx => h x (mem_cons_of_mem _ hx))
#align list.dvd_sum List.dvd_sum

section Alternating

variable [CommGroup α]

@[to_additive]
theorem alternatingProd_append :
    ∀ l₁ l₂ : List α,
      alternatingProd (l₁ ++ l₂) = alternatingProd l₁ * alternatingProd l₂ ^ (-1 : ℤ) ^ length l₁
  | [], l₂ => by simp
  | a :: l₁, l₂ => by
    simp_rw [cons_append, alternatingProd_cons, alternatingProd_append, length_cons, pow_succ',
      neg_mul, one_mul, zpow_neg, ← div_eq_mul_inv, div_div]
#align list.alternating_prod_append List.alternatingProd_append
#align list.alternating_sum_append List.alternatingSum_append

@[to_additive]
theorem alternatingProd_reverse :
    ∀ l : List α, alternatingProd (reverse l) = alternatingProd l ^ (-1 : ℤ) ^ (length l + 1)
  | [] => by simp only [alternatingProd_nil, one_zpow, reverse_nil]
  | a :: l => by
    simp_rw [reverse_cons, alternatingProd_append, alternatingProd_reverse,
      alternatingProd_singleton, alternatingProd_cons, length_reverse, length, pow_succ', neg_mul,
      one_mul, zpow_neg, inv_inv]
    rw [mul_comm, ← div_eq_mul_inv, div_zpow]
#align list.alternating_prod_reverse List.alternatingProd_reverse
#align list.alternating_sum_reverse List.alternatingSum_reverse

end Alternating

section MonoidWithZero
variable [MonoidWithZero M₀]

/-- If zero is an element of a list `L`, then `List.prod L = 0`. If the domain is a nontrivial
monoid with zero with no divisors, then this implication becomes an `iff`, see
`List.prod_eq_zero_iff`. -/
theorem prod_eq_zero {L : List M₀} (h : (0 : M₀) ∈ L) : L.prod = 0 := by
  induction' L with a L ihL
  · exact absurd h (not_mem_nil _)
  · rw [prod_cons]
    cases' mem_cons.1 h with ha hL
    exacts [mul_eq_zero_of_left ha.symm _, mul_eq_zero_of_right _ (ihL hL)]
#align list.prod_eq_zero List.prod_eq_zero

/-- Product of elements of a list `L` equals zero if and only if `0 ∈ L`. See also
`List.prod_eq_zero` for an implication that needs weaker typeclass assumptions. -/
@[simp]
theorem prod_eq_zero_iff [Nontrivial M₀] [NoZeroDivisors M₀] {L : List M₀} :
    L.prod = 0 ↔ (0 : M₀) ∈ L := by
  induction' L with a L ihL
  · simp only [prod_nil, one_ne_zero, not_mem_nil]
  · rw [prod_cons, mul_eq_zero, ihL, mem_cons, eq_comm]
#align list.prod_eq_zero_iff List.prod_eq_zero_iff

theorem prod_ne_zero [Nontrivial M₀] [NoZeroDivisors M₀] {L : List M₀} (hL : (0 : M₀) ∉ L) :
    L.prod ≠ 0 :=
  mt prod_eq_zero_iff.1 hL
#align list.prod_ne_zero List.prod_ne_zero

end MonoidWithZero

theorem sum_map_mul_left [NonUnitalNonAssocSemiring R] (L : List ι) (f : ι → R) (r : R) :
    (L.map fun b => r * f b).sum = r * (L.map f).sum :=
  sum_map_hom L f <| AddMonoidHom.mulLeft r
#align list.sum_map_mul_left List.sum_map_mul_left

theorem sum_map_mul_right [NonUnitalNonAssocSemiring R] (L : List ι) (f : ι → R) (r : R) :
    (L.map fun b => f b * r).sum = (L.map f).sum * r :=
  sum_map_hom L f <| AddMonoidHom.mulRight r
#align list.sum_map_mul_right List.sum_map_mul_right

end List

namespace MulOpposite

open List

variable [Monoid M]

theorem op_list_prod : ∀ l : List M, op l.prod = (l.map op).reverse.prod := by
  intro l; induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.prod_cons, List.map_cons, List.reverse_cons', List.prod_concat, op_mul, ih]
#align mul_opposite.op_list_prod MulOpposite.op_list_prod

theorem unop_list_prod (l : List Mᵐᵒᵖ) : l.prod.unop = (l.map unop).reverse.prod := by
  rw [← op_inj, op_unop, MulOpposite.op_list_prod, map_reverse, map_map, reverse_reverse,
    op_comp_unop, map_id]
#align mul_opposite.unop_list_prod MulOpposite.unop_list_prod

end MulOpposite

section MonoidHom

variable [Monoid M] [Monoid N]

/-- A morphism into the opposite monoid acts on the product by acting on the reversed elements. -/
theorem unop_map_list_prod {F : Type*} [FunLike F M Nᵐᵒᵖ] [MonoidHomClass F M Nᵐᵒᵖ]
    (f : F) (l : List M) :
    (f l.prod).unop = (l.map (MulOpposite.unop ∘ f)).reverse.prod := by
  rw [map_list_prod f l, MulOpposite.unop_list_prod, List.map_map]
#align unop_map_list_prod unop_map_list_prod

namespace MonoidHom

/-- A morphism into the opposite monoid acts on the product by acting on the reversed elements. -/
@[deprecated _root_.unop_map_list_prod]
protected theorem unop_map_list_prod (f : M →* Nᵐᵒᵖ) (l : List M) :
    (f l.prod).unop = (l.map (MulOpposite.unop ∘ f)).reverse.prod :=
  unop_map_list_prod f l
#align monoid_hom.unop_map_list_prod MonoidHom.unop_map_list_prod

end MonoidHom

end MonoidHom
