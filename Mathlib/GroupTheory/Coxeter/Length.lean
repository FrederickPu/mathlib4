/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Parity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Group

/-!
# The length function and reduced words
Throughout this file, `B` is a type and `M : Matrix B B ℕ` is a Coxeter matrix.
`cs : CoxeterSystem M W` is a Coxeter system; that is, `W` is a group, and `cs` holds the data
of a group isomorphism `W ≃* Matrix.CoxeterGroup M`, where `Matrix.CoxeterGroup M` refers to
the quotient of the free group on `B` by the Coxeter relations given by the matrix `M`. See
`Mathlib.GroupTheory.Coxeter.Basic` for more details.

We define the length function $\ell : W → \mathbb{N}$, and we prove that
$\ell (w_1 w_2) \leq \ell (w_1) + \ell (w_2)$
and that $\ell (w_1 w_2)$ and $\ell (w_1) + \ell (w_2)$ have the same parity.

We define a *reduced word* for an element $w \in W$ to be a way of writing $w$ as a product
of exactly $\ell(w)$ simple reflections. Every element of $W$ has a reduced word.

## Main definitions
* `cs.length`

## References
* [A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*](bjorner2005)
-/

noncomputable section

namespace CoxeterSystem

open List Matrix Function CoxeterSystem

variable {B : Type*} [DecidableEq B]
variable {M : Matrix B B ℕ}
variable {W : Type*} [Group W]
variable (cs : CoxeterSystem M W)

local prefix:100 "s" => cs.simpleReflection
local prefix:100 "π" => cs.wordProd

/-! ### Length -/

private local instance (w : W) : DecidablePred (fun n ↦ ∃ ω : List B, ω.length = n ∧ π ω = w) :=
  Classical.decPred _

private theorem exists_word_with_prod (w : W) : ∃ n : ℕ, ∃ ω : List B, ω.length = n ∧ π ω = w := by
  rcases cs.wordProd_surjective w with ⟨ω, rfl⟩
  use ω.length, ω

/-- The length of `w`; i.e., the minimum number of simple reflections that
must be multiplied to form `w`. -/
def length (w : W) : ℕ := Nat.find (cs.exists_word_with_prod w)
local prefix:100 "ℓ" => cs.length

theorem exists_reduced_word (w : W) : ∃ ω : List B, ω.length = ℓ w ∧ w = π ω := by
  have := Nat.find_spec (cs.exists_word_with_prod w)
  tauto

theorem length_wordProd_le (ω : List B) : ℓ (π ω) ≤ ω.length := by
  apply Nat.find_min' (cs.exists_word_with_prod (π ω))
  use ω

@[simp] theorem length_one : ℓ (1 : W) = 0 := Nat.eq_zero_of_le_zero (cs.length_wordProd_le [])

theorem length_eq_zero_iff {w : W} : ℓ w = 0 ↔ w = 1 := by
  constructor
  · intro h
    rcases cs.exists_reduced_word w with ⟨ω, hω, rfl⟩
    have : ω = [] := eq_nil_of_length_eq_zero (hω.trans h)
    rw [this]
    simp
  · rintro rfl
    exact cs.length_one

@[simp] theorem length_inv (w : W) : ℓ (w⁻¹) = ℓ w := by
  apply Nat.le_antisymm
  · rcases cs.exists_reduced_word w with ⟨ω, hω, rfl⟩
    have := cs.length_wordProd_le (List.reverse ω)
    simp at this
    rwa [hω] at this
  · rcases cs.exists_reduced_word w⁻¹ with ⟨ω, hω, h'ω⟩
    have := cs.length_wordProd_le (List.reverse ω)
    simp at this
    rwa [← h'ω, hω, inv_inv] at this

theorem length_mul_le (w₁ w₂ : W) :
    ℓ (w₁ * w₂) ≤ ℓ w₁ + ℓ w₂ := by
  rcases cs.exists_reduced_word w₁ with ⟨ω₁, hω₁, rfl⟩
  rcases cs.exists_reduced_word w₂ with ⟨ω₂, hω₂, rfl⟩
  have := cs.length_wordProd_le (ω₁ ++ ω₂)
  simp at this
  rwa [hω₁, hω₂] at this

theorem length_mul_ge (w₁ w₂ : W) :
    ℓ (w₁ * w₂) ≥ max (ℓ w₁ - ℓ w₂) (ℓ w₂ - ℓ w₁) := by
  apply max_le_iff.mpr
  constructor
  · apply Nat.sub_le_of_le_add
    have := cs.length_mul_le (w₁ * w₂) w₂⁻¹
    simp at this
    assumption
  · apply Nat.sub_le_of_le_add
    have := cs.length_mul_le (w₁ * w₂)⁻¹ w₁
    simp only [length_inv] at this
    simp at this
    assumption

private def lengthParity (cs : CoxeterSystem M W) : W →* Multiplicative (ZMod 2) := cs.lift (
    show IsLiftable M (fun _ ↦ Multiplicative.ofAdd 1) by
      intro i i'
      dsimp
      rw [← ofAdd_add, one_add_one_eq_two, (by decide : (2 : ZMod 2) = 0)]
      simp
  )

private theorem lengthParity_simple :
    ⇑(CoxeterSystem.lengthParity cs) ∘ simpleReflection cs = fun _ ↦ Multiplicative.ofAdd 1 := by
  ext x
  dsimp
  rw [lengthParity, lift_apply_simple]

private theorem parity_length_eq' (w : W) :
    Multiplicative.toAdd (cs.lengthParity w) = ((↑) : ℕ → ZMod 2) (ℓ w) := by
  rcases cs.exists_reduced_word w with ⟨ω, hω, rfl⟩
  nth_rw 1 [wordProd]
  rw [MonoidHom.map_list_prod, List.map_map, lengthParity_simple,
      map_const', prod_replicate, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, mul_one]
  tauto

theorem length_mul_mod_two (w₁ w₂ : W) : ℓ (w₁ * w₂) % 2 = (ℓ w₁ + ℓ w₂) % 2 := by
  rw [← ZMod.nat_cast_eq_nat_cast_iff']
  rw [(by simp : (↑(length cs w₁ + length cs w₂) : ZMod 2) = ↑(length cs w₁) + ↑(length cs w₂))]
  repeat rw [← parity_length_eq']
  simp

@[simp] theorem length_simple (i : B) : ℓ (s i) = 1 := by
  apply Nat.le_antisymm
  · show length cs (s i) ≤ 1
    have := cs.length_wordProd_le [i]
    simp at this
    tauto
  · show 1 ≤ length cs (s i)
    by_contra! length_lt_1
    have := congrArg Multiplicative.toAdd (congrFun cs.lengthParity_simple i)
    simp [parity_length_eq'] at this
    rw [Nat.lt_one_iff.mp length_lt_1] at this
    contradiction

theorem length_eq_one_iff {w : W} : ℓ w = 1 ↔ ∃ i : B, w = s i := by
  constructor
  · intro h
    rcases cs.exists_reduced_word w with ⟨ω, hω, rfl⟩
    rcases List.length_eq_one.mp (hω.trans h) with ⟨i, rfl⟩
    use i
    simp
  · rintro ⟨i, rfl⟩
    exact cs.length_simple i

theorem length_mul_simple (w : W) (i : B) :
    ℓ (w * s i) = ℓ w + 1 ∨ ℓ (w * s i) + 1 = ℓ w := by
  rcases Nat.lt_trichotomy (ℓ (w * s i)) (ℓ w) with lt | eq | gt
  · -- lt : ℓ (w * s i) < ℓ w
    right
    have length_ge := (max_le_iff.mp (cs.length_mul_ge w (s i))).left
    simp at length_ge
    -- length_ge : ℓ w ≤ ℓ (w * s i) + 1
    linarith
  · -- eq : ℓ (w * s i) = ℓ w
    have length_mod_two := cs.length_mul_mod_two w (s i)
    rw [eq] at length_mod_two
    simp at length_mod_two
    -- length_mod_two : (ℓ w) % 2 = (ℓ w + 1) % 2
    rcases Nat.mod_two_eq_zero_or_one (ℓ w) with even | odd
    · rw [even, Nat.succ_mod_two_eq_one_iff.mpr even] at length_mod_two
      contradiction
    · rw [odd, Nat.succ_mod_two_eq_zero_iff.mpr odd] at length_mod_two
      contradiction
  · -- gt : ℓ w < ℓ (w * s i)
    left
    have length_le := cs.length_mul_le w (s i)
    simp at length_le
    -- length_le : ℓ (w * s i) ≤ ℓ w + 1
    linarith

theorem length_simple_mul (w : W) (i : B) :
    ℓ (s i * w) = ℓ w + 1 ∨ ℓ (s i * w) + 1 = ℓ w := by
  have := cs.length_mul_simple w⁻¹ i
  rwa [(by simp : w⁻¹ * (s i) = ((s i) * w)⁻¹), length_inv, length_inv] at this

/-! ### Reduced words -/

/-- The proposition that `ω` is reduced; that is, it has minimal length among all words that
represent the same element of `W`. -/
def IsReduced (ω : List B) : Prop := ℓ (π ω) = ω.length

@[simp] theorem isReduced_reverse (ω : List B) : cs.IsReduced (ω.reverse) ↔ cs.IsReduced ω := by
  simp [IsReduced]

theorem exists_reduced_word' (w : W) : ∃ ω : List B, cs.IsReduced ω ∧ w = π ω := by
  rcases cs.exists_reduced_word w with ⟨ω, hω, rfl⟩
  use ω
  tauto

private theorem isReduced_take_and_drop {ω : List B} (rω : cs.IsReduced ω) (j : ℕ) :
    cs.IsReduced (ω.take j) ∧ cs.IsReduced (ω.drop j) := by
  have take_append_drop : ω = ω.take j ++ ω.drop j           := (List.take_append_drop _ _).symm
  have mul_take_drop : π ω = π (ω.take j) * π (ω.drop j)     := by
    rw [← wordProd_append]
    nth_rw 1 [take_append_drop]

  have take_length : ℓ (π (ω.take j)) ≤ (ω.take j).length    := cs.length_wordProd_le (ω.take j)
  have drop_length : ℓ (π (ω.drop j)) ≤ (ω.drop j).length    := cs.length_wordProd_le (ω.drop j)

  have length_add_ge := calc
    ℓ (π (ω.take j)) + ℓ (π (ω.drop j))
    _ ≥ ℓ (π ω)                                              := by
        rw [mul_take_drop]
        exact cs.length_mul_le _ _
    _ = ω.length                                             := rω
    _ = (ω.take j).length + (ω.drop j).length                := by
        nth_rw 1 [take_append_drop]
        exact List.length_append _ _

  constructor
  · unfold IsReduced
    linarith
  · unfold IsReduced
    linarith

theorem isReduced_take {ω : List B} (rω : cs.IsReduced ω) (j : ℕ) : cs.IsReduced (ω.take j) :=
  (isReduced_take_and_drop _ rω _).1

theorem isReduced_drop {ω : List B} (rω : cs.IsReduced ω) (j : ℕ) : cs.IsReduced (ω.drop j) :=
  (isReduced_take_and_drop _ rω _).2

theorem not_isReduced_alternatingWord (i i' : B) (m : ℕ) (hM : M i i' ≠ 0) (hm : m > M i i') :
    ¬ cs.IsReduced (alternatingWord i i' m) := by
  induction' hm with m _ ih
  · -- Base case; m = M i i' + 1
    suffices h : ℓ (π (alternatingWord i i' (M i i' + 1))) < M i i' + 1 by
      unfold IsReduced
      rw [Nat.succ_eq_add_one, length_alternatingWord]
      linarith
    have : M i i' + 1 ≤ M i i' * 2 := by linarith [Nat.one_le_iff_ne_zero.mpr hM]
    rw [cs.prod_alternatingWord_eq_prod_alternatingWord i i' _ this]

    have : M i i' * 2 - (M i i' + 1) = M i i' - 1 := by
      apply (Nat.sub_eq_iff_eq_add' this).mpr
      rw [add_assoc, add_comm 1, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hM)]
      exact mul_two _
    rw [this]

    calc
      ℓ (π (alternatingWord i' i (M i i' - 1)))
      _ ≤ (alternatingWord i' i (M i i' - 1)).length  := cs.length_wordProd_le _
      _ = M i i' - 1                                  := length_alternatingWord _ _ _
      _ ≤ M i i'                                      := Nat.sub_le _ _
      _ < M i i' + 1                                  := Nat.lt_succ_self _
  · -- Inductive step
    contrapose! ih
    rw [alternatingWord_succ'] at ih
    apply isReduced_drop (j := 1) at ih
    simp at ih
    assumption

end CoxeterSystem

end