/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.IsLocalHomeomorph

#align_import analysis.special_functions.complex.circle from "leanprover-community/mathlib"@"f333194f5ecd1482191452c5ea60b37d4d6afa08"

/-!
# Maps on the unit circle

In this file we prove some basic lemmas about `expMapCircle` and the restriction of `Complex.arg`
to the unit circle. These two maps define a partial equivalence between `circle` and `ℝ`, see
`circle.argPartialEquiv` and `circle.argEquiv`, that sends the whole circle to `(-π, π]`.
-/


open Complex Function Set

open Real

namespace circle

theorem injective_arg : Injective fun z : circle => arg z := fun z w h =>
  Subtype.ext <| ext_abs_arg ((abs_coe_circle z).trans (abs_coe_circle w).symm) h
#align circle.injective_arg circle.injective_arg

@[simp]
theorem arg_eq_arg {z w : circle} : arg z = arg w ↔ z = w :=
  injective_arg.eq_iff
#align circle.arg_eq_arg circle.arg_eq_arg

end circle

theorem arg_expMapCircle {x : ℝ} (h₁ : -π < x) (h₂ : x ≤ π) : arg (expMapCircle x) = x := by
  rw [expMapCircle_apply, exp_mul_I, arg_cos_add_sin_mul_I ⟨h₁, h₂⟩]
#align arg_exp_map_circle arg_expMapCircle

@[simp]
theorem expMapCircle_arg (z : circle) : expMapCircle (arg z) = z :=
  circle.injective_arg <| arg_expMapCircle (neg_pi_lt_arg _) (arg_le_pi _)
#align exp_map_circle_arg expMapCircle_arg

namespace circle

/-- `Complex.arg ∘ (↑)` and `expMapCircle` define a partial equivalence between `circle` and `ℝ`
with `source = Set.univ` and `target = Set.Ioc (-π) π`. -/
@[simps (config := .asFn)]
noncomputable def argPartialEquiv : PartialEquiv circle ℝ where
  toFun := arg ∘ (↑)
  invFun := expMapCircle
  source := univ
  target := Ioc (-π) π
  map_source' _ _ := ⟨neg_pi_lt_arg _, arg_le_pi _⟩
  map_target' := mapsTo_univ _ _
  left_inv' z _ := expMapCircle_arg z
  right_inv' _ hx := arg_expMapCircle hx.1 hx.2
#align circle.arg_local_equiv circle.argPartialEquiv

/-- `Complex.arg` and `expMapCircle` define an equivalence between `circle` and `(-π, π]`. -/
@[simps (config := .asFn)]
noncomputable def argEquiv : circle ≃ Ioc (-π) π where
  toFun z := ⟨arg z, neg_pi_lt_arg _, arg_le_pi _⟩
  invFun := expMapCircle ∘ (↑)
  left_inv _ := argPartialEquiv.left_inv trivial
  right_inv x := Subtype.ext <| argPartialEquiv.right_inv x.2
#align circle.arg_equiv circle.argEquiv

/-- `Complex.arg ∘ (↑)` and `expMapCircle` define a partial equivalence between `circle` and `ℝ`
with `source = Set.univ` and `target = Set.Ioo (-π) π`. -/
@[simps (config := .asFn)]
noncomputable def argPartialHomeomorph : PartialHomeomorph circle ℝ :=
  let fund : ∀ x : circle, Complex.arg x = Real.pi ↔ x = expMapCircle Real.pi :=
    fun x ↦ ⟨fun hx ↦ hx ▸ (expMapCircle_arg x).symm,
      fun hx ↦ hx ▸ arg_expMapCircle (neg_lt_self pi_pos) le_rfl⟩
  { toFun := arg ∘ (↑)
    invFun := expMapCircle
    source := {expMapCircle π}ᶜ
    target := Set.Ioo (-π) π
    map_source' := fun x hx ↦ let h := arg_mem_Ioc x; ⟨h.1, lt_of_le_of_ne h.2 (hx ∘ (fund x).mp)⟩
    map_target' := fun x hx hx' ↦ hx.2.ne
      (by rwa [mem_singleton_iff, ← fund, arg_expMapCircle hx.1 hx.2.le] at hx')
    left_inv' := fun x _ ↦ expMapCircle_arg x
    right_inv' := fun x hx ↦ arg_expMapCircle hx.1 hx.2.le
    open_source := isOpen_compl_singleton
    open_target := isOpen_Ioo
    continuousOn_toFun := (ContinuousAt.continuousOn fun _ ↦ continuousAt_arg).comp
      continuous_induced_dom.continuousOn
        (fun x h ↦ mem_slitPlane_iff_arg.mpr ⟨mt (fund x).mp h, ne_zero_of_mem_circle x⟩)
    continuousOn_invFun := Continuous.continuousOn (by continuity) }

end circle

theorem leftInverse_expMapCircle_arg : LeftInverse expMapCircle (arg ∘ (↑)) :=
  expMapCircle_arg
#align left_inverse_exp_map_circle_arg leftInverse_expMapCircle_arg

theorem invOn_arg_expMapCircle : InvOn (arg ∘ (↑)) expMapCircle (Ioc (-π) π) univ :=
  circle.argPartialEquiv.symm.invOn
#align inv_on_arg_exp_map_circle invOn_arg_expMapCircle

theorem surjOn_expMapCircle_neg_pi_pi : SurjOn expMapCircle (Ioc (-π) π) univ :=
  circle.argPartialEquiv.symm.surjOn
#align surj_on_exp_map_circle_neg_pi_pi surjOn_expMapCircle_neg_pi_pi

theorem expMapCircle_eq_expMapCircle {x y : ℝ} :
    expMapCircle x = expMapCircle y ↔ ∃ m : ℤ, x = y + m * (2 * π) := by
  rw [Subtype.ext_iff, expMapCircle_apply, expMapCircle_apply, exp_eq_exp_iff_exists_int]
  refine' exists_congr fun n => _
  rw [← mul_assoc, ← add_mul, mul_left_inj' I_ne_zero]
  norm_cast
#align exp_map_circle_eq_exp_map_circle expMapCircle_eq_expMapCircle

theorem periodic_expMapCircle : Periodic expMapCircle (2 * π) := fun z =>
  expMapCircle_eq_expMapCircle.2 ⟨1, by rw [Int.cast_one, one_mul]⟩
#align periodic_exp_map_circle periodic_expMapCircle

@[simp]
theorem expMapCircle_two_pi : expMapCircle (2 * π) = 1 :=
  periodic_expMapCircle.eq.trans expMapCircle_zero
#align exp_map_circle_two_pi expMapCircle_two_pi

theorem expMapCircle_sub_two_pi (x : ℝ) : expMapCircle (x - 2 * π) = expMapCircle x :=
  periodic_expMapCircle.sub_eq x
#align exp_map_circle_sub_two_pi expMapCircle_sub_two_pi

theorem expMapCircle_add_two_pi (x : ℝ) : expMapCircle (x + 2 * π) = expMapCircle x :=
  periodic_expMapCircle x
#align exp_map_circle_add_two_pi expMapCircle_add_two_pi

/-- `expMapCircle`, applied to a `Real.Angle`. -/
noncomputable def Real.Angle.expMapCircle (θ : Real.Angle) : circle :=
  periodic_expMapCircle.lift θ
#align real.angle.exp_map_circle Real.Angle.expMapCircle

@[simp]
theorem Real.Angle.expMapCircle_coe (x : ℝ) : Real.Angle.expMapCircle x = _root_.expMapCircle x :=
  rfl
#align real.angle.exp_map_circle_coe Real.Angle.expMapCircle_coe

theorem Real.Angle.coe_expMapCircle (θ : Real.Angle) :
    (θ.expMapCircle : ℂ) = θ.cos + θ.sin * I := by
  induction θ using Real.Angle.induction_on
  simp [Complex.exp_mul_I]
#align real.angle.coe_exp_map_circle Real.Angle.coe_expMapCircle

@[simp]
theorem Real.Angle.expMapCircle_zero : Real.Angle.expMapCircle 0 = 1 := by
  rw [← Real.Angle.coe_zero, Real.Angle.expMapCircle_coe, _root_.expMapCircle_zero]
#align real.angle.exp_map_circle_zero Real.Angle.expMapCircle_zero

@[simp]
theorem Real.Angle.expMapCircle_neg (θ : Real.Angle) :
    Real.Angle.expMapCircle (-θ) = (Real.Angle.expMapCircle θ)⁻¹ := by
  induction θ using Real.Angle.induction_on
  simp_rw [← Real.Angle.coe_neg, Real.Angle.expMapCircle_coe, _root_.expMapCircle_neg]
#align real.angle.exp_map_circle_neg Real.Angle.expMapCircle_neg

@[simp]
theorem Real.Angle.expMapCircle_add (θ₁ θ₂ : Real.Angle) : Real.Angle.expMapCircle (θ₁ + θ₂) =
    Real.Angle.expMapCircle θ₁ * Real.Angle.expMapCircle θ₂ := by
  induction θ₁ using Real.Angle.induction_on
  induction θ₂ using Real.Angle.induction_on
  exact _root_.expMapCircle_add _ _
#align real.angle.exp_map_circle_add Real.Angle.expMapCircle_add

@[simp]
theorem Real.Angle.arg_expMapCircle (θ : Real.Angle) :
    (arg (Real.Angle.expMapCircle θ) : Real.Angle) = θ := by
  induction θ using Real.Angle.induction_on
  rw [Real.Angle.expMapCircle_coe, expMapCircle_apply, exp_mul_I, ← ofReal_cos, ← ofReal_sin, ←
    Real.Angle.cos_coe, ← Real.Angle.sin_coe, arg_cos_add_sin_mul_I_coe_angle]
#align real.angle.arg_exp_map_circle Real.Angle.arg_expMapCircle

-- todo: upgrade this to `IsCoveringMap expMapCircle`.
lemma isLocalHomeomorph_expMapCircle : IsLocalHomeomorph expMapCircle := by
  intro t
  let e1 : PartialHomeomorph ℝ circle := circle.argPartialHomeomorph.symm
  let e2 : PartialHomeomorph ℝ ℝ := ((Homeomorph.addRight t).toPartialHomeomorphOfImageEq
    (Ioo (-π) π) (isOpen_Ioo) (Ioo (-π + t) (π + t)) (image_add_const_Ioo t (-π) π)).symm
  let e3 : PartialHomeomorph circle circle :=
    (Homeomorph.mulRight (expMapCircle t)).toPartialHomeomorphOfImageEq
      {expMapCircle Real.pi}ᶜ isOpen_compl_singleton {expMapCircle (Real.pi + t)}ᶜ
        (by rw [image_compl_eq (Homeomorph.mulRight (expMapCircle t)).bijective,
          image_singleton, Homeomorph.coe_mulRight, expMapCircle_add])
  let e4 : PartialHomeomorph ℝ circle := e2.trans' (e1.trans' e3 rfl) rfl
  exact ⟨e4, ⟨add_lt_of_neg_left t (neg_neg_of_pos pi_pos), lt_add_of_pos_left t pi_pos⟩,
    funext fun x ↦ (congrArg _ (sub_add_cancel x t).symm).trans (expMapCircle_add (x - t) t)⟩
