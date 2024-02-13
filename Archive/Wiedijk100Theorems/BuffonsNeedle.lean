/-
Copyright (c) 2024 Enrico Z. Borba. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Enrico Z. Borba
-/

import Mathlib.Probability.Density
import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Constructions.Prod.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Probability.Distributions.Uniform

/-!

# Freek № 99: Buffon's Needle

This file proves Theorem 99 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/), also
known as Buffon's Needle, which gives the probability of a needle of length `l > 0` crossing any
one of infinite vertical lines spaced out `d > 0` apart.

The two cases are proven in `buffon_short` and `buffon_long`.

## Overview of the Proof

We define a random variable `B : Ω → ℝ × ℝ` with a uniform distribution on `[-d/2, d/2] × [0, π]`.
This represents the needle's x-position and angle with respect to a vertical line. By symmetry, we
need to consider only a single vertical line positioned at `x = 0`. A needle therefore crosses the
vertical line if its projection onto the x-axis contains `0`.

We define a random variable `N : Ω → ℝ` that is `1` if the needle crosses a vertical line, and `0`
otherwise. This is defined as `fun ω => Set.indicator (needleProjX l (B ω).1 (B ω).2) 1 0`.

As in many references, the problem is split into two cases, `l ≤ d` (`buffon_short`), and `l ≥ d`
(`buffon_long`). For both cases, we show that
```
ℙ[N] = (d * π) ⁻¹ *
    ∫ θ in 0..π,
      ∫ x in Set.Icc (-d / 2) (d / 2) ∩ Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2), 1
```
In the short case `l ≤ d`, we show that `[-l * θ.sin/2, l * θ.sin/2] ⊆ [-d/2, d/2]`
(`short_needle_inter_eq`), and therefore the inner integral simplifies to
```
∫ x in (-θ.sin * l / 2)..(θ.sin * l / 2), 1 = θ.sin * l
```
Which then concludes in the short case being `ℙ[N] = (2 * l) / (d * π)`.

In the long case, `d ≥ l` (`buffon_long`), we show the outer integral simplifies to
```
∫ θ in 0..π, min d (θ.sin * l)
```
which can be expanded to
```
2 * (
  ∫ θ in 0..(d / l).arcsin, min d (θ.sin * l) +
  ∫ θ in (d / l).arcsin..(π / 2), min d (θ.sin * l)
)
```
We then show the two integrals equal their respective values `l - (l^2 - d^2).sqrt` and
`(π / 2 - (d / l).arcsin) * d`. Then with some algebra we conclude
```
ℙ[N] = (2 * l) / (d * π) - 2 / (d * π) * ((l^2 - d^2).sqrt + d * (d / l).arcsin) + 1
```

## References

* https://en.wikipedia.org/wiki/Buffon%27s_needle_problem
* https://www.math.leidenuniv.nl/~hfinkeln/seminarium/stelling_van_Buffon.pdf
* https://www.isa-afp.org/entries/Buffons_Needle.html

-/

open MeasureTheory (MeasureSpace IsProbabilityMeasure Measure pdf.IsUniform)
open ProbabilityTheory Real

lemma set_integral_toReal_ofReal_nonneg_ae {α : Type*} [MeasureSpace α] {s : Set α} {f : α → ℝ}
    (hs : MeasurableSet s) (hf : ∀ᵐ x : α, x ∈ s → 0 ≤ f x) :
    ∫ (x : α) in s, ENNReal.toReal (ENNReal.ofReal (f x)) =
    ∫ (x : α) in s, f x := by

  have : ∀ᵐ x : α, x ∈ s → f x = ENNReal.toReal (ENNReal.ofReal (f x)) := by
    simp_rw [eq_comm (a := f _), ENNReal.toReal_ofReal_eq_iff, hf]

  rw [MeasureTheory.set_integral_congr_ae hs this]

variable
  /- Probability theory variables. -/
  {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

  /- Buffon's needle variables. -/

  /-
    - `d > 0` is the distance between parallel lines.
    - `l > 0` is the length of the needle.
  -/
  (d l : ℝ)
  (hd : d > 0)
  (hl : l > 0)

  /- `B = (X, Θ)` is the joint random variable for the x-position and angle of the needle. -/
  (B : Ω → ℝ × ℝ)
  (hBₘ : Measurable B)

  /- `B` is uniformly distributed on `[-d/2, d/2] × [0, π]`. -/
  (hB : pdf.IsUniform B ((Set.Icc (-d / 2) (d / 2)) ×ˢ (Set.Icc 0 π)) ℙ)

/--
  Projection of a needle onto the x-axis. The needle's center is at x-coordinate `x`, of length
  `l` and angle `θ`. Note, `θ` is measured relative to the y-axis, that is, a vertical needle has
  `θ = 0`.
-/
def needleProjX (x θ : ℝ) : Set ℝ := Set.Icc (x - θ.sin * l / 2) (x + θ.sin * l / 2)

/--
  The indicator function of whether a needle at position `⟨x, θ⟩ : ℝ × ℝ` crosses the line `x = 0`.

  In order to faithfully model the problem, we compose `needleCrossesIndicator` with a random
  variable `B : Ω → ℝ × ℝ` with uniform distribution on `[-d/2, d/2] × [0, π]`. Then, by symmetry,
  the probability that the needle crosses `x = 0`, is the same as the probability of a needle
  crossing any of the infinitely spaced vertical lines distance `d` apart.
-/
noncomputable def needleCrossesIndicator (p : ℝ × ℝ) : ℝ :=
  Set.indicator (needleProjX l p.1 p.2) 1 0

/--
  A random variable representing whether the needle crosses a line.

  The line is at `x = 0`, and therefore a needle crosses the line if its projection onto the x-axis
  contains `0`. This random variable is `1` if the needle crosses the line, and `0` otherwise.
-/
noncomputable def N : Ω → ℝ := needleCrossesIndicator l ∘ B

/--
  The possible x-positions and angle relative to the y-axis of a needle.
-/
abbrev needleSpace := Set.Icc (-d / 2) (d / 2) ×ˢ Set.Icc 0 π

lemma needleSpace_volume : ℙ (needleSpace d) = ENNReal.ofReal (d * π) := by
  simp_rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod, Real.volume_Icc,
    ENNReal.ofReal_mul hd.le]
  ring_nf

lemma needleCrossesIndicator_measurable : Measurable (needleCrossesIndicator l) := by
  unfold needleCrossesIndicator
  refine' Measurable.indicator measurable_const (IsClosed.measurableSet (IsClosed.inter ?l ?r))

  all_goals simp only [tsub_le_iff_right, zero_add, ← neg_le_iff_add_nonneg']
  case' l => refine' isClosed_le continuous_fst _
  case' r => refine' isClosed_le (Continuous.neg continuous_fst) _

  all_goals
    refine' Continuous.mul (Continuous.mul _ continuous_const) continuous_const
    simp_rw [← Function.comp_apply (f := Real.sin) (g := Prod.snd),
      Continuous.comp Real.continuous_sin continuous_snd]

lemma needleCrossesIndicator_stronglyMeasurable :
    MeasureTheory.StronglyMeasurable (needleCrossesIndicator l) := by
  refine' stronglyMeasurable_iff_measurable_separable.mpr
    ⟨needleCrossesIndicator_measurable l, {0, 1}, ?seperable⟩

  have range_finite : Set.Finite ({0, 1} : Set ℝ) := by
    simp only [Set.mem_singleton_iff, Set.finite_singleton, Set.Finite.insert]
  refine' ⟨range_finite.countable, ?subset_closure⟩
  rw [IsClosed.closure_eq range_finite.isClosed, Set.subset_def, Set.range]

  intro x ⟨p, hxp⟩
  by_cases hp : 0 ∈ needleProjX l p.1 p.2
  · simp_rw [needleCrossesIndicator, Set.indicator_of_mem hp, Pi.one_apply] at hxp
    apply Or.inr hxp.symm
  · simp_rw [needleCrossesIndicator, Set.indicator_of_not_mem hp] at hxp
    apply Or.inl hxp.symm

lemma needleCrossesIndicator_integrable :
    MeasureTheory.Integrable (needleCrossesIndicator l)
      (Measure.prod
        (Measure.restrict ℙ (Set.Icc (-d / 2) (d / 2)))
        (Measure.restrict ℙ (Set.Icc 0 π))) := by

  have needleCrossesIndicator_nonneg p : needleCrossesIndicator l p ≥ 0 := by
    apply Set.indicator_apply_nonneg
    simp only [Pi.one_apply, zero_le_one, implies_true]

  have needleCrossesIndicator_le_one p : needleCrossesIndicator l p ≤ 1 := by
    unfold needleCrossesIndicator
    by_cases hp : 0 ∈ needleProjX l p.1 p.2
    · simp_rw [Set.indicator_of_mem hp, Pi.one_apply, le_refl]
    · simp_rw [Set.indicator_of_not_mem hp, zero_le_one]

  refine' And.intro
    (needleCrossesIndicator_stronglyMeasurable l).aestronglyMeasurable
    ((MeasureTheory.hasFiniteIntegral_iff_norm (needleCrossesIndicator l)).mpr _)
  refine' lt_of_le_of_lt (MeasureTheory.lintegral_mono (g := 1) ?le_const) ?lt_top

  case le_const =>
    intro p
    simp only [Real.norm_eq_abs, abs_of_nonneg (needleCrossesIndicator_nonneg _),
      ENNReal.ofReal_le_one, Pi.one_apply]
    exact needleCrossesIndicator_le_one p

  case lt_top =>
    simp only [Pi.one_apply, MeasureTheory.lintegral_const, one_mul, Measure.prod_restrict,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Measure.prod_prod, Real.volume_Icc]
    ring_nf
    simp_rw [← ENNReal.ofReal_mul hd.le, ENNReal.ofReal_lt_top]

/--
  This is a common step in both the short and the long case to simplify the expectation of the
  needle crossing a line to a double integral.
  ```
  ∫ (θ : ℝ) in Set.Icc 0 π,
    ∫ (x : ℝ) in Set.Icc (-d / 2) (d / 2) ∩ Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2), 1
  ```
  The domain of the inner integral is simpler in the short case, where the intersection is
  equal to `Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2)` by `short_needle_inter_eq`.
-/
lemma buffon_integral :
    𝔼[N l B] = (d * π) ⁻¹ *
      ∫ (θ : ℝ) in Set.Icc 0 π,
      ∫ (x : ℝ) in Set.Icc (-d / 2) (d / 2) ∩ Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2), 1 := by

  simp_rw [N, Function.comp_apply]
  rw [
    ← MeasureTheory.integral_map hBₘ.aemeasurable
      (needleCrossesIndicator_stronglyMeasurable l).aestronglyMeasurable,
    hB, MeasureTheory.integral_smul_measure, needleSpace_volume d hd,
    ENNReal.ofReal_inv_of_pos (mul_pos hd Real.pi_pos),
    ENNReal.toReal_ofReal (inv_nonneg.mpr (mul_nonneg hd.le Real.pi_pos.le)), smul_eq_mul,
  ]

  refine' mul_eq_mul_left_iff.mpr (Or.inl _)

  have Real_measure_prod : (ℙ : Measure (ℝ × ℝ)) = Measure.prod ℙ ℙ := rfl
  have : MeasureTheory.IntegrableOn (needleCrossesIndicator l)
      (Set.Icc (-d / 2) (d / 2) ×ˢ Set.Icc 0 π) := by
    apply (MeasureTheory.integrableOn_def _ _ _).mpr
    simp_rw [Real_measure_prod, ← Measure.prod_restrict,
      needleCrossesIndicator_integrable d l hd]

  rw [Real_measure_prod, MeasureTheory.set_integral_prod _ this,
    MeasureTheory.integral_integral_swap ?integrable]

  case integrable => simp_rw [Function.uncurry_def, Prod.mk.eta,
    needleCrossesIndicator_integrable d l hd]

  simp only [needleCrossesIndicator, needleProjX, Set.mem_Icc]

  have indicator_eq (x θ : ℝ) :
    Set.indicator (Set.Icc (x - θ.sin * l / 2) (x + θ.sin * l / 2)) 1 0 =
    Set.indicator (Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2)) (1 : ℝ → ℝ) x := by
    simp_rw [Set.indicator, Pi.one_apply, Set.mem_Icc, tsub_le_iff_right, zero_add, neg_mul]

    have :
        x ≤ Real.sin θ * l / 2 ∧ 0 ≤ x + Real.sin θ * l / 2 ↔
        -(Real.sin θ * l) / 2 ≤ x ∧ x ≤ Real.sin θ * l / 2 := by
      rw [neg_div, and_comm, ← tsub_le_iff_right, zero_sub]

    by_cases h : x ≤ Real.sin θ * l / 2 ∧ 0 ≤ x + Real.sin θ * l / 2
    · rw [if_pos h, if_pos (this.mp h)]
    · rw [if_neg h, if_neg (this.not.mp h)]

  simp_rw [indicator_eq, MeasureTheory.set_integral_indicator measurableSet_Icc, Pi.one_apply]

/--
  From `buffon_integral`, in both the short and the long case, we have
  ```
  𝔼[N l B] = (d * π)⁻¹ *
    ∫ (θ : ℝ) in Set.Icc 0 π,
      ∫ (x : ℝ) in Set.Icc (-d / 2) (d / 2) ∩ Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2), 1
  ```
  With this lemma, in the short case, the inner integral's domain simplifies to
  `Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2)`.
-/
lemma short_needle_inter_eq (h : l ≤ d) (θ : ℝ) :
    Set.Icc (-d / 2) (d / 2) ∩ Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2) =
    Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2) := by

  rw [Set.Icc_inter_Icc, inf_eq_min, sup_eq_max, max_div_div_right zero_le_two,
    min_div_div_right zero_le_two, neg_mul, max_neg_neg, mul_comm,
    min_eq_right (mul_le_of_le_of_le_one_of_nonneg h θ.sin_le_one hl.le)]

/--
  Buffon's Needle, the short case (`l ≤ d`). The probability of the needle crossing a line
  equals `(2 * l) / (d * π)`.
-/
theorem buffon_short (h : l ≤ d) : ℙ[N l B] = (2 * l) * (d * π)⁻¹ := by
  simp_rw [buffon_integral d l hd B hBₘ hB, short_needle_inter_eq d l hl h _,
    MeasureTheory.set_integral_const, Real.volume_Icc, smul_eq_mul, mul_one, mul_comm (d * π)⁻¹ _,
    mul_eq_mul_right_iff]

  apply Or.inl
  ring_nf

  have : ∀ θ ∈ Set.Icc 0 π, θ.sin * l ≥ 0 := by
    intro θ hθ
    exact mul_nonneg (Real.sin_nonneg_of_mem_Icc hθ) hl.le

  simp_rw [set_integral_toReal_ofReal_nonneg_ae measurableSet_Icc (MeasureTheory.ae_of_all _ this),
    ← smul_eq_mul, integral_smul_const, smul_eq_mul, mul_comm, mul_eq_mul_left_iff]

  apply Or.inl
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le Real.pi_pos.le,
    integral_sin, Real.cos_zero, Real.cos_pi]

  ring_nf

/--
  The integrand in the long case is `min d (θ.sin * l)` and its integrability is necessary for
  the integral lemmas below.
-/
lemma min_const_sin_mul_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun (θ : ℝ) => min d (θ.sin * l)) ℙ a b := by
  apply Continuous.intervalIntegrable
  exact Continuous.min continuous_const (Continuous.mul Real.continuous_sin continuous_const)

/--
  This equality is useful since `θ.sin` is increasing in `0..π / 2` (but not in `0..π`).
  Then, `∫ θ in (0)..π / 2, min d (θ.sin * l)` can be split into two adjacent integrals, at the
  point where `d = θ.sin * l`, which is `θ = (d / l).arcsin`.
-/
lemma integral_min_eq_two_mul :
    ∫ θ in (0)..π, min d (θ.sin * l) = 2 * ∫ θ in (0)..π / 2, min d (θ.sin * l) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π / 2) (c := π)]
  conv => lhs; arg 2; arg 1; intro θ; rw [← neg_neg θ, Real.sin_neg]

  simp_rw [intervalIntegral.integral_comp_neg fun θ => min d (-θ.sin * l), ← Real.sin_add_pi,
    intervalIntegral.integral_comp_add_right (fun θ => min d (θ.sin * l)), add_left_neg,
    (by ring : -(π / 2) + π = π / 2), two_mul]

  all_goals exact min_const_sin_mul_intervalIntegrable d l _ _

/--
  The first of two adjacent integrals in the long case. In the range `(0)..(d / l).arcsin`, we
  have that `θ.sin * l ≤ d`, and thus the integral is `∫ θ in (0)..(d / l).arcsin, θ.sin * l`.
-/
lemma integral_zero_to_arcsin_min :
    ∫ θ in (0)..(d / l).arcsin, min d (θ.sin * l) = (1 - (1 - (d / l) ^ 2).sqrt) * l := by
  have : Set.EqOn (fun θ => min d (θ.sin * l)) (Real.sin · * l) (Set.uIcc 0 (d / l).arcsin) := by
    intro θ ⟨hθ₁, hθ₂⟩
    have : (d / l).arcsin ≥ 0 := Real.arcsin_nonneg.mpr (div_nonneg hd.le hl.le)
    simp only [sup_eq_max, inf_eq_min, min_eq_left this, max_eq_right this] at hθ₁ hθ₂

    have hθ_mem : θ ∈ Set.Ioc (-(π / 2)) (π / 2) := by
      exact ⟨lt_of_lt_of_le (neg_lt_zero.mpr (div_pos Real.pi_pos two_pos)) hθ₁,
        le_trans hθ₂ (d / l).arcsin_mem_Icc.right⟩
    simp_rw [min_eq_right ((le_div_iff hl).mp ((Real.le_arcsin_iff_sin_le' hθ_mem).mp hθ₂))]

  rw [intervalIntegral.integral_congr this, intervalIntegral.integral_mul_const, integral_sin,
    Real.cos_zero, Real.cos_arcsin]

/--
  The second of two adjacent integrals in the long case. In the range `(d / l).arcsin..(π / 2)`, we
  have that `d ≤ θ.sin * l`, and thus the integral is `∫ θ in (d / l).arcsin..(π / 2), d`.
-/
lemma integral_arcsin_to_pi_div_two_min (h : l ≥ d) :
    ∫ θ in (d / l).arcsin..(π / 2), min d (θ.sin * l) = (π / 2 - (d / l).arcsin) * d := by
  have : Set.EqOn (fun θ => min d (θ.sin * l)) (fun _ => d) (Set.uIcc (d / l).arcsin (π / 2)) := by
    intro θ ⟨hθ₁, hθ₂⟩

    wlog hθ_ne_pi_div_two : θ ≠ π / 2
    · simp only [ne_eq, not_not] at hθ_ne_pi_div_two
      simp only [hθ_ne_pi_div_two, Real.sin_pi_div_two, one_mul, min_eq_left h]

    simp only [sup_eq_max, inf_eq_min, min_eq_left (d / l).arcsin_le_pi_div_two,
      max_eq_right (d / l).arcsin_le_pi_div_two] at hθ₁ hθ₂

    have hθ_mem : θ ∈ Set.Ico (-(π / 2)) (π / 2) := by
      exact ⟨le_trans (Real.arcsin_mem_Icc (d / l)).left hθ₁, lt_of_le_of_ne hθ₂ hθ_ne_pi_div_two⟩
    simp_rw [min_eq_left ((div_le_iff hl).mp ((Real.arcsin_le_iff_le_sin' hθ_mem).mp hθ₁))]

  rw [intervalIntegral.integral_congr this, intervalIntegral.integral_const, smul_eq_mul]

/--
  Buffon's Needle, the short case (`l ≥ d`).
-/
theorem buffon_long (h : l ≥ d) :
    ℙ[N l B] = (2 * l) / (d * π) - 2 / (d * π) * ((l^2 - d^2).sqrt + d * (d / l).arcsin) + 1 := by

  simp only [
    buffon_integral d l hd B hBₘ hB, MeasureTheory.integral_const, smul_eq_mul, mul_one,
    MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, Set.Icc_inter_Icc, Real.volume_Icc,
    sup_eq_max, inf_eq_min, min_div_div_right zero_le_two d, max_div_div_right zero_le_two (-d),
    div_sub_div_same, neg_mul, max_neg_neg, sub_neg_eq_add, ← mul_two,
    mul_div_cancel (min d (Real.sin _ * l)) two_ne_zero
  ]

  have (θ : ℝ) (hθ : θ ∈ Set.Icc 0 π) : min d (θ.sin * l) ≥ 0 := by
    by_cases h : d ≤ θ.sin * l
    · rw [min_eq_left h]; exact hd.le
    · rw [min_eq_right (not_le.mp h).le]; exact mul_nonneg (Real.sin_nonneg_of_mem_Icc hθ) hl.le

  rw [set_integral_toReal_ofReal_nonneg_ae measurableSet_Icc (MeasureTheory.ae_of_all _ this),
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le Real.pi_pos.le, integral_min_eq_two_mul,
    ← intervalIntegral.integral_add_adjacent_intervals
      (min_const_sin_mul_intervalIntegrable d l _ _) (min_const_sin_mul_intervalIntegrable d l _ _),
    integral_zero_to_arcsin_min d l hd hl, integral_arcsin_to_pi_div_two_min d l hl h]

  /-
    the rest of the proof is annoying algebra, the goal is
      (d * π)⁻¹ * (2 * ((1 - sqrt (1 - (d / l) ^ 2)) * l + (π / 2 - arcsin (d / l)) * d)) =
      2 * l / (d * π) - 2 / (d * π) * (sqrt (l ^ 2 - d ^ 2) + d * arcsin (d / l)) + 1
  -/

  have this₁ : (1 - Real.sqrt (1 - (d / l) ^ 2)) * l = l - (l ^ 2 - d ^ 2).sqrt := by
    rw [mul_comm, mul_sub, mul_one, div_pow, one_sub_div, Real.sqrt_div, Real.sqrt_sq hl.le,
      ← mul_div_assoc, mul_comm, mul_div_cancel _ (ne_of_gt hl)]
    · simp_rw [sub_nonneg, sq_le_sq, abs_of_pos hd, abs_of_pos hl, h]
    · simp_rw [(pow_eq_zero_iff two_ne_zero).not, ne_of_gt hl, not_false_eq_true]
  have this₂ : 2 * d * (π / 2 - (d / l).arcsin) / (d * π) = 1 - (2 / π) * (d / l).arcsin := by
    rw [mul_sub, sub_div, mul_assoc, ← mul_comm_div, ← mul_assoc, ← mul_comm_div,
      div_self two_ne_zero, one_mul, div_self (ne_of_gt (mul_pos hd Real.pi_pos)), mul_div_assoc,
      ← mul_comm_div, mul_comm 2, mul_div_mul_left _ _ (ne_of_gt hd)]
  have this₃ : 2 * Real.sqrt (l^2 - d^2) / (d * π) = 2 / (d * π) * (l^2 - d^2).sqrt := by ring_nf
  have this₄ : 2 / π * d / d = 2 / (d * π) * d := by ring_nf

  conv =>
    lhs
    rw [this₁, inv_mul_eq_div, mul_add, mul_sub, add_div, sub_div,
      mul_comm (π / 2 - (d / l).arcsin), ← mul_assoc, this₂, this₃, add_sub, add_sub_right_comm,
      sub_eq_add_neg, sub_eq_add_neg, ← neg_mul, ← mul_div_cancel (2 / π) (ne_of_gt hd), this₄,
      mul_assoc, ← neg_mul, add_assoc (2 * l / (d * π)) _ _, ← mul_add, neg_mul, ← sub_eq_add_neg]
