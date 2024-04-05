/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.MeasureCompProd
import Mathlib.Probability.Kernel.Disintegration.CondCdf
import Mathlib.Probability.Kernel.Disintegration.Density
import Mathlib.Probability.Kernel.Disintegration.CdfToKernel

/-!
# Disintegration of kernels and measures

Let `κ : kernel α (β × Ω)` be a finite kernel, where `Ω` is a standard Borel space. Then if `α` is
countable or `β` has a countably generated σ-algebra (for example if it is standard Borel), then
there exists a `kernel (α × β) Ω` called conditional kernel and denoted by `condKernel κ` such that
`κ = fst κ ⊗ₖ condKernel κ`.
We also define a conditional kernel for a measure `ρ : Measure (β × Ω)`, where `Ω` is a standard
Borel space. This is a `kernel β Ω` denoted by `ρ.condKernel` such that `ρ = ρ.fst ⊗ₘ ρ.condKernel`.

In order to obtain a disintegration for any standard Borel space `Ω`, we use that these spaces embed
measurably into `ℝ`: it then suffices to define a suitable kernel for `Ω = ℝ`.

For `κ : kernel α (β × ℝ)`, the construction of the conditional kernel proceeds as follows:
* Build a measurable function `f : (α × β) → ℚ → ℝ` such that for all measurable sets
  `s` and all `q : ℚ`, `∫ x in s, f (a, x) q ∂(kernel.fst κ a) = (κ a (s ×ˢ Iic (q : ℝ))).toReal`.
  We restrict to `ℚ` here to be able to prove the measurability.
* Extend that function to `(α × β) → StieltjesFunction`. See the file `MeasurableStieltjes.lean`.
* Finally obtain from the measurable Stieltjes function a measure on `ℝ` for each element of `α × β`
  in a measurable way: we have obtained a `kernel (α × β) ℝ`.
  See the file `CdfToKernel.lean` for that step.

The first step (building the measurable function on `ℚ`) is done differently depending on whether
`α` is countable or not.
* If `α` is countable, we can provide for each `a : α` a function `f : β → ℚ → ℝ` and proceed as
  above to obtain a `kernel β ℝ`. Since `α` is countable, measurability is not an issue and we can
  put those together into a `kernel (α × β) ℝ`. The construction of that `f` is done in
  the `CondCdf.lean` file.
* If `α` is not countable, we can't proceed separately for each `a : α` and have to build a function
  `f : α × β → ℚ → ℝ` which is measurable on the product. We are able to do so if `β` has a
  countably generated σ-algebra (this is the case in particular for standard Borel spaces).
  See the file `Density.lean`.

The conditional kernel is defined under the typeclass assumption
`CountableOrCountablyGenerated α β`, which encodes the property
`(Countable α ∧ MeasurableSingletonClass α) ∨ CountablyGenerated β`.

Properties of integrals involving `condKernel` are collated in the file `Integral.lean`.
The conditional kernel is unique (almost everywhere w.r.t. `fst κ`): this is proved in the file
`Unique.lean`.

## Main definitions

* `ProbabilityTheory.kernel.condKernel κ : kernel (α × β) Ω`: conditional kernel described above.
* `MeasureTheory.Measure.condKernel ρ : kernel β Ω`: conditional kernel of a measure.

## Main statements

* `ProbabilityTheory.kernel.compProd_fst_condKernel`: `fst κ ⊗ₖ condKernel κ = κ`
* `MeasureTheory.Measure.compProd_fst_condKernel`: `ρ.fst ⊗ₘ ρ.condKernel = ρ`
-/

#align_import probability.kernel.disintegration from "leanprover-community/mathlib"@"6315581f5650ffa2fbdbbbedc41243c8d7070981"

open MeasureTheory Set Filter MeasurableSpace

open scoped ENNReal MeasureTheory Topology ProbabilityTheory

#noalign probability_theory.cond_kernel_real
#noalign probability_theory.cond_kernel_real_Iic
#noalign probability_theory.set_lintegral_cond_kernel_real_Iic
#noalign probability_theory.set_lintegral_cond_kernel_real_univ
#noalign probability_theory.lintegral_cond_kernel_real_univ
#noalign probability_theory.set_lintegral_cond_kernel_real_prod
#noalign probability_theory.lintegral_cond_kernel_real_mem
#noalign probability_theory.kernel.const_eq_comp_prod_real
#noalign probability_theory.measure_eq_comp_prod_real
#noalign probability_theory.lintegral_cond_kernel_real
#noalign probability_theory.ae_cond_kernel_real_eq_one
#noalign probability_theory.exists_cond_kernel
#noalign probability_theory.cond_kernel_def
#noalign probability_theory.kernel.const_unit_eq_comp_prod
#noalign probability_theory.kernel.const_eq_comp_prod

namespace ProbabilityTheory.kernel

variable {α β γ Ω : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} [MeasurableSpace.CountablyGenerated γ]
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]

section BorelSnd

/-! ### Disintegration of kernels on standard Borel spaces

Since every standard Borel space embeds measurably into `ℝ`, we can generalize a disintegration
property on `ℝ` to all these spaces. -/

/-- Auxiliary definition for `ProbabilityTheory.kernel.condKernel`.
For `κ` a kernel from `α` to `β × Ω` where `Ω` is standard borel, and `f` a conditional kernel
CDF of the map of `κ` by an embedding of `Ω` into `ℝ` (a kernel from `α` to `β × ℝ`), we build a
`kernel (α × β) Ω`.

`f` gives a Markov kernel from `α × β` to `ℝ`: we can't take directly the comap of that kernel by
the embedding `embeddingReal Ω`, because it would not be a Markov kernel (its value is a probability
measure only almost everywhere). We thus take the comap of a slight modification. -/
noncomputable
def condKernelBorelSnd (κ : kernel α (β × Ω)) {f : α × β → StieltjesFunction}
    (hf : IsCondKernelCDF f
      (map κ (Prod.map (id : β → β) (embeddingReal Ω))
        (measurable_id.prod_map (measurableEmbedding_embeddingReal Ω).measurable))
      (fst (map κ (Prod.map (id : β → β) (embeddingReal Ω))
        (measurable_id.prod_map (measurableEmbedding_embeddingReal Ω).measurable)))) :
    kernel (α × β) Ω :=
  have he := measurableEmbedding_embeddingReal Ω
  let x₀ := (range_nonempty (embeddingReal Ω)).choose
  comapRight (piecewise (measurableSet_toKernel_eq_one hf he.measurableSet_range)
    (hf.toKernel f) (deterministic (fun _ ↦ x₀) measurable_const)) he

/-- `condKernelBorelSnd` is a Markov kernel. -/
instance instIsMarkovKernel_condKernelBorelSnd (κ : kernel α (β × Ω))
    {f : α × β → StieltjesFunction}
    (hf : IsCondKernelCDF f
      (map κ (Prod.map (id : β → β) (embeddingReal Ω))
        (measurable_id.prod_map (measurableEmbedding_embeddingReal Ω).measurable))
      (fst (map κ (Prod.map (id : β → β) (embeddingReal Ω))
        (measurable_id.prod_map (measurableEmbedding_embeddingReal Ω).measurable)))) :
    IsMarkovKernel (condKernelBorelSnd κ hf) := by
  rw [condKernelBorelSnd]
  refine IsMarkovKernel.comapRight _ _ fun a ↦ ?_
  rw [piecewise_apply']
  split_ifs with h_mem
  · exact h_mem
  · classical
    rw [deterministic_apply' _ _ (measurableEmbedding_embeddingReal Ω).measurableSet_range,
      indicator_apply, if_pos]
    exact (range_nonempty (embeddingReal Ω)).choose_spec

/-- `fst κ ⊗ₖ condKernelBorelSnd κ hf = κ`. -/
lemma compProd_fst_condKernelBorelSnd (κ : kernel α (β × Ω)) [IsFiniteKernel κ]
    {f : α × β → StieltjesFunction}
    (hf : IsCondKernelCDF f
      (map κ (Prod.map (id : β → β) (embeddingReal Ω))
        (measurable_id.prod_map (measurableEmbedding_embeddingReal Ω).measurable))
      (fst (map κ (Prod.map (id : β → β) (embeddingReal Ω))
        (measurable_id.prod_map (measurableEmbedding_embeddingReal Ω).measurable)))) :
    fst κ ⊗ₖ condKernelBorelSnd κ hf = κ := by
  let e := embeddingReal Ω
  let he := measurableEmbedding_embeddingReal Ω
  let κ' := map κ (Prod.map (id : β → β) e) (measurable_id.prod_map he.measurable)
  have h_prod_embed : MeasurableEmbedding (Prod.map (id : β → β) e) :=
    MeasurableEmbedding.id.prod_mk he
  have h_fst : fst κ' = fst κ := by
    ext a u hu
    unfold_let κ'
    rw [fst_apply' _ _ hu, fst_apply' _ _ hu, map_apply' κ h_prod_embed.measurable]
    · rfl
    · exact measurable_fst hu
  have : κ = comapRight κ' h_prod_embed := by
    ext c t ht : 2
    unfold_let κ'
    rw [comapRight_apply' _ _ _ ht, map_apply' κ h_prod_embed.measurable
      _ (h_prod_embed.measurableSet_image.mpr ht)]
    congr with x : 1
    rw [← @Prod.mk.eta _ _ x]
    simp only [id.def, mem_preimage, Prod.map_mk, mem_image, Prod.mk.inj_iff, Prod.exists]
    refine' ⟨fun h => ⟨x.1, x.2, h, rfl, rfl⟩, _⟩
    rintro ⟨a, b, h_mem, rfl, he_eq⟩
    rwa [he.injective he_eq] at h_mem
  conv_rhs => rw [this]
  unfold_let κ'
  conv_rhs => rw [← compProd_toKernel hf]
  change fst κ ⊗ₖ condKernelBorelSnd κ hf = comapRight (fst κ' ⊗ₖ hf.toKernel f) h_prod_embed
  ext c t ht : 2
  rw [comapRight_apply' _ _ _ ht, compProd_apply _ _ _ (h_prod_embed.measurableSet_image.mpr ht)]
  simp_rw [h_fst, compProd_apply _ _ _ ht]
  refine lintegral_congr_ae ?_
  let ρ_set := {p : α × β | hf.toKernel f p (range e) = 1}
  have h_ae : ∀ a, ∀ᵐ t ∂(fst κ a), (a, t) ∈ ρ_set := by
    intro a
    rw [← h_fst]
    refine ae_toKernel_eq_one hf a he.measurableSet_range ?_
    simp only [mem_compl_iff, mem_range, not_exists]
    rw [map_apply']
    · have h_empty : {a : β × Ω | ∀ (x : Ω), ¬e x = e a.2} = ∅ := by
        ext x
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_forall, not_not,
          exists_apply_eq_apply]
      simp [h_empty]
    · have : {x : β × ℝ | ∀ (y : Ω), ¬ e y = x.2} = univ ×ˢ (range e)ᶜ := by
        ext x
        simp only [mem_setOf_eq, mem_prod, mem_univ, mem_compl_iff, mem_range, not_exists, true_and]
      rw [this]
      exact MeasurableSet.univ.prod he.measurableSet_range.compl
  filter_upwards [h_ae c] with a ha
  rw [condKernelBorelSnd, comapRight_apply']
  swap; · exact measurable_prod_mk_left ht
  have h1 : {c : ℝ | (a, c) ∈ Prod.map id e '' t} = e '' {c : Ω | (a, c) ∈ t} := by
    ext1 x
    simp only [Prod_map, id.def, mem_image, Prod.mk.inj_iff, Prod.exists, mem_setOf_eq]
    constructor
    · rintro ⟨a', b, h_mem, rfl, hf_eq⟩
      exact ⟨b, h_mem, hf_eq⟩
    · rintro ⟨b, h_mem, hf_eq⟩
      exact ⟨a, b, h_mem, rfl, hf_eq⟩
  rw [h1, piecewise_apply, if_pos ha]
  rfl

end BorelSnd

section CountablyGenerated

open ProbabilityTheory.kernel

lemma isRatCondKernelCDFAux_density_Iic (κ : kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    IsRatCondKernelCDFAux (fun (p : α × γ) q ↦ density κ (fst κ) p.1 p.2 (Iic q)) κ (fst κ)
      where
  measurable := measurable_pi_iff.mpr fun _ ↦ measurable_density κ (fst κ) measurableSet_Iic
  mono' a q r hqr :=
    ae_of_all _ fun c ↦ density_mono_set le_rfl a c (Iic_subset_Iic.mpr (by exact_mod_cast hqr))
  nonneg' a q := ae_of_all _ fun c ↦ density_nonneg le_rfl _ _ _
  le_one' a q := ae_of_all _ fun c ↦ density_le_one le_rfl _ _ _
  tendsto_integral_of_antitone a s hs_anti hs_tendsto := by
    let s' : ℕ → Set ℝ := fun n ↦ Iic (s n)
    refine tendsto_integral_density_of_antitone le_rfl a s' ?_ ?_ (fun _ ↦ measurableSet_Iic)
    · refine fun i j hij ↦ Iic_subset_Iic.mpr ?_
      exact mod_cast hs_anti hij
    · ext x
      simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false, not_forall, not_le, s']
      rw [tendsto_atTop_atBot] at hs_tendsto
      have ⟨q, hq⟩ := exists_rat_lt x
      obtain ⟨i, hi⟩ := hs_tendsto q
      refine ⟨i, lt_of_le_of_lt ?_ hq⟩
      exact mod_cast hi i le_rfl
  tendsto_integral_of_monotone a s hs_mono hs_tendsto := by
    rw [fst_apply' _ _ MeasurableSet.univ]
    let s' : ℕ → Set ℝ := fun n ↦ Iic (s n)
    refine tendsto_integral_density_of_monotone (le_rfl : fst κ ≤ fst κ)
      a s' ?_ ?_ (fun _ ↦ measurableSet_Iic)
    · exact fun i j hij ↦ Iic_subset_Iic.mpr (by exact mod_cast hs_mono hij)
    · ext x
      simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
      rw [tendsto_atTop_atTop] at hs_tendsto
      have ⟨q, hq⟩ := exists_rat_gt x
      obtain ⟨i, hi⟩ := hs_tendsto q
      refine ⟨i, hq.le.trans ?_⟩
      exact mod_cast hi i le_rfl
  integrable a q := integrable_density le_rfl a measurableSet_Iic
  set_integral a A hA q := set_integral_density le_rfl a measurableSet_Iic hA

/-- Taking the kernel density of intervals `Iic q` for `q : ℚ` gives a function with the property
`isRatCondKernelCDF`. -/
lemma isRatCondKernelCDF_density_Iic (κ : kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    IsRatCondKernelCDF (fun (p : α × γ) q ↦ density κ (fst κ) p.1 p.2 (Iic q)) κ (fst κ) :=
  (isRatCondKernelCDFAux_density_Iic κ).isRatCondKernelCDF

/-- The conditional kernel CDF of a kernel `κ : kernel α (γ × ℝ)`, where `γ` is countably generated.
-/
noncomputable
def condKernelCDF (κ : kernel α (γ × ℝ)) [IsFiniteKernel κ] : α × γ → StieltjesFunction :=
  stieltjesOfMeasurableRat (fun (p : α × γ) q ↦ density κ (fst κ) p.1 p.2 (Iic q))
    (isRatCondKernelCDF_density_Iic κ).measurable

lemma isCondKernelCDF_condKernelCDF (κ : kernel α (γ × ℝ)) [IsFiniteKernel κ] :
    IsCondKernelCDF (condKernelCDF κ) κ (fst κ) :=
  isCondKernelCDF_stieltjesOfMeasurableRat (isRatCondKernelCDF_density_Iic κ)

/-- Auxiliary definition for `ProbabilityTheory.kernel.condKernel`.
A conditional kernel for `κ : kernel α (γ × Ω)` where `γ` is countably generated and `Ω` is
standard Borel. -/
noncomputable
def condKernelBorel (κ : kernel α (γ × Ω)) [IsFiniteKernel κ] : kernel (α × γ) Ω :=
  let f := embeddingReal Ω
  let hf := measurableEmbedding_embeddingReal Ω
  let κ' := map κ (Prod.map (id : γ → γ) f) (measurable_id.prod_map hf.measurable)
  condKernelBorelSnd κ (isCondKernelCDF_condKernelCDF κ')

instance instIsMarkovKernel_condKernelBorel (κ : kernel α (γ × Ω)) [IsFiniteKernel κ] :
    IsMarkovKernel (condKernelBorel κ) := by
  rw [condKernelBorel]
  infer_instance

lemma compProd_fst_condKernelBorel (κ : kernel α (γ × Ω)) [IsFiniteKernel κ] :
    fst κ ⊗ₖ condKernelBorel κ = κ := by
  rw [condKernelBorel, compProd_fst_condKernelBorelSnd]

end CountablyGenerated

section Unit

/-- Auxiliary definition for `MeasureTheory.Measure.condKernel` and
`ProbabilityTheory.kernel.condKernel`.
A conditional kernel for `κ : kernel Unit (α × Ω)` where `Ω` is standard Borel. -/
noncomputable
def condKernelUnitBorel (κ : kernel Unit (α × Ω)) [IsFiniteKernel κ] : kernel (Unit × α) Ω :=
  let f := embeddingReal Ω
  let hf := measurableEmbedding_embeddingReal Ω
  let κ' := map κ (Prod.map (id : α → α) f) (measurable_id.prod_map hf.measurable)
  condKernelBorelSnd κ (isCondKernelCDF_condCDF (κ' ()))

instance instIsMarkovKernel_condKernelUnitBorel (κ : kernel Unit (α × Ω)) [IsFiniteKernel κ] :
    IsMarkovKernel (condKernelUnitBorel κ) := by
  rw [condKernelUnitBorel]
  infer_instance

lemma compProd_fst_condKernelUnitBorel (κ : kernel Unit (α × Ω)) [IsFiniteKernel κ] :
    fst κ ⊗ₖ condKernelUnitBorel κ = κ := by
  rw [condKernelUnitBorel, compProd_fst_condKernelBorelSnd]

end Unit

section Measure

variable {ρ : Measure (α × Ω)} [IsFiniteMeasure ρ]

/-- Conditional kernel of a measure on a product space: a Markov kernel such that
`ρ = ρ.fst ⊗ₘ ρ.condKernel` (see `MeasureTheory.Measure.compProd_fst_condKernel`). -/
noncomputable
def _root_.MeasureTheory.Measure.condKernel (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ] :
    kernel α Ω :=
  comap (condKernelUnitBorel (const Unit ρ)) (fun a ↦ ((), a)) measurable_prod_mk_left
#align measure_theory.measure.cond_kernel MeasureTheory.Measure.condKernel

lemma _root_.MeasureTheory.Measure.condKernel_apply (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ]
    (a : α) :
    ρ.condKernel a = condKernelUnitBorel (const Unit ρ) ((), a) := rfl

instance _root_.MeasureTheory.Measure.instIsMarkovKernel_condKernel
    (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ] :
    IsMarkovKernel ρ.condKernel := by
  rw [Measure.condKernel]
  infer_instance

/-- **Disintegration** of finite product measures on `α × Ω`, where `Ω` is standard Borel. Such a
measure can be written as the composition-product of `ρ.fst` (marginal measure over `α`) and
a Markov kernel from `α` to `Ω`. We call that Markov kernel `ρ.condKernel`. -/
lemma _root_.MeasureTheory.Measure.compProd_fst_condKernel
    (ρ : Measure (α × Ω)) [IsFiniteMeasure ρ] :
    ρ.fst ⊗ₘ ρ.condKernel = ρ := by
  have h1 : const Unit (Measure.fst ρ) = fst (const Unit ρ) := by
    ext
    simp only [fst_apply, Measure.fst, const_apply]
  have h2 : prodMkLeft Unit (Measure.condKernel ρ)
      = condKernelUnitBorel (const Unit ρ) := by
    ext
    simp only [prodMkLeft_apply, Measure.condKernel_apply]
  rw [Measure.compProd, h1, h2, compProd_fst_condKernelUnitBorel]
  simp
#align probability_theory.measure_eq_comp_prod MeasureTheory.Measure.compProd_fst_condKernel

/-- Auxiliary lemma for `condKernel_apply_of_ne_zero`. -/
lemma _root_.MeasureTheory.Measure.condKernel_apply_of_ne_zero_of_measurableSet
    [MeasurableSingletonClass α] {x : α} (hx : ρ.fst {x} ≠ 0) {s : Set Ω} (hs : MeasurableSet s) :
    ρ.condKernel x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s) := by
  nth_rewrite 3 [← ρ.compProd_fst_condKernel]
  rw [Measure.compProd_apply (measurableSet_prod.mpr (Or.inl ⟨measurableSet_singleton x, hs⟩))]
  classical
  have : ∀ a, ρ.condKernel a (Prod.mk a ⁻¹' {x} ×ˢ s)
      = ({x} : Set α).indicator (fun a ↦ ρ.condKernel a s) a := by
    intro a
    by_cases hax : a = x
    · simp only [hax, singleton_prod, mem_singleton_iff, indicator_of_mem]
      congr with y
      simp
    · simp only [singleton_prod, mem_singleton_iff, hax, not_false_eq_true, indicator_of_not_mem]
      have : Prod.mk a ⁻¹' (Prod.mk x '' s) = ∅ := by
        ext y
        simp [Ne.symm hax]
      simp only [this, measure_empty]
  simp_rw [this]
  rw [MeasureTheory.lintegral_indicator _ (measurableSet_singleton x)]
  simp only [Measure.restrict_singleton, lintegral_smul_measure, lintegral_dirac]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hx (measure_ne_top ρ.fst _), one_mul]

/-- If the singleton `{x}` has non-zero mass for `ρ.fst`, then for all `s : Set Ω`,
`ρ.condKernel x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s)` . -/
lemma _root_.MeasureTheory.Measure.condKernel_apply_of_ne_zero [MeasurableSingletonClass α]
    {x : α} (hx : ρ.fst {x} ≠ 0) (s : Set Ω) :
    ρ.condKernel x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s) := by
  have : ρ.condKernel x s = ((ρ.fst {x})⁻¹ • ρ).comap (fun (y : Ω) ↦ (x, y)) s := by
    congr 2 with s hs
    simp [Measure.condKernel_apply_of_ne_zero_of_measurableSet hx hs,
      (measurableEmbedding_prod_mk_left x).comap_apply]
  simp [this, (measurableEmbedding_prod_mk_left x).comap_apply, hx]

end Measure

section Countable

variable [Countable α]

/-- Auxiliary definition for `ProbabilityTheory.kernel.condKernel`.
A conditional kernel for `κ : kernel α (β × Ω)` where `α` is countable and `Ω` is standard Borel. -/
noncomputable
def condKernelCountable (κ : kernel α (β × Ω)) [IsFiniteKernel κ] : kernel (α × β) Ω where
  val p := (κ p.1).condKernel p.2
  property := by
    change Measurable ((fun q : β × α ↦ (κ q.2).condKernel q.1) ∘ Prod.swap)
    refine (measurable_from_prod_countable' (fun a ↦ ?_) ?_).comp measurable_swap
    · exact kernel.measurable (κ a).condKernel
    · intro y y' x hy'
      have : κ y' = κ y := by
        ext s hs
        exact mem_of_mem_measurableAtom hy'
          (kernel.measurable_coe κ hs (measurableSet_singleton (κ y s))) rfl
      simp [this]

lemma condKernelCountable_apply (κ : kernel α (β × Ω)) [IsFiniteKernel κ] (p : α × β) :
    condKernelCountable κ p = (κ p.1).condKernel p.2 := rfl

instance instIsMarkovKernel_condKernelCountable (κ : kernel α (β × Ω)) [IsFiniteKernel κ] :
    IsMarkovKernel (condKernelCountable κ) :=
  ⟨fun p ↦ (Measure.instIsMarkovKernel_condKernel (κ p.1)).isProbabilityMeasure p.2⟩

lemma compProd_fst_condKernelCountable (κ : kernel α (β × Ω)) [IsFiniteKernel κ] :
    fst κ ⊗ₖ condKernelCountable κ = κ := by
  ext a s hs
  have h := (κ a).compProd_fst_condKernel
  conv_rhs => rw [← h]
  simp_rw [compProd_apply _ _ _ hs, condKernelCountable_apply, Measure.compProd_apply hs]
  congr

end Countable

section CountableOrCountablyGenerated

open Classical in

/-- Conditional kernel of a kernel `κ : kernel α (β × Ω)`: a Markov kernel such that
`fst κ ⊗ₖ condKernel κ = κ` (see `MeasureTheory.Measure.compProd_fst_condKernel`).
It exists whenever `Ω` is standard Borel and either `α` is countable
or `β` is countably generated. -/
noncomputable
irreducible_def condKernel [h : CountableOrCountablyGenerated α β]
    (κ : kernel α (β × Ω)) [IsFiniteKernel κ] :
    kernel (α × β) Ω :=
  if hα : Countable α then condKernelCountable κ
  else letI := h.countableOrCountablyGenerated.resolve_left hα; condKernelBorel κ

/-- `condKernel κ` is a Markov kernel. -/
instance instIsMarkovKernel_condKernel [CountableOrCountablyGenerated α β]
    (κ : kernel α (β × Ω)) [IsFiniteKernel κ] :
    IsMarkovKernel (condKernel κ) := by
  rw [condKernel_def]
  split_ifs <;> infer_instance

/-- **Disintegration** of finite kernels.
The composition-product of `fst κ` and `condKernel κ` is equal to `κ`. -/
lemma compProd_fst_condKernel [hαβ : CountableOrCountablyGenerated α β]
    (κ : kernel α (β × Ω)) [IsFiniteKernel κ] :
    fst κ ⊗ₖ condKernel κ = κ := by
  rw [condKernel_def]
  split_ifs with h
  · exact compProd_fst_condKernelCountable κ
  · have := hαβ.countableOrCountablyGenerated.resolve_left h
    exact compProd_fst_condKernelBorel κ

end CountableOrCountablyGenerated

end ProbabilityTheory.kernel
