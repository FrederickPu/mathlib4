import Mathlib.Topology.Instances.ENNReal

open scoped ENNReal

variable {α : Type*}

namespace MeasureTheory

/-- An outer measure is a countably subadditive monotone function that sends `∅` to `0`. -/
structure OuterMeasure (α : Type*) where
  protected measureOf : Set α → ℝ≥0∞
  protected empty : measureOf ∅ = 0
  protected mono : ∀ {s₁ s₂}, s₁ ⊆ s₂ → measureOf s₁ ≤ measureOf s₂
  protected iUnion_nat : ∀ s : ℕ → Set α, Pairwise (Disjoint on s) →
    measureOf (⋃ i, s i) ≤ ∑' i, measureOf (s i)
#align measure_theory.outer_measure MeasureTheory.OuterMeasure
#align measure_theory.outer_measure.measure_of MeasureTheory.OuterMeasure.measureOf
#align measure_theory.outer_measure.empty MeasureTheory.OuterMeasure.empty
#align measure_theory.outer_measure.mono MeasureTheory.OuterMeasure.mono
#align measure_theory.outer_measure.Union_nat MeasureTheory.OuterMeasure.iUnion_nat

class OuterMeasureClass (F : Type*) (α : outParam (Type*)) [FunLike F (Set α) ℝ≥0∞] where
  protected measure_empty (f : F) : f ∅ = 0
  protected measure_mono (f : F) {s t} : s ⊆ t → f s ≤ f t
  protected measure_iUnion_nat_le (f : F) (s : ℕ → Set α) : Pairwise (Disjoint on s) →
    f (⋃ i, s i) ≤ ∑' i, f (s i)

namespace OuterMeasure

instance : FunLike (OuterMeasure α) (Set α) ℝ≥0∞ where
  coe m := m.measureOf
  coe_injective' | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl

#noalign measure_theory.outer_measure.has_coe_to_fun

@[simp] theorem measureOf_eq_coe (m : OuterMeasure α) : m.measureOf = m := rfl
#align measure_theory.outer_measure.measure_of_eq_coe MeasureTheory.OuterMeasure.measureOf_eq_coe
 
instance : OuterMeasureClass (OuterMeasure α) α where
  measure_empty f := f.empty
  measure_mono f := f.mono
  measure_iUnion_nat_le f := f.iUnion_nat

end OuterMeasure
