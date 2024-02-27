import Mathlib.MeasureTheory.OuterMeasure.Defs
import Mathlib.Order.Disjointed

open Set Filter
open scoped ENNReal BigOperators Topology

namespace MeasureTheory

variable {α F : Type*} [FunLike F (Set α) ℝ≥0∞] [OuterMeasureClass F α] {μ ν : F} {s t : Set α}

@[gcongr] alias measure_mono := OuterMeasureClass.measure_mono
@[simp] alias measure_empty := OuterMeasureClass.measure_empty

protected theorem Measure.ext_nonempty (h : ∀ s, s.Nonempty → μ s = ν s) : μ = ν :=
  DFunLike.ext _ _ fun s ↦ s.eq_empty_or_nonempty.elim (fun h ↦ by simp [h]) (h s)

theorem measure_mono_null (ht : t ⊆ s) (hs : μ s = 0) : μ t = 0 :=
  nonpos_iff_eq_zero.1 <| hs ▸ measure_mono μ ht

theorem measure_pos_of_subset_ne_zero (μ : F) (hsub : s ⊆ t) (hs : μ s ≠ 0) : 0 < μ t :=
  lt_of_lt_of_le (pos_iff_ne_zero.mpr hs) (measure_mono μ hsub)

@[gcongr]
theorem measure_mono_both (hle : μ ≤ ν) (hst : s ⊆ t) : μ s ≤ ν t :=
  (hle s).trans (measure_mono ν hst)

theorem measure_iUnion_le {ι : Type*} [Countable ι] (μ : F) (s : ι → Set α) :
    μ (⋃ i, s i) ≤ ∑' i, μ (s i) := by
  refine rel_iSup_tsum μ (measure_empty μ) (· ≤ ·) (fun t ↦ ?_) _
  calc
    μ (⋃ i, t i) = μ (⋃ i, disjointed t i) := by rw [iUnion_disjointed]
    _ ≤ ∑' i, μ (disjointed t i) :=
      OuterMeasureClass.measure_iUnion_nat_le _ _ (disjoint_disjointed _)
    _ ≤ ∑' i, μ (t i) := ENNReal.tsum_le_tsum fun _ ↦ measure_mono μ <| disjointed_subset _ _

theorem measure_biUnion_le {ι : Type*} {I : Set ι} (μ : F) (hI : I.Countable) (s : ι → Set α) :
    μ (⋃ i ∈ I, s i) ≤ ∑' i : I, μ (s i) := by
  have := hI.to_subtype
  rw [biUnion_eq_iUnion]
  apply measure_iUnion_le

theorem measure_biUnion_finset_le {ι : Type*} (μ : F) (I : Finset ι) (s : ι → Set α) :
    μ (⋃ i ∈ I, s i) ≤ ∑ i in I, μ (s i) :=
  (measure_biUnion_le μ I.countable_toSet s).trans_eq <| I.tsum_subtype (μ <| s ·)

theorem measure_iUnion_fintype_le {ι : Type*} [Fintype ι] (μ : F) (s : ι → Set α) :
    μ (⋃ i, s i) ≤ ∑ i, μ (s i) := by
  simpa using measure_biUnion_finset_le μ Finset.univ s

theorem measure_union_le (μ : F) (s t : Set α) : μ (s ∪ t) ≤ μ s + μ t := by
  simpa [union_eq_iUnion] using measure_iUnion_fintype_le μ (cond · s t)

theorem measure_le_inter_add_diff (μ : F) (s t : Set α) : μ s ≤ μ (s ∩ t) + μ (s \ t) := by
  simpa using measure_union_le μ (s ∩ t) (s \ t)

theorem measure_diff_null (μ : F) (s : Set α) (ht : μ t = 0) : μ (s \ t) = μ s :=
  (measure_mono μ <| diff_subset _ _).antisymm <| calc
    μ s ≤ μ (s ∩ t) + μ (s \ t) := measure_le_inter_add_diff _ _ _
    _ ≤ μ t + μ (s \ t) := by gcongr; apply inter_subset_right
    _ = μ (s \ t) := by simp [ht]

theorem measure_biUnion_null_iff {ι : Type*} {I : Set ι} (hI : I.Countable) {s : ι → Set α} :
    μ (⋃ i ∈ I, s i) = 0 ↔ ∀ i ∈ I, μ (s i) = 0 := by
  refine ⟨fun h i hi ↦ measure_mono_null (subset_biUnion_of_mem hi) h, fun h ↦ ?_⟩
  have _ := hI.to_subtype
  simpa [h] using measure_iUnion_le μ fun x : I ↦ s x

theorem measure_sUnion_null_iff {S : Set (Set α)} (hS : S.Countable) :
    μ (⋃₀ S) = 0 ↔ ∀ s ∈ S, μ s = 0 := by
  rw [sUnion_eq_biUnion, measure_biUnion_null_iff hS]

@[simp]
theorem measure_iUnion_null_iff {ι : Sort*} [Countable ι] {s : ι → Set α} :
    μ (⋃ i, s i) = 0 ↔ ∀ i, μ (s i) = 0 := by
  rw [← sUnion_range, measure_sUnion_null_iff (countable_range s), forall_range_iff]

alias ⟨_, measure_iUnion_null⟩ := measure_iUnion_null_iff

@[simp]
theorem measure_union_null_iff : μ (s ∪ t) = 0 ↔ μ s = 0 ∧ μ t = 0 := by
  simp [union_eq_iUnion, and_comm]

theorem measure_union_null (hs : μ s = 0) (ht : μ t = 0) : μ (s ∪ t) = 0 := by simp [*]

/-- Let `μ` be an (outer) measure; let `s : ι → Set α` be a sequence of sets, `S = ⋃ n, s n`.
If `μ (S \ s n)` tends to zero along some nontrivial filter (usually `Filter.atTop` on `ι = ℕ`),
then `μ S = ⨆ n, μ (s n)`. -/
theorem measure_iUnion_of_tendsto_zero {ι} (μ : F) {s : ι → Set α} (l : Filter ι) [NeBot l]
    (h0 : Tendsto (fun k => μ ((⋃ n, s n) \ s k)) l (𝓝 0)) : μ (⋃ n, s n) = ⨆ n, μ (s n) := by
  refine le_antisymm ?_ <| iSup_le fun n ↦ measure_mono μ <| subset_iUnion _ _
  set S := ⋃ n, s n
  set M := ⨆ n, μ (s n)
  have A : ∀ k, μ S ≤ M + μ (S \ s k) := fun k ↦ calc
    μ S ≤ μ (S ∩ s k) + μ (S \ s k) := measure_le_inter_add_diff _ _ _
    _ ≤ μ (s k) + μ (S \ s k) := by gcongr; apply inter_subset_right
    _ ≤ M + μ (S \ s k) := by gcongr; exact le_iSup (μ ∘ s) k
  have B : Tendsto (fun k ↦ M + μ (S \ s k)) l (𝓝 M) := by simpa using tendsto_const_nhds.add h0
  exact ge_of_tendsto' B A

end MeasureTheory
