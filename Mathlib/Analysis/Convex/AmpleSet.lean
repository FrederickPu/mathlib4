/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Michael Rothgang, Floris van Doorn
-/
import Mathlib.Analysis.Convex.Normed
import Mathlib.LinearAlgebra.AffineSpace.ContinuousAffineEquiv

/-!
# Ample subsets of real vector spaces

In this file we study ample set in real vector spaces. A set is ample if all its connected
component have full convex hull. Ample sets are an important ingredient for defining ample
differential relations.

## Main results
- `ampleSet_empty` and `ampleSet_univ`: the empty set and `univ` are ample
- `AmpleSet.union`: the union of two ample sets is ample
- `AmpleSet.{pre}image`: being ample is invariant under continuous affine equivalences
- `AmpleSet.vadd`: in particular, ampleness is invariant under affine translations

- `AmpleSet.of_two_le_codim`: a linear subspace of codimension at least two has an ample complement.
This is the crucial geometric ingredient which allows to apply convex integration
to the theory of immersions in positive codimension.

## Implementation notes

A priori, the definition of ample subset asks for a vector space structure and a topology on the
ambient type without any link between those structures. In practice, we care most about using these
for finite dimensional vector spaces with their natural topology.

All vector spaces in the file are real vector spaces. While the definition generalises to other
connected fields, that is not useful in practice.

## Tags
ample set
-/

/-! ## Definition and invariance -/

open Set

variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

/-- A subset of a topological real vector space is ample
if the convex hull of each of its connected components is the full space. -/
def AmpleSet (s : Set F) : Prop :=
  ∀ x ∈ s, convexHull ℝ (connectedComponentIn s x) = univ

/-- A whole vector space is ample. -/
@[simp]
theorem ampleSet_univ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    AmpleSet (univ : Set F) := by
  intro x _
  rw [connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ, convexHull_univ]

/-- The empty set in a vector space is ample. -/
@[simp]
theorem ampleSet_empty : AmpleSet (∅ : Set F) := fun _ h ↦ False.elim h

/-- The union of two ample sets is ample. -/
theorem AmpleSet.union {s t : Set F} (hs : AmpleSet s) (ht : AmpleSet t) : AmpleSet (s ∪ t) := by
  intro x hx
  rcases hx with (h | h)
  -- The connected component of x ∈ s in s ∪ t contains the connected component of x in s,
  -- similarly for `t`.
  · rw [← Set.univ_subset_iff, ← hs x h]
    apply convexHull_mono
    apply connectedComponentIn_mono
    apply subset_union_left
  · rw [← Set.univ_subset_iff, ← ht x h]
    apply convexHull_mono
    apply connectedComponentIn_mono
    apply subset_union_right

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- Images of ample sets under continuous affine equivalences are ample. -/
theorem AmpleSet.image {s : Set E} (h : AmpleSet s) (L : E ≃ᵃL[ℝ] F) :
    AmpleSet (L '' s) := fun x hx ↦ by
  rw [L.image_eq_preimage] at hx
  have : L '' connectedComponentIn s (L.symm x) = connectedComponentIn (L '' s) x := by
    conv_rhs => rw [← L.apply_symm_apply x]
    exact (L.toHomeomorph).image_connectedComponentIn hx
  rw [← this]
  -- when mathlib4#11298 lands, switch argument order
  refine (AffineMap.image_convexHull _ L.toAffineMap).symm.trans ?_
  rw [h (L.symm x) hx, image_univ]
  exact L.surjective.range_eq

/-- Preimages of ample sets under continuous affine equivalences are ample. -/
theorem AmpleSet.preimage {s : Set F} (h : AmpleSet s) (L : E ≃ᵃL[ℝ] F) : AmpleSet (L ⁻¹' s) := by
  rw [← L.image_symm_eq_preimage]
  exact h.image L.symm

/-! ## Subspaces of codimension at least two have ample complement -/
section Codimension

variable {E F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [TopologicalAddGroup F] [ContinuousSMul ℝ F]

/-- Let `E` be a linear subspace in a real vector space.
If `E` has codimension at least two, its complement is ample. -/
theorem AmpleSet.of_two_le_codim {E : Submodule ℝ F} (hcodim : 2 ≤ Module.rank ℝ (F ⧸ E)) :
    AmpleSet (Eᶜ : Set F) := fun x hx ↦ by
  rw [E.connectedComponentIn_eq_self_of_two_le_codim hcodim hx, eq_univ_iff_forall]
  intro y
  by_cases h : y ∈ E
  · obtain ⟨z, hz⟩ : ∃ z, z ∉ E := by
      rw [← not_forall, ← Submodule.eq_top_iff']
      rintro rfl
      simp [rank_zero_iff.2 inferInstance] at hcodim
    refine segment_subset_convexHull ?_ ?_ (mem_segment_sub_add y z) <;>
      simpa [sub_eq_add_neg, Submodule.add_mem_iff_right _ h]
  · exact subset_convexHull ℝ (Eᶜ : Set F) h

end Codimension
