/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.Semisimple
import Mathlib.Algebra.Lie.Weights.Cartan
import Mathlib.Algebra.Lie.Weights.Chain
import Mathlib.Algebra.Lie.Weights.Linear
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.PID
import Mathlib.LinearAlgebra.Trace

/-!
# The trace and Killing forms of a Lie algebra.

Let `L` be a Lie algebra with coefficients in a commutative ring `R`. Suppose `M` is a finite, free
`R`-module and we have a representation `φ : L → End M`. This data induces a natural bilinear form
`B` on `L`, called the trace form associated to `M`; it is defined as `B(x, y) = Tr (φ x) (φ y)`.

In the special case that `M` is `L` itself and `φ` is the adjoint representation, the trace form
is known as the Killing form.

We define the trace / Killing form in this file and prove some basic properties.

## Main definitions

 * `LieModule.traceForm`: a finite, free representation of a Lie algebra `L` induces a bilinear form
   on `L` called the trace Form.
 * `LieModule.traceForm_eq_zero_of_isNilpotent`: the trace form induced by a nilpotent
   representation of a Lie algebra vanishes.
 * `killingForm`: the adjoint representation of a (finite, free) Lie algebra `L` induces a bilinear
   form on `L` via the trace form construction.
 * `LieAlgebra.IsKilling`: a typeclass encoding the fact that a Lie algebra has a non-singular
   Killing form.
 * `LieAlgebra.IsKilling.ker_restrictBilinear_eq_bot_of_isCartanSubalgebra`: if the Killing form of
   a Lie algebra is non-singular, it remains non-singular when restricted to a Cartan subalgebra.
 * `LieAlgebra.IsKilling.isSemisimple`: if a Lie algebra has non-singular Killing form then it is
   semisimple.
 * `LieAlgebra.IsKilling.instIsLieAbelianOfIsCartanSubalgebra`: if the Killing form of a Lie
   algebra is non-singular, then its Cartan subalgebras are Abelian.
 * `LieAlgebra.IsKilling.span_weight_eq_top`: given a splitting Cartan subalgebra `H` of a
   finite-dimensional Lie algebra with non-singular Killing form, the corresponding roots span the
   dual space of `H`.
 * `LieAlgebra.IsKilling.coroot`: the coroot corresponding to a root.
 * `LieAlgebra.IsKilling.isCompl_ker_weight_corootSpace`: given a root `α` with respect
   to a Cartan subalgebra `H`, we have a natural decomposition of `H` which we write informally as:
   `H = ker α ⊕ ⁅H(α), H(-α)⁆`, where `H(±α)` are the root spaces of `±α`.

## TODO

 * Prove that in characteristic zero, a semisimple Lie algebra has non-singular Killing form.
-/

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [Module.Free R M] [Module.Finite R M]
  [Field K] [LieAlgebra K L] [Module K M] [LieModule K L M] [FiniteDimensional K M]

local notation "φ" => LieModule.toEndomorphism R L M

open LinearMap (trace)
open Set BigOperators FiniteDimensional

namespace LieModule

/-- A finite, free representation of a Lie algebra `L` induces a bilinear form on `L` called
the trace Form. See also `killingForm`. -/
noncomputable def traceForm : LinearMap.BilinForm R L :=
  ((LinearMap.mul _ _).compl₁₂ (φ).toLinearMap (φ).toLinearMap).compr₂ (trace R M)

lemma traceForm_apply_apply (x y : L) :
    traceForm R L M x y = trace R _ (φ x ∘ₗ φ y) :=
  rfl

lemma traceForm_comm (x y : L) : traceForm R L M x y = traceForm R L M y x :=
  LinearMap.trace_mul_comm R (φ x) (φ y)

@[simp] lemma traceForm_flip : (traceForm R L M).flip = traceForm R L M :=
  Eq.symm <| LinearMap.ext₂ <| traceForm_comm R L M

/-- The trace form of a Lie module is compatible with the action of the Lie algebra.

See also `LieModule.traceForm_apply_lie_apply'`. -/
lemma traceForm_apply_lie_apply (x y z : L) :
    traceForm R L M ⁅x, y⁆ z = traceForm R L M x ⁅y, z⁆ := by
  calc traceForm R L M ⁅x, y⁆ z
      = trace R _ (φ ⁅x, y⁆ ∘ₗ φ z) := by simp only [traceForm_apply_apply]
    _ = trace R _ ((φ x * φ y - φ y * φ x) * φ z) := ?_
    _ = trace R _ (φ x * (φ y * φ z)) - trace R _ (φ y * (φ x * φ z)) := ?_
    _ = trace R _ (φ x * (φ y * φ z)) - trace R _ (φ x * (φ z * φ y)) := ?_
    _ = traceForm R L M x ⁅y, z⁆ := ?_
  · simp only [LieHom.map_lie, Ring.lie_def, ← LinearMap.mul_eq_comp]
  · simp only [sub_mul, mul_sub, map_sub, mul_assoc]
  · simp only [LinearMap.trace_mul_cycle' R (φ x) (φ z) (φ y)]
  · simp only [traceForm_apply_apply, LieHom.map_lie, Ring.lie_def, mul_sub, map_sub,
      ← LinearMap.mul_eq_comp]

/-- Given a representation `M` of a Lie algebra `L`, the action of any `x : L` is skew-adjoint wrt
the trace form. -/
lemma traceForm_apply_lie_apply' (x y z : L) :
    traceForm R L M ⁅x, y⁆ z = - traceForm R L M y ⁅x, z⁆ :=
  calc traceForm R L M ⁅x, y⁆ z
      = - traceForm R L M ⁅y, x⁆ z := by rw [← lie_skew x y, map_neg, LinearMap.neg_apply]
    _ = - traceForm R L M y ⁅x, z⁆ := by rw [traceForm_apply_lie_apply]

/-- This lemma justifies the terminology "invariant" for trace forms. -/
@[simp] lemma lie_traceForm_eq_zero (x : L) : ⁅x, traceForm R L M⁆ = 0 := by
  ext y z
  rw [LieHom.lie_apply, LinearMap.sub_apply, Module.Dual.lie_apply, LinearMap.zero_apply,
    LinearMap.zero_apply, traceForm_apply_lie_apply', sub_self]

@[simp] lemma traceForm_eq_zero_of_isNilpotent [IsReduced R] [IsNilpotent R L M] :
    traceForm R L M = 0 := by
  ext x y
  simp only [traceForm_apply_apply, LinearMap.zero_apply, ← isNilpotent_iff_eq_zero]
  apply LinearMap.isNilpotent_trace_of_isNilpotent
  exact isNilpotent_toEndomorphism_of_isNilpotent₂ R L M x y

@[simp]
lemma traceForm_weightSpace_eq [IsDomain R] [IsPrincipalIdealRing R]
    [LieAlgebra.IsNilpotent R L] [IsNoetherian R M] [LinearWeights R L M] (χ : L → R) (x y : L) :
    traceForm R L (weightSpace M χ) x y = finrank R (weightSpace M χ) • (χ x * χ y) := by
  set d := finrank R (weightSpace M χ)
  have h₁ : χ y • d • χ x - χ y • χ x • (d : R) = 0 := by simp [mul_comm (χ x)]
  have h₂ : χ x • d • χ y = d • (χ x * χ y) := by
    simpa [nsmul_eq_mul, smul_eq_mul] using mul_left_comm (χ x) d (χ y)
  have := traceForm_eq_zero_of_isNilpotent R L (shiftedWeightSpace R L M χ)
  replace this := LinearMap.congr_fun (LinearMap.congr_fun this x) y
  rwa [LinearMap.zero_apply, LinearMap.zero_apply, traceForm_apply_apply,
    shiftedWeightSpace.toEndomorphism_eq, shiftedWeightSpace.toEndomorphism_eq,
    ← LinearEquiv.conj_comp, LinearMap.trace_conj', LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.sub_comp, map_sub, map_sub, map_sub, LinearMap.comp_smul, LinearMap.smul_comp,
    LinearMap.comp_id, LinearMap.id_comp, LinearMap.map_smul, LinearMap.map_smul,
    trace_toEndomorphism_weightSpace, trace_toEndomorphism_weightSpace,
    LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.id_comp, map_smul, map_smul,
    LinearMap.trace_id, ← traceForm_apply_apply, h₁, h₂, sub_zero, sub_eq_zero] at this

/-- The upper and lower central series of `L` are orthogonal wrt the trace form of any Lie module
`M`. -/
lemma traceForm_eq_zero_if_mem_lcs_of_mem_ucs {x y : L} (k : ℕ)
    (hx : x ∈ (⊤ : LieIdeal R L).lcs L k) (hy : y ∈ (⊥ : LieIdeal R L).ucs k) :
    traceForm R L M x y = 0 := by
  induction' k with k ih generalizing x y
  · replace hy : y = 0 := by simpa using hy
    simp [hy]
  · rw [LieSubmodule.ucs_succ, LieSubmodule.mem_normalizer] at hy
    simp_rw [LieIdeal.lcs_succ, ← LieSubmodule.mem_coeSubmodule,
      LieSubmodule.lieIdeal_oper_eq_linear_span', LieSubmodule.mem_top, true_and] at hx
    refine Submodule.span_induction hx ?_ ?_ (fun z w hz hw ↦ ?_) (fun t z hz ↦ ?_)
    · rintro - ⟨z, w, hw, rfl⟩
      rw [← lie_skew, map_neg, LinearMap.neg_apply, neg_eq_zero, traceForm_apply_lie_apply]
      exact ih hw (hy _)
    · simp
    · simp [hz, hw]
    · simp [hz]

lemma traceForm_apply_eq_zero_of_mem_lcs_of_mem_center {x y : L}
    (hx : x ∈ lowerCentralSeries R L L 1) (hy : y ∈ LieAlgebra.center R L) :
    traceForm R L M x y = 0 := by
  apply traceForm_eq_zero_if_mem_lcs_of_mem_ucs R L M 1
  · simpa using hx
  · simpa using hy

-- This is barely worth having: it usually follows from `LieModule.traceForm_eq_zero_of_isNilpotent`
@[simp] lemma traceForm_eq_zero_of_isTrivial [IsTrivial L M] :
    traceForm R L M = 0 := by
  ext x y
  suffices φ x ∘ₗ φ y = 0 by simp [traceForm_apply_apply, this]
  ext m
  simp

/-- Given a bilinear form `B` on a representation `M` of a nilpotent Lie algebra `L`, if `B` is
invariant (in the sense that the action of `L` is skew-adjoint wrt `B`) then components of the
Fitting decomposition of `M` are orthogonal wrt `B`. -/
lemma eq_zero_of_mem_weightSpace_mem_posFitting [LieAlgebra.IsNilpotent R L]
    {B : LinearMap.BilinForm R M} (hB : ∀ (x : L) (m n : M), B ⁅x, m⁆ n = - B m ⁅x, n⁆)
    {m₀ m₁ : M} (hm₀ : m₀ ∈ weightSpace M (0 : L → R)) (hm₁ : m₁ ∈ posFittingComp R L M) :
    B m₀ m₁ = 0 := by
  replace hB : ∀ x (k : ℕ) m n, B m ((φ x ^ k) n) = (- 1 : R) ^ k • B ((φ x ^ k) m) n := by
    intro x k
    induction k with
    | zero => simp
    | succ k ih =>
    intro m n
    replace hB : ∀ m, B m (φ x n) = (- 1 : R) • B (φ x m) n := by simp [hB]
    have : (-1 : R) ^ k • (-1 : R) = (-1 : R) ^ (k + 1) := by rw [pow_succ (-1 : R), smul_eq_mul]
    conv_lhs => rw [pow_succ, LinearMap.mul_eq_comp, LinearMap.comp_apply, ih, hB,
      ← (φ x).comp_apply, ← LinearMap.mul_eq_comp, ← pow_succ', ← smul_assoc, this]
  suffices ∀ (x : L) m, m ∈ posFittingCompOf R M x → B m₀ m = 0 by
    apply LieSubmodule.iSup_induction _ hm₁ this (map_zero _)
    aesop
  clear hm₁ m₁; intro x m₁ hm₁
  simp only [mem_weightSpace, Pi.zero_apply, zero_smul, sub_zero] at hm₀
  obtain ⟨k, hk⟩ := hm₀ x
  obtain ⟨m, rfl⟩ := (mem_posFittingCompOf R x m₁).mp hm₁ k
  simp [hB, hk]

lemma trace_toEndomorphism_eq_zero_of_mem_lcs
    {k : ℕ} {x : L} (hk : 1 ≤ k) (hx : x ∈ lowerCentralSeries R L L k) :
    trace R _ (toEndomorphism R L M x) = 0 := by
  replace hx : x ∈ lowerCentralSeries R L L 1 := antitone_lowerCentralSeries _ _ _ hk hx
  replace hx : x ∈ Submodule.span R {m | ∃ u v : L, ⁅u, v⁆ = m} := by
    rw [lowerCentralSeries_succ, ← LieSubmodule.mem_coeSubmodule,
      LieSubmodule.lieIdeal_oper_eq_linear_span'] at hx
    simpa using hx
  refine Submodule.span_induction (p := fun x ↦ trace R _ (toEndomorphism R L M x) = 0) hx
    (fun y ⟨u, v, huv⟩ ↦ ?_) ?_ (fun u v hu hv ↦ ?_) (fun t u hu ↦ ?_)
  · simp [← huv]
  · simp
  · simp [hu, hv]
  · simp [hu]

open TensorProduct

variable [LieAlgebra.IsNilpotent R L] [IsDomain R] [IsPrincipalIdealRing R]

lemma traceForm_eq_sum_weightSpaceOf [IsTriangularizable R L M] (z : L) :
    traceForm R L M =
    ∑ χ in (finite_weightSpaceOf_ne_bot R L M z).toFinset, traceForm R L (weightSpaceOf M χ z) := by
  ext x y
  have hxy : ∀ χ : R, MapsTo ((toEndomorphism R L M x).comp (toEndomorphism R L M y))
      (weightSpaceOf M χ z) (weightSpaceOf M χ z) :=
    fun χ m hm ↦ LieSubmodule.lie_mem _ <| LieSubmodule.lie_mem _ hm
  have hfin : {χ : R | (weightSpaceOf M χ z : Submodule R M) ≠ ⊥}.Finite := by
    convert finite_weightSpaceOf_ne_bot R L M z
    exact LieSubmodule.coeSubmodule_eq_bot_iff (weightSpaceOf M _ _)
  classical
  have hds := DirectSum.isInternal_submodule_of_independent_of_iSup_eq_top
    (LieSubmodule.independent_iff_coe_toSubmodule.mp <| independent_weightSpaceOf R L M z)
    (IsTriangularizable.iSup_eq_top z)
  simp only [LinearMap.coeFn_sum, Finset.sum_apply, traceForm_apply_apply,
    LinearMap.trace_eq_sum_trace_restrict' hds hfin hxy]
  exact Finset.sum_congr (by simp) (fun χ _ ↦ rfl)

-- In characteristic zero (or even just `LinearWeights R L M`) a stronger result holds (no
-- `⊓ LieAlgebra.center R L`) TODO prove this using `LieModule.traceForm_eq_sum_finrank_nsmul_mul`.
lemma lowerCentralSeries_one_inf_center_le_ker_traceForm :
    lowerCentralSeries R L L 1 ⊓ LieAlgebra.center R L ≤ LinearMap.ker (traceForm R L M) := by
  /- Sketch of proof (due to Zassenhaus):

  Let `z ∈ lowerCentralSeries R L L 1 ⊓ LieAlgebra.center R L` and `x : L`. We must show that
  `trace (φ x ∘ φ z) = 0` where `φ z : End R M` indicates the action of `z` on `M` (and likewise
  for `φ x`).

  Because `z` belongs to the indicated intersection, it has two key properties:
  (a) the trace of the action of `z` vanishes on any Lie module of `L`
      (see `LieModule.trace_toEndomorphism_eq_zero_of_mem_lcs`),
  (b) `z` commutes with all elements of `L`.

  If `φ x` were triangularizable, we could write `M` as a direct sum of generalized eigenspaces of
  `φ x`. Because `L` is nilpotent these are all Lie submodules, thus Lie modules in their own right,
  and thus by (a) above we learn that `trace (φ z) = 0` restricted to each generalized eigenspace.
  Because `z` commutes with `x`, this forces `trace (φ x ∘ φ z) = 0` on each generalized eigenspace,
  and so by summing the traces on each generalized eigenspace we learn the total trace is zero, as
  required (see `LinearMap.trace_comp_eq_zero_of_commute_of_trace_restrict_eq_zero`).

  To cater for the fact that `φ x` may not be triangularizable, we first extend the scalars from `R`
  to `AlgebraicClosure (FractionRing R)` and argue using the action of `A ⊗ L` on `A ⊗ M`. -/
  rintro z ⟨hz : z ∈ lowerCentralSeries R L L 1, hzc : z ∈ LieAlgebra.center R L⟩
  ext x
  rw [traceForm_apply_apply, LinearMap.zero_apply]
  let A := AlgebraicClosure (FractionRing R)
  suffices algebraMap R A (trace R _ ((φ z).comp (φ x))) = 0 by
    have _i : NoZeroSMulDivisors R A := NoZeroSMulDivisors.trans R (FractionRing R) A
    rw [← map_zero (algebraMap R A)] at this
    exact NoZeroSMulDivisors.algebraMap_injective R A this
  rw [← LinearMap.trace_baseChange, LinearMap.baseChange_comp, ← toEndomorphism_baseChange,
    ← toEndomorphism_baseChange]
  replace hz : 1 ⊗ₜ z ∈ lowerCentralSeries A (A ⊗[R] L) (A ⊗[R] L) 1 := by
    simp only [lowerCentralSeries_succ, lowerCentralSeries_zero] at hz ⊢
    rw [← LieSubmodule.baseChange_top, ← LieSubmodule.lie_baseChange]
    exact Submodule.tmul_mem_baseChange_of_mem 1 hz
  replace hzc : 1 ⊗ₜ[R] z ∈ LieAlgebra.center A (A ⊗[R] L) := by
    simp only [mem_maxTrivSubmodule] at hzc ⊢
    intro y
    exact y.induction_on rfl (fun a u ↦ by simp [hzc u]) (fun u v hu hv ↦ by simp [hu, hv])
  apply LinearMap.trace_comp_eq_zero_of_commute_of_trace_restrict_eq_zero
  · exact IsTriangularizable.iSup_eq_top (1 ⊗ₜ[R] x)
  · exact fun μ ↦ trace_toEndomorphism_eq_zero_of_mem_lcs A (A ⊗[R] L)
      (weightSpaceOf (A ⊗[R] M) μ (1 ⊗ₜ x)) (le_refl 1) hz
  · exact commute_toEndomorphism_of_mem_center_right (A ⊗[R] M) hzc (1 ⊗ₜ x)

/-- A nilpotent Lie algebra with a representation whose trace form is non-singular is Abelian. -/
lemma isLieAbelian_of_ker_traceForm_eq_bot (h : LinearMap.ker (traceForm R L M) = ⊥) :
    IsLieAbelian L := by
  simpa only [← disjoint_lowerCentralSeries_maxTrivSubmodule_iff R L L, disjoint_iff_inf_le,
    LieIdeal.coe_to_lieSubalgebra_to_submodule, LieSubmodule.coeSubmodule_eq_bot_iff, h]
    using lowerCentralSeries_one_inf_center_le_ker_traceForm R L M

end LieModule

namespace LieSubmodule

open LieModule (traceForm)

variable {R L M}
variable [IsDomain R] [IsPrincipalIdealRing R]
  (N : LieSubmodule R L M) (I : LieIdeal R L) (h : I ≤ N.idealizer) (x : L) {y : L} (hy : y ∈ I)

lemma trace_eq_trace_restrict_of_le_idealizer
    (hy' : ∀ m ∈ N, (φ x ∘ₗ φ y) m ∈ N := fun m _ ↦ N.lie_mem (N.mem_idealizer.mp (h hy) m)) :
    trace R M (φ x ∘ₗ φ y) = trace R N ((φ x ∘ₗ φ y).restrict hy') := by
  suffices ∀ m, ⁅x, ⁅y, m⁆⁆ ∈ N by simp [(φ x ∘ₗ φ y).trace_restrict_eq_of_forall_mem _ this]
  exact fun m ↦ N.lie_mem (h hy m)

lemma traceForm_eq_of_le_idealizer :
    traceForm R I N = I.restrictBilinear (traceForm R L M) := by
  ext ⟨x, hx⟩ ⟨y, hy⟩
  change _ = trace R M (φ x ∘ₗ φ y)
  rw [N.trace_eq_trace_restrict_of_le_idealizer I h x hy]
  rfl

/-- Note that this result is slightly stronger than it might look at first glance: we only assume
that `N` is trivial over `I` rather than all of `L`. This means that it applies in the important
case of an Abelian ideal (which has `M = L` and `N = I`). -/
lemma traceForm_eq_zero_of_isTrivial [LieModule.IsTrivial I N] :
    trace R M (φ x ∘ₗ φ y) = 0 := by
  let hy' : ∀ m ∈ N, (φ x ∘ₗ φ y) m ∈ N := fun m _ ↦ N.lie_mem (N.mem_idealizer.mp (h hy) m)
  suffices (φ x ∘ₗ φ y).restrict hy' = 0 by
    simp [this, N.trace_eq_trace_restrict_of_le_idealizer I h x hy]
  ext n
  suffices ⁅y, (n : M)⁆ = 0 by simp [this]
  exact Submodule.coe_eq_zero.mpr (LieModule.IsTrivial.trivial (⟨y, hy⟩ : I) n)

end LieSubmodule

section LieAlgebra

variable [Module.Free R L] [Module.Finite R L]

/-- A finite, free (as an `R`-module) Lie algebra `L` carries a bilinear form on `L`.

This is a specialisation of `LieModule.traceForm` to the adjoint representation of `L`. -/
noncomputable abbrev killingForm : LinearMap.BilinForm R L := LieModule.traceForm R L L

lemma killingForm_eq_zero_of_mem_zeroRoot_mem_posFitting
    (H : LieSubalgebra R L) [LieAlgebra.IsNilpotent R H]
    {x₀ x₁ : L}
    (hx₀ : x₀ ∈ LieAlgebra.zeroRootSubalgebra R L H)
    (hx₁ : x₁ ∈ LieModule.posFittingComp R H L) :
    killingForm R L x₀ x₁ = 0 :=
  LieModule.eq_zero_of_mem_weightSpace_mem_posFitting R H L
    (fun x y z ↦ LieModule.traceForm_apply_lie_apply' R L L x y z) hx₀ hx₁

namespace LieIdeal

variable (I : LieIdeal R L)

/-- The orthogonal complement of an ideal with respect to the killing form is an ideal. -/
noncomputable def killingCompl : LieIdeal R L :=
  { LinearMap.ker ((killingForm R L).compl₁₂ LinearMap.id I.subtype) with
    lie_mem := by
      intro x y hy
      ext ⟨z, hz⟩
      suffices killingForm R L ⁅x, y⁆ z = 0 by simpa
      rw [LieModule.traceForm_comm, ← LieModule.traceForm_apply_lie_apply, LieModule.traceForm_comm]
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        Submodule.mem_toAddSubmonoid, LinearMap.mem_ker] at hy
      replace hy := LinearMap.congr_fun hy ⟨⁅z, x⁆, lie_mem_left R L I z x hz⟩
      simpa using hy }

@[simp] lemma mem_killingCompl {x : L} :
    x ∈ I.killingCompl ↔ ∀ y ∈ I, killingForm R L x y = 0 := by
  change x ∈ LinearMap.ker ((killingForm R L).compl₁₂ LinearMap.id I.subtype) ↔ _
  simp only [LinearMap.mem_ker, LieModule.traceForm_apply_apply, LinearMap.ext_iff,
    LinearMap.compl₁₂_apply, LinearMap.id_coe, id_eq, Submodule.coeSubtype,
    LieModule.traceForm_apply_apply, LinearMap.zero_apply, Subtype.forall]
  rfl

lemma coe_killingCompl_top :
    killingCompl R L ⊤ = LinearMap.ker (killingForm R L) := by
  ext
  simp [LinearMap.ext_iff]

variable [IsDomain R] [IsPrincipalIdealRing R]

lemma killingForm_eq :
    killingForm R I = I.restrictBilinear (killingForm R L) :=
  LieSubmodule.traceForm_eq_of_le_idealizer I I <| by simp

lemma restrictBilinear_killingForm :
    I.restrictBilinear (killingForm R L) = LieModule.traceForm R I L :=
  rfl

@[simp] lemma le_killingCompl_top_of_isLieAbelian [IsLieAbelian I] :
    I ≤ LieIdeal.killingCompl R L ⊤ := by
  intro x (hx : x ∈ I)
  simp only [mem_killingCompl, LieSubmodule.mem_top, forall_true_left]
  intro y
  rw [LieModule.traceForm_comm, LieModule.traceForm_apply_apply]
  exact LieSubmodule.traceForm_eq_zero_of_isTrivial I I (by simp) _ hx

end LieIdeal

namespace LieAlgebra

/-- We say a Lie algebra is Killing if its Killing form is non-singular.

NB: This is not standard terminology (the literature does not seem to name Lie algebras with this
property). -/
class IsKilling : Prop :=
  /-- We say a Lie algebra is Killing if its Killing form is non-singular. -/
  killingCompl_top_eq_bot : LieIdeal.killingCompl R L ⊤ = ⊥

attribute [simp] IsKilling.killingCompl_top_eq_bot

namespace IsKilling

variable [IsKilling R L]

@[simp] lemma ker_killingForm_eq_bot :
    LinearMap.ker (killingForm R L) = ⊥ := by
  simp [← LieIdeal.coe_killingCompl_top, killingCompl_top_eq_bot]

/-- If the Killing form of a Lie algebra is non-singular, it remains non-singular when restricted
to a Cartan subalgebra. -/
lemma ker_restrictBilinear_eq_bot_of_isCartanSubalgebra
    [IsNoetherian R L] [IsArtinian R L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    LinearMap.ker (H.restrictBilinear (killingForm R L)) = ⊥ := by
  have h : Codisjoint (rootSpace H 0) (LieModule.posFittingComp R H L) :=
    (LieModule.isCompl_weightSpace_zero_posFittingComp R H L).codisjoint
  replace h : Codisjoint (H : Submodule R L) (LieModule.posFittingComp R H L : Submodule R L) := by
    rwa [codisjoint_iff, ← LieSubmodule.coe_toSubmodule_eq_iff, LieSubmodule.sup_coe_toSubmodule,
      LieSubmodule.top_coeSubmodule, rootSpace_zero_eq R L H, LieSubalgebra.coe_toLieSubmodule,
      ← codisjoint_iff] at h
  suffices this : ∀ m₀ ∈ H, ∀ m₁ ∈ LieModule.posFittingComp R H L, killingForm R L m₀ m₁ = 0 by
    simp [LinearMap.ker_restrictBilinear_eq_of_codisjoint h this]
  intro m₀ h₀ m₁ h₁
  exact killingForm_eq_zero_of_mem_zeroRoot_mem_posFitting R L H (le_zeroRootSubalgebra R L H h₀) h₁

lemma restrictBilinear_killingForm (H : LieSubalgebra R L) :
    H.restrictBilinear (killingForm R L) = LieModule.traceForm R H L :=
  rfl

@[simp] lemma ker_traceForm_eq_bot_of_isCartanSubalgebra
    [IsNoetherian R L] [IsArtinian R L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    LinearMap.ker (LieModule.traceForm R H L) = ⊥ :=
  ker_restrictBilinear_eq_bot_of_isCartanSubalgebra R L H

/-- The converse of this is true over a field of characteristic zero. There are counterexamples
over fields with positive characteristic. -/
instance isSemisimple [IsDomain R] [IsPrincipalIdealRing R] : IsSemisimple R L := by
  refine' (isSemisimple_iff_no_abelian_ideals R L).mpr fun I hI ↦ _
  rw [eq_bot_iff, ← killingCompl_top_eq_bot]
  exact I.le_killingCompl_top_of_isLieAbelian

-- TODO: formalize a positive-characteristic counterexample to the above instance

instance instIsLieAbelianOfIsCartanSubalgebra
    [IsDomain R] [IsPrincipalIdealRing R] [IsArtinian R L]
    (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    IsLieAbelian H :=
  LieModule.isLieAbelian_of_ker_traceForm_eq_bot R H L <|
    ker_restrictBilinear_eq_bot_of_isCartanSubalgebra R L H

end IsKilling

end LieAlgebra

end LieAlgebra

section Field

open LieModule FiniteDimensional
open Submodule (span subset_span)

namespace LieModule

variable [LieAlgebra.IsNilpotent K L] [LinearWeights K L M] [IsTriangularizable K L M]

lemma traceForm_eq_sum_finrank_nsmul_mul (x y : L) :
    traceForm K L M x y = ∑ χ in weight K L M, finrank K (weightSpace M χ) • (χ x * χ y) := by
  have hxy : ∀ χ : L → K, MapsTo (toEndomorphism K L M x ∘ₗ toEndomorphism K L M y)
      (weightSpace M χ) (weightSpace M χ) :=
    fun χ m hm ↦ LieSubmodule.lie_mem _ <| LieSubmodule.lie_mem _ hm
  have hfin : {χ : L → K | (weightSpace M χ : Submodule K M) ≠ ⊥}.Finite := by
    convert finite_weightSpace_ne_bot K L M
    exact LieSubmodule.coeSubmodule_eq_bot_iff (weightSpace M _)
  classical
  have hds := DirectSum.isInternal_submodule_of_independent_of_iSup_eq_top
    (LieSubmodule.independent_iff_coe_toSubmodule.mp <| independent_weightSpace K L M)
    (LieSubmodule.iSup_eq_top_iff_coe_toSubmodule.mp <| iSup_weightSpace_eq_top K L M)
  simp only [LinearMap.coeFn_sum, Finset.sum_apply, traceForm_apply_apply,
    LinearMap.trace_eq_sum_trace_restrict' hds hfin hxy]
  exact Finset.sum_congr (by simp) (fun χ _ ↦ traceForm_weightSpace_eq K L M χ x y)

lemma traceForm_eq_sum_finrank_nsmul :
    traceForm K L M = ∑ χ : weight K L M, finrank K (weightSpace M (χ : L → K)) •
      (weight.toLinear K L M χ).smulRight (weight.toLinear K L M χ) := by
  ext
  rw [traceForm_eq_sum_finrank_nsmul_mul, ← Finset.sum_attach]
  simp

-- The reverse inclusion should also hold: TODO prove this!
lemma range_traceForm_le_span_weight :
    LinearMap.range (traceForm K L M) ≤ span K (range (weight.toLinear K L M)) := by
  rintro - ⟨x, rfl⟩
  rw [LieModule.traceForm_eq_sum_finrank_nsmul, LinearMap.coeFn_sum, Finset.sum_apply]
  refine Submodule.sum_mem _ fun χ _ ↦ ?_
  simp_rw [LinearMap.smul_apply, LinearMap.coe_smulRight, weight.toLinear_apply,
    nsmul_eq_smul_cast (R := K)]
  exact Submodule.smul_mem _ _ <| Submodule.smul_mem _ _ <| subset_span <| mem_range_self χ

end LieModule

namespace LieAlgebra

variable [FiniteDimensional K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- For any `α` and `β`, the corresponding root spaces are orthogonal with respect to the Killing
form, provided `α + β ≠ 0`. -/
lemma killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero {α β : H → K} {x y : L}
    (hx : x ∈ rootSpace H α) (hy : y ∈ rootSpace H β) (hαβ : α + β ≠ 0) :
    killingForm K L x y = 0 := by
  /- If `ad R L z` is semisimple for all `z ∈ H` then writing `⟪x, y⟫ = killingForm K L x y`, there
  is a slick proof of this lemma that requires only invariance of the Killing form as follows.
  For any `z ∈ H`, we have:
  `α z • ⟪x, y⟫ = ⟪α z • x, y⟫ = ⟪⁅z, x⁆, y⟫ = - ⟪x, ⁅z, y⁆⟫ = - ⟪x, β z • y⟫ = - β z • ⟪x, y⟫`.
  Since this is true for any `z`, we thus have: `(α + β) • ⟪x, y⟫ = 0`, and hence the result.
  However the semisimplicity of `ad R L z` is (a) non-trivial and (b) requires the assumption
  that `K` is characteristic 0 (possibly perfect field would suffice) and `L` is semisimple. -/
  let σ : (H → K) → (H → K) := fun γ ↦ α + (β + γ)
  have hσ : ∀ γ, σ γ ≠ γ := fun γ ↦ by simpa only [σ, ← add_assoc] using add_left_ne_self.mpr hαβ
  let f : Module.End K L := (ad K L x) ∘ₗ (ad K L y)
  have hf : ∀ γ, MapsTo f (rootSpace H γ) (rootSpace H (σ γ)) := fun γ ↦
    (mapsTo_toEndomorphism_weightSpace_add_of_mem_rootSpace K L H L α (β + γ) hx).comp <|
      mapsTo_toEndomorphism_weightSpace_add_of_mem_rootSpace K L H L β γ hy
  classical
  have hds := DirectSum.isInternal_submodule_of_independent_of_iSup_eq_top
    (LieSubmodule.independent_iff_coe_toSubmodule.mp <| independent_weightSpace K H L)
    (LieSubmodule.iSup_eq_top_iff_coe_toSubmodule.mp <| iSup_weightSpace_eq_top K H L)
  exact LinearMap.trace_eq_zero_of_mapsTo_ne hds σ hσ hf

/-- Elements of the `α` root space which are Killing-orthogonal to the `-α` root space are
Killing-orthogonal to all of `L`. -/
lemma mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg
    {α : H → K} {x : L} (hx : x ∈ rootSpace H α)
    (hx' : ∀ y ∈ rootSpace H (-α), killingForm K L x y = 0) :
    x ∈ LinearMap.ker (killingForm K L) := by
  rw [LinearMap.mem_ker]
  ext y
  have hy : y ∈ ⨆ β, rootSpace H β := by simp [iSup_weightSpace_eq_top K H L]
  induction hy using LieSubmodule.iSup_induction'
  · next β y hy =>
    by_cases hαβ : α + β = 0
    · exact hx' _ (add_eq_zero_iff_neg_eq.mp hαβ ▸ hy)
    · exact killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero K L H hx hy hαβ
  · simp
  · simp_all

namespace IsKilling

variable [IsKilling K L]

/-- The Killing form as a linear equivalence to the dual. -/
@[simps!]
noncomputable def killingEquiv :
    L ≃ₗ[K] Module.Dual K L :=
  LinearMap.linearEquivOfInjective (killingForm K L) (by simp [← LinearMap.ker_eq_bot])
    Subspace.dual_finrank_eq.symm

variable {K L} in
/-- The restriction of the Killing form to a Cartan subalgebra, as a linear equivalence to the
dual. -/
@[simps!]
noncomputable def killingEquivCartan :
    H ≃ₗ[K] Module.Dual K H :=
  LinearMap.linearEquivOfInjective (traceForm K H L) (by simp [← LinearMap.ker_eq_bot])
    Subspace.dual_finrank_eq.symm

lemma killingEquivCartan_apply_foo (f : Module.Dual K H) (z : H) :
    killingForm K L ((killingEquivCartan H).symm f) z = f z := by
  change killingEquivCartan H ((killingEquivCartan H).symm f) z = _
  simp only [LinearEquiv.apply_symm_apply]

/-- This is Proposition 4.18 from [carter2005] except that we use
`exists_forall_lie_eq_smul_of_weightSpace_ne_bot` instead of Lie's theorem (and so avoid assuming
`K` has characteristic zero). -/
lemma killingEquivCartan_symm_apply_mem_corootSpace (α : weight K H L) :
    (killingEquivCartan H).symm (weight.toLinear K H L α) ∈ corootSpace α := by
  set α' := (killingEquivCartan H).symm (weight.toLinear K H L α)
  have hα : rootSpace H (α : H → K) ≠ ⊥ := by aesop -- Missing API for `weight`
  obtain ⟨e, he₀, he⟩ := exists_forall_lie_eq_smul_of_weightSpace_ne_bot K H L α hα
  have he' : e ∈ rootSpace H α :=
    (mem_weightSpace L (α : H → K) e).mpr fun x ↦ ⟨1, by simp [← he x]⟩
  suffices ∃ f ∈ rootSpace H (-α), killingForm K L e f ≠ 0 by
    obtain ⟨f, hf', hf⟩ := this
    have hef' : ⁅e, f⁆ ∈ H := by
      simpa using mapsTo_toEndomorphism_weightSpace_add_of_mem_rootSpace K L H L α (-α) he' hf'
    have hef : ⟨⁅e, f⁆, hef'⟩ = killingForm K L e f • α' := by
      -- TODO Fix this crazy proof (just POC)
      have h_inj : Function.Injective (traceForm K H L) := by simp [← LinearMap.ker_eq_bot]
      rw [← h_inj.eq_iff]
      ext ⟨z, hz⟩
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      change killingForm K L ⁅e, f⁆ z = killingForm K L e f * killingForm K L α' z -- Missing API
      specialize he ⟨z, hz⟩
      simp only [LieSubalgebra.coe_bracket_of_module] at he
      rw [traceForm_comm, ← traceForm_apply_lie_apply, he, mul_comm]
      simp [killingEquivCartan_apply_foo (f := (weight.toLinear K H L α)) (z := ⟨z, hz⟩)]
    rw [mem_corootSpace]
    apply Submodule.subset_span
    refine ⟨(killingForm K L e f)⁻¹ • e, Submodule.smul_mem _ _ he', f, hf', ?_⟩
    simpa [smul_lie, inv_smul_eq_iff₀ hf, Subtype.ext_iff] using hef
  contrapose! he₀
  simpa using mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg K L H he' he₀

/-- Given a splitting Cartan subalgebra `H` of a finite-dimensional Lie algebra with non-singular
Killing form, the corresponding roots span the dual space of `H`. -/
@[simp]
lemma span_weight_eq_top :
    span K (range (weight.toLinear K H L)) = ⊤ := by
  refine eq_top_iff.mpr (le_trans ?_ (LieModule.range_traceForm_le_span_weight K H L))
  rw [← traceForm_flip K H L, ← LinearMap.dualAnnihilator_ker_eq_range_flip,
    ker_traceForm_eq_bot_of_isCartanSubalgebra, Submodule.dualAnnihilator_bot]

@[simp]
lemma iInf_ker_weight_eq_bot :
    ⨅ α : weight K H L, LinearMap.ker (weight.toLinear K H L α) = ⊥ := by
  rw [← Subspace.dualAnnihilator_inj, Subspace.dualAnnihilator_iInf_eq,
    Submodule.dualAnnihilator_bot]
  simp [← LinearMap.range_dualMap_eq_dualAnnihilator_ker, ← Submodule.span_range_eq_iSup]

@[simp]
lemma corootSpace_zero_eq_bot :
    corootSpace (0 : H → K) = ⊥ := by
  refine eq_bot_iff.mpr fun x hx ↦ ?_
  suffices {x | ∃ y ∈ H, ∃ z ∈ H, ⁅y, z⁆ = x} = {0} by simpa [mem_corootSpace, this] using hx
  refine eq_singleton_iff_unique_mem.mpr ⟨⟨0, H.zero_mem, 0, H.zero_mem, zero_lie 0⟩, ?_⟩
  rintro - ⟨y, hy, z, hz, rfl⟩
  suffices ⁅(⟨y, hy⟩ : H), (⟨z, hz⟩ : H)⁆ = 0 by
    simpa only [Subtype.ext_iff, LieSubalgebra.coe_bracket, ZeroMemClass.coe_zero] using this
  simp

section CharZero

variable {K H L}
variable [CharZero K]

/-- The contrapositive of this result is very useful, taking `x` to be the element of `H`
corresponding to a root `α` under the identification between `H` and `H^*` provided by the Killing
form. -/
lemma eq_zero_of_apply_eq_zero_of_mem_corootSpace
    (x : H) (α : H → K) (hαx : α x = 0) (hx : x ∈ corootSpace α) :
    x = 0 := by
  rcases eq_or_ne α 0 with rfl | hα; · simpa using hx
  replace hx : x ∈ ⨅ β : weight K H L, LinearMap.ker (weight.toLinear K H L β) := by
    simp only [Submodule.mem_iInf, Subtype.forall, Finite.mem_toFinset]
    intro β hβ
    obtain ⟨a, b, hb, hab⟩ := exists_forall_mem_corootSpace_smul_add_eq_zero L α β hα hβ
    simpa [hαx, hb.ne'] using hab _ hx
  simpa using hx

/-- See also `LieAlgebra.IsKilling.isCompl_ker_weight_corootSpace`. -/
lemma disjoint_ker_weight_corootSpace (α : weight K H L) :
    Disjoint (LinearMap.ker (weight.toLinear K H L α)) (corootSpace (α : H → K)) := by
  rw [disjoint_iff]
  refine (Submodule.eq_bot_iff _).mpr fun x ⟨hαx, hx⟩ ↦ ?_
  replace hαx : (α : H → K) x = 0 := by simpa using hαx
  exact eq_zero_of_apply_eq_zero_of_mem_corootSpace x α hαx hx

/-- The coroot corresponding to a root.

TODO Should we have an abbrev for `(killingEquivCartan H).symm (weight.toLinear K H L α)`? Or
maybe we should have API for a linear form + vector which pair together to give `1`? -/
noncomputable def coroot (α : weight K H L) : H := by
  exact 2 • (weight.toLinear K H L α <| (killingEquivCartan H).symm (weight.toLinear K H L α))⁻¹ •
    (killingEquivCartan H).symm (weight.toLinear K H L α)

lemma root_apply_coroot (α : weight K H L) (hα : weight.toLinear K H L α ≠ 0) :
    weight.toLinear K H L α (coroot α) = 2 := by
  set t := (weight.toLinear K H L α <| (killingEquivCartan H).symm (weight.toLinear K H L α))
  suffices t ≠ 0 by simpa [coroot] using inv_mul_cancel this
  contrapose! hα
  suffices (killingEquivCartan H).symm (weight.toLinear K H L α) ∈
      LinearMap.ker (weight.toLinear K H L α) ⊓ corootSpace (α : H → K) by
    rw [(disjoint_ker_weight_corootSpace α).eq_bot] at this
    simpa using this
  exact Submodule.mem_inf.mp ⟨hα, killingEquivCartan_symm_apply_mem_corootSpace K L H α⟩

lemma corootSpace_eq_span_singleton (α : weight K H L) :
    corootSpace (α : H → K) = K ∙ (killingEquivCartan H).symm (weight.toLinear K H L α) := by
  -- TODO: fix this truly awful proof.
  rcases eq_or_ne (α : H → K) 0 with hα | hα
  · have hα' : weight.toLinear K H L α = 0 := by ext z; simp [hα]
    rw [hα, hα']
    simp
  replace hα : (killingEquivCartan H).symm (weight.toLinear K H L α) ≠ 0 := by
    contrapose! hα
    simp only [AddEquivClass.map_eq_zero_iff] at hα
    ext z
    simpa using LinearMap.congr_fun hα z
  have : (K ∙ (killingEquivCartan H).symm (weight.toLinear K H L α) : Submodule K H) ≤
      corootSpace (α : H → K) := by
    simpa using killingEquivCartan_symm_apply_mem_corootSpace K L H α
  refine (eq_of_le_of_finrank_le this ?_).symm
  rw [finrank_span_singleton hα, LieIdeal.coe_to_lieSubalgebra_to_submodule]
  have aux := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (weight.toLinear K H L α))
    (corootSpace (α : H → K))
  rw [(disjoint_ker_weight_corootSpace α).eq_bot] at aux
  simp only [finrank_bot, add_zero] at aux
  have aux₂ : finrank K
      ↑(LinearMap.ker (weight.toLinear K H L α) ⊔ (corootSpace (α : H → K))) ≤
      finrank K H := by exact Submodule.finrank_le _
  have aux₃ : finrank K H = finrank K ↑(LinearMap.ker (weight.toLinear K H L α)) + 1 := by
    simp only [ne_eq, AddEquivClass.map_eq_zero_iff] at hα
    rw [Module.Dual.finrank_ker_add_one_of_ne_zero hα]
  rw [aux, aux₃] at aux₂
  simpa using aux₂

/-- Given a root `α` with respect to a Cartan subalgebra `H`, we have a natural decomposition of
`H` which we write informally as: `H = ker α ⊕ ⁅H(α), H(-α)⁆`, where `H(±α)` are the root spaces
of `±α`.

This is a non-trivial and important result since it allows us to define the _coroot_ of `α` as the
unique element of `⁅H(α), H(-α)⁆` on which `α` takes value `2`.

In fact these complementary spaces are orthogonal (wrt the Killing form). TODO (easy) prove this. -/
lemma isCompl_ker_weight_corootSpace (α : weight K H L) (hα : (α : H → K) ≠ 0) :
    IsCompl (LinearMap.ker (weight.toLinear K H L α)) (corootSpace (α : H → K)) := by
  suffices corootSpace (α : H → K) ≠ ⊥ by
    have hα' : weight.toLinear K H L α ≠ 0 := by
      -- OMG we're proving this again 🙄 API sorely missing
      contrapose! hα
      ext z
      simpa using LinearMap.congr_fun hα z
    apply Module.Dual.isCompl_ker_of_disjoint_of_ne_bot hα' (disjoint_ker_weight_corootSpace α)
    simp only [LieIdeal.coe_to_lieSubalgebra_to_submodule, LieModuleHom.coeSubmodule_range]
    rw [ne_eq, ← LieSubmodule.coe_toSubmodule_eq_iff] at this
    exact this
  contrapose! hα
  rw [← LieSubmodule.coeSubmodule_eq_bot_iff] at hα
  change (corootSpace (α : H → K) : Submodule K H) = _ at hα --Fix bad coercion?
  rw [corootSpace_eq_span_singleton α, killingEquivCartan_symm_apply,
    Submodule.span_singleton_eq_bot, AddEquivClass.map_eq_zero_iff,
    AddEquivClass.map_eq_zero_iff] at hα
  -- Missing API for `weight.toLinear`
  ext x
  simpa using LinearMap.congr_fun hα x

end CharZero

end IsKilling

end LieAlgebra

end Field
