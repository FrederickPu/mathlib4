/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kexing Ying
-/
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Bilinear form

This file defines orthogonal bilinear forms.

## Notations

Given any term `B` of type `BilinForm`, due to a coercion, can use
the notation `B x y` to refer to the function field, ie. `B x y = B.bilin x y`.

In this file we use the following type variables:
 - `M`, `M'`, ... are modules over the commutative semiring `R`,
 - `M₁`, `M₁'`, ... are modules over the commutative ring `R₁`,
 - `V`, ... is a vector space over the field `K`.

## References

* <https://en.wikipedia.org/wiki/Bilinear_form>

## Tags

Bilinear form,
-/


open BigOperators

open LinearMap (BilinForm)

universe u v w

variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {R₁ : Type*} {M₁ : Type*} [CommRing R₁] [AddCommGroup M₁] [Module R₁ M₁]
variable {V : Type*} {K : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {B : BilinForm R M} {B₁ : BilinForm R₁ M₁}

namespace LinearMap

namespace BilinForm

/-- The proposition that two elements of a bilinear form space are orthogonal. For orthogonality
of an indexed set of elements, use `BilinForm.iIsOrtho`. -/
def IsOrtho (B : BilinForm R M) (x y : M) : Prop :=
  B x y = 0
#align bilin_form.is_ortho LinearMap.BilinForm.IsOrtho

theorem isOrtho_def {B : BilinForm R M} {x y : M} : B.IsOrtho x y ↔ B x y = 0 :=
  Iff.rfl
#align bilin_form.is_ortho_def LinearMap.BilinForm.isOrtho_def

theorem isOrtho_zero_left (x : M) : IsOrtho B (0 : M) x := LinearMap.isOrtho_zero_left B x
#align bilin_form.is_ortho_zero_left LinearMap.BilinForm.isOrtho_zero_left

theorem isOrtho_zero_right (x : M) : IsOrtho B x (0 : M) :=
  zero_right x
#align bilin_form.is_ortho_zero_right LinearMap.BilinForm.isOrtho_zero_right

theorem ne_zero_of_not_isOrtho_self {B : BilinForm K V} (x : V) (hx₁ : ¬B.IsOrtho x x) : x ≠ 0 :=
  fun hx₂ => hx₁ (hx₂.symm ▸ isOrtho_zero_left _)
#align bilin_form.ne_zero_of_not_is_ortho_self LinearMap.BilinForm.ne_zero_of_not_isOrtho_self

theorem IsRefl.ortho_comm (H : B.IsRefl) {x y : M} : IsOrtho B x y ↔ IsOrtho B y x :=
  ⟨eq_zero H, eq_zero H⟩
#align bilin_form.is_refl.ortho_comm LinearMap.BilinForm.IsRefl.ortho_comm

theorem IsAlt.ortho_comm (H : B₁.IsAlt) {x y : M₁} : IsOrtho B₁ x y ↔ IsOrtho B₁ y x :=
  H.isRefl.ortho_comm
#align bilin_form.is_alt.ortho_comm LinearMap.BilinForm.IsAlt.ortho_comm

theorem IsSymm.ortho_comm (H : B.IsSymm) {x y : M} : IsOrtho B x y ↔ IsOrtho B y x :=
  H.isRefl.ortho_comm
#align bilin_form.is_symm.ortho_comm LinearMap.BilinForm.IsSymm.ortho_comm

/-- A set of vectors `v` is orthogonal with respect to some bilinear form `B` if and only
if for all `i ≠ j`, `B (v i) (v j) = 0`. For orthogonality between two elements, use
`BilinForm.IsOrtho` -/
def iIsOrtho {n : Type w} (B : BilinForm R M) (v : n → M) : Prop :=
  Pairwise (B.IsOrtho on v)
set_option linter.uppercaseLean3 false in
#align bilin_form.is_Ortho LinearMap.BilinForm.iIsOrtho

theorem iIsOrtho_def {n : Type w} {B : BilinForm R M} {v : n → M} :
    B.iIsOrtho v ↔ ∀ i j : n, i ≠ j → B (v i) (v j) = 0 :=
  Iff.rfl
set_option linter.uppercaseLean3 false in
#align bilin_form.is_Ortho_def LinearMap.BilinForm.iIsOrtho_def

section

variable {R₄ M₄ : Type*} [CommRing R₄] [IsDomain R₄]
variable [AddCommGroup M₄] [Module R₄ M₄] {G : BilinForm R₄ M₄}

@[simp]
theorem isOrtho_smul_left {x y : M₄} {a : R₄} (ha : a ≠ 0) :
    IsOrtho G (a • x) y ↔ IsOrtho G x y := by
  dsimp only [IsOrtho]
  rw [map_smul]
  simp only [LinearMap.smul_apply, smul_eq_mul, mul_eq_zero, or_iff_right_iff_imp]
  exact fun a ↦ (ha a).elim
#align bilin_form.is_ortho_smul_left LinearMap.BilinForm.isOrtho_smul_left

@[simp]
theorem isOrtho_smul_right {x y : M₄} {a : R₄} (ha : a ≠ 0) :
    IsOrtho G x (a • y) ↔ IsOrtho G x y := by
  dsimp only [IsOrtho]
  rw [map_smul]
  simp only [smul_eq_mul, mul_eq_zero, or_iff_right_iff_imp]
  exact fun a ↦ (ha a).elim
#align bilin_form.is_ortho_smul_right LinearMap.BilinForm.isOrtho_smul_right

/-- A set of orthogonal vectors `v` with respect to some bilinear form `B` is linearly independent
  if for all `i`, `B (v i) (v i) ≠ 0`. -/
theorem linearIndependent_of_iIsOrtho {n : Type w} {B : BilinForm K V} {v : n → V}
    (hv₁ : B.iIsOrtho v) (hv₂ : ∀ i, ¬B.IsOrtho (v i) (v i)) : LinearIndependent K v := by
  classical
    rw [linearIndependent_iff']
    intro s w hs i hi
    have : B (s.sum fun i : n => w i • v i) (v i) = 0 := by rw [hs, zero_left]
    have hsum : (s.sum fun j : n => w j * B (v j) (v i)) = w i * B (v i) (v i) := by
      apply Finset.sum_eq_single_of_mem i hi
      intro j _ hij
      rw [iIsOrtho_def.1 hv₁ _ _ hij, mul_zero]
    simp_rw [sum_left, smul_left, hsum] at this
    exact eq_zero_of_ne_zero_of_mul_right_eq_zero (hv₂ i) this
set_option linter.uppercaseLean3 false in
#align bilin_form.linear_independent_of_is_Ortho LinearMap.BilinForm.linearIndependent_of_iIsOrtho

end

section Orthogonal

/-- The orthogonal complement of a submodule `N` with respect to some bilinear form is the set of
elements `x` which are orthogonal to all elements of `N`; i.e., for all `y` in `N`, `B x y = 0`.

Note that for general (neither symmetric nor antisymmetric) bilinear forms this definition has a
chirality; in addition to this "left" orthogonal complement one could define a "right" orthogonal
complement for which, for all `y` in `N`, `B y x = 0`.  This variant definition is not currently
provided in mathlib. -/
def orthogonal (B : BilinForm R M) (N : Submodule R M) : Submodule R M where
  carrier := { m | ∀ n ∈ N, IsOrtho B n m }
  zero_mem' x _ := isOrtho_zero_right x
  add_mem' {x y} hx hy n hn := by
    rw [IsOrtho, add_right, show B n x = 0 from hx n hn, show B n y = 0 from hy n hn, zero_add]
  smul_mem' c x hx n hn := by
    rw [IsOrtho, smul_right, show B n x = 0 from hx n hn, mul_zero]
#align bilin_form.orthogonal LinearMap.BilinForm.orthogonal

variable {N L : Submodule R M}

@[simp]
theorem mem_orthogonal_iff {N : Submodule R M} {m : M} :
    m ∈ B.orthogonal N ↔ ∀ n ∈ N, IsOrtho B n m :=
  Iff.rfl
#align bilin_form.mem_orthogonal_iff LinearMap.BilinForm.mem_orthogonal_iff

theorem orthogonal_le (h : N ≤ L) : B.orthogonal L ≤ B.orthogonal N := fun _ hn l hl => hn l (h hl)
#align bilin_form.orthogonal_le LinearMap.BilinForm.orthogonal_le

theorem le_orthogonal_orthogonal (b : B.IsRefl) : N ≤ B.orthogonal (B.orthogonal N) :=
  fun n hn _ hm => b _ _ (hm n hn)
#align bilin_form.le_orthogonal_orthogonal LinearMap.BilinForm.le_orthogonal_orthogonal

-- ↓ This lemma only applies in fields as we require `a * b = 0 → a = 0 ∨ b = 0`
theorem span_singleton_inf_orthogonal_eq_bot {B : BilinForm K V} {x : V} (hx : ¬B.IsOrtho x x) :
    (K ∙ x) ⊓ B.orthogonal (K ∙ x) = ⊥ := by
  rw [← Finset.coe_singleton]
  refine' eq_bot_iff.2 fun y h => _
  rcases mem_span_finset.1 h.1 with ⟨μ, rfl⟩
  have := h.2 x ?_
  · rw [Finset.sum_singleton] at this ⊢
    suffices hμzero : μ x = 0 by rw [hμzero, zero_smul, Submodule.mem_bot]
    change B x (μ x • x) = 0 at this
    rw [smul_right] at this
    exact eq_zero_of_ne_zero_of_mul_right_eq_zero hx this
  · rw [Submodule.mem_span]
    exact fun _ hp => hp <| Finset.mem_singleton_self _
#align bilin_form.span_singleton_inf_orthogonal_eq_bot LinearMap.BilinForm.span_singleton_inf_orthogonal_eq_bot

-- ↓ This lemma only applies in fields since we use the `mul_eq_zero`
theorem orthogonal_span_singleton_eq_toLin_ker {B : BilinForm K V} (x : V) :
    B.orthogonal (K ∙ x) = LinearMap.ker (LinearMap.BilinForm.toLinHomAux₁ B x) := by
  ext y
  simp_rw [mem_orthogonal_iff, LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · exact fun h => h x ⟨1, one_smul _ _⟩
  · rintro h _ ⟨z, rfl⟩
    rw [IsOrtho, smul_left, mul_eq_zero]
    exact Or.intro_right _ h
#align bilin_form.orthogonal_span_singleton_eq_to_lin_ker LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker

theorem span_singleton_sup_orthogonal_eq_top {B : BilinForm K V} {x : V} (hx : ¬B.IsOrtho x x) :
    (K ∙ x) ⊔ B.orthogonal (K ∙ x) = ⊤ := by
  rw [orthogonal_span_singleton_eq_toLin_ker]
  exact LinearMap.span_singleton_sup_ker_eq_top _ hx
#align bilin_form.span_singleton_sup_orthogonal_eq_top LinearMap.BilinForm.span_singleton_sup_orthogonal_eq_top

/-- Given a bilinear form `B` and some `x` such that `B x x ≠ 0`, the span of the singleton of `x`
  is complement to its orthogonal complement. -/
theorem isCompl_span_singleton_orthogonal {B : BilinForm K V} {x : V} (hx : ¬B.IsOrtho x x) :
    IsCompl (K ∙ x) (B.orthogonal <| K ∙ x) :=
  { disjoint := disjoint_iff.2 <| span_singleton_inf_orthogonal_eq_bot hx
    codisjoint := codisjoint_iff.2 <| span_singleton_sup_orthogonal_eq_top hx }
#align bilin_form.is_compl_span_singleton_orthogonal LinearMap.BilinForm.isCompl_span_singleton_orthogonal

end Orthogonal

variable {M₂' : Type*}
variable [AddCommMonoid M₂'] [Module R M₂']

/-- The restriction of a reflexive bilinear form `B` onto a submodule `W` is
nondegenerate if `Disjoint W (B.orthogonal W)`. -/
theorem nondegenerateRestrictOfDisjointOrthogonal (B : BilinForm R₁ M₁) (b : B.IsRefl)
    {W : Submodule R₁ M₁} (hW : Disjoint W (B.orthogonal W)) : (B.restrict W).Nondegenerate := by
  rintro ⟨x, hx⟩ b₁
  rw [Submodule.mk_eq_zero, ← Submodule.mem_bot R₁]
  refine' hW.le_bot ⟨hx, fun y hy => _⟩
  specialize b₁ ⟨y, hy⟩
  simp only [restrict_apply, domRestrict_apply] at b₁
  exact isOrtho_def.mpr (b x y b₁)
#align bilin_form.nondegenerate_restrict_of_disjoint_orthogonal LinearMap.BilinForm.nondegenerateRestrictOfDisjointOrthogonal

/-- An orthogonal basis with respect to a nondegenerate bilinear form has no self-orthogonal
elements. -/
theorem iIsOrtho.not_isOrtho_basis_self_of_nondegenerate {n : Type w} [Nontrivial R]
    {B : BilinForm R M} {v : Basis n R M} (h : B.iIsOrtho v) (hB : B.Nondegenerate) (i : n) :
    ¬B.IsOrtho (v i) (v i) := by
  intro ho
  refine' v.ne_zero i (hB (v i) fun m => _)
  obtain ⟨vi, rfl⟩ := v.repr.symm.surjective m
  rw [Basis.repr_symm_apply, Finsupp.total_apply, Finsupp.sum, sum_right]
  apply Finset.sum_eq_zero
  rintro j -
  rw [smul_right]
  convert mul_zero (vi j) using 2
  obtain rfl | hij := eq_or_ne i j
  · exact ho
  · exact h hij
set_option linter.uppercaseLean3 false in
#align bilin_form.is_Ortho.not_is_ortho_basis_self_of_nondegenerate LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate

/-- Given an orthogonal basis with respect to a bilinear form, the bilinear form is nondegenerate
iff the basis has no elements which are self-orthogonal. -/
theorem iIsOrtho.nondegenerate_iff_not_isOrtho_basis_self {n : Type w} [Nontrivial R]
    [NoZeroDivisors R] (B : BilinForm R M) (v : Basis n R M) (hO : B.iIsOrtho v) :
    B.Nondegenerate ↔ ∀ i, ¬B.IsOrtho (v i) (v i) := by
  refine' ⟨hO.not_isOrtho_basis_self_of_nondegenerate, fun ho m hB => _⟩
  obtain ⟨vi, rfl⟩ := v.repr.symm.surjective m
  rw [LinearEquiv.map_eq_zero_iff]
  ext i
  rw [Finsupp.zero_apply]
  specialize hB (v i)
  simp_rw [Basis.repr_symm_apply, Finsupp.total_apply, Finsupp.sum, sum_left, smul_left] at hB
  rw [Finset.sum_eq_single i] at hB
  · exact eq_zero_of_ne_zero_of_mul_right_eq_zero (ho i) hB
  · intro j _ hij
    convert mul_zero (vi j) using 2
    exact hO hij
  · intro hi
    convert zero_mul (M₀ := R) _ using 2
    exact Finsupp.not_mem_support_iff.mp hi
set_option linter.uppercaseLean3 false in
#align bilin_form.is_Ortho.nondegenerate_iff_not_is_ortho_basis_self LinearMap.BilinForm.iIsOrtho.nondegenerate_iff_not_isOrtho_basis_self

section

theorem toLin_restrict_ker_eq_inf_orthogonal (B : BilinForm K V) (W : Subspace K V) (b : B.IsRefl) :
    (B.domRestrict W).ker.map W.subtype = (W ⊓ B.orthogonal ⊤ : Subspace K V) := by
  ext x; constructor <;> intro hx
  · rcases hx with ⟨⟨x, hx⟩, hker, rfl⟩
    erw [LinearMap.mem_ker] at hker
    constructor
    · simp [hx]
    · intro y _
      rw [IsOrtho, b]
      change (B.domRestrict W) ⟨x, hx⟩ y = 0
      rw [hker]
      rfl
  · simp_rw [Submodule.mem_map, LinearMap.mem_ker]
    refine' ⟨⟨x, hx.1⟩, _, rfl⟩
    ext y
    change B x y = 0
    rw [b]
    exact hx.2 _ Submodule.mem_top
#align bilin_form.to_lin_restrict_ker_eq_inf_orthogonal LinearMap.BilinForm.toLin_restrict_ker_eq_inf_orthogonal

theorem toLin_restrict_range_dualCoannihilator_eq_orthogonal (B : BilinForm K V)
    (W : Subspace K V) : (B.domRestrict W).range.dualCoannihilator = B.orthogonal W := by
  ext x; constructor <;> rw [mem_orthogonal_iff] <;> intro hx
  · intro y hy
    rw [Submodule.mem_dualCoannihilator] at hx
    exact hx (B.domRestrict W ⟨y, hy⟩) ⟨⟨y, hy⟩, rfl⟩
  · rw [Submodule.mem_dualCoannihilator]
    rintro _ ⟨⟨w, hw⟩, rfl⟩
    exact hx w hw
#align bilin_form.to_lin_restrict_range_dual_coannihilator_eq_orthogonal LinearMap.BilinForm.toLin_restrict_range_dualCoannihilator_eq_orthogonal

variable [FiniteDimensional K V]

open FiniteDimensional Submodule

theorem finrank_add_finrank_orthogonal {B : BilinForm K V} {W : Subspace K V} (b₁ : B.IsRefl) :
    finrank K W + finrank K (B.orthogonal W) =
      finrank K V + finrank K (W ⊓ B.orthogonal ⊤ : Subspace K V) := by
  rw [← toLin_restrict_ker_eq_inf_orthogonal _ _ b₁, ←
    toLin_restrict_range_dualCoannihilator_eq_orthogonal _ _, finrank_map_subtype_eq]
  conv_rhs =>
    rw [← @Subspace.finrank_add_finrank_dualCoannihilator_eq K V _ _ _ _
        (LinearMap.range (B.domRestrict W)),
      add_comm, ← add_assoc, add_comm (finrank K (LinearMap.ker (B.domRestrict W))),
      LinearMap.finrank_range_add_finrank_ker]
#align bilin_form.finrank_add_finrank_orthogonal LinearMap.BilinForm.finrank_add_finrank_orthogonal

/-- A subspace is complement to its orthogonal complement with respect to some
reflexive bilinear form if that bilinear form restricted on to the subspace is nondegenerate. -/
theorem restrict_nondegenerate_of_isCompl_orthogonal {B : BilinForm K V} {W : Subspace K V}
    (b₁ : B.IsRefl) (b₂ : (B.restrict W).Nondegenerate) : IsCompl W (B.orthogonal W) := by
  have : W ⊓ B.orthogonal W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := mem_inf.1 hx
    refine' Subtype.mk_eq_mk.1 (b₂ ⟨x, hx₁⟩ _)
    rintro ⟨n, hn⟩
    simp only [restrict_apply, domRestrict_apply]
    exact b₁ n x (b₁ x n (b₁ n x (hx₂ n hn)))
  refine' IsCompl.of_eq this (eq_top_of_finrank_eq <| (finrank_le _).antisymm _)
  conv_rhs => rw [← add_zero (finrank K _)]
  rw [← finrank_bot K V, ← this, finrank_sup_add_finrank_inf_eq,
    finrank_add_finrank_orthogonal b₁]
  exact le_self_add
#align bilin_form.restrict_nondegenerate_of_is_compl_orthogonal LinearMap.BilinForm.restrict_nondegenerate_of_isCompl_orthogonal

/-- A subspace is complement to its orthogonal complement with respect to some reflexive bilinear
form if and only if that bilinear form restricted on to the subspace is nondegenerate. -/
theorem restrict_nondegenerate_iff_isCompl_orthogonal {B : BilinForm K V} {W : Subspace K V}
    (b₁ : B.IsRefl) : (B.restrict W).Nondegenerate ↔ IsCompl W (B.orthogonal W) :=
  ⟨fun b₂ => restrict_nondegenerate_of_isCompl_orthogonal b₁ b₂, fun h =>
    B.nondegenerateRestrictOfDisjointOrthogonal b₁ h.1⟩
#align bilin_form.restrict_nondegenerate_iff_is_compl_orthogonal LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal

end

/-! We note that we cannot use `BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal` for the
lemma below since the below lemma does not require `V` to be finite dimensional. However,
`BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal` does not require `B` to be nondegenerate
on the whole space. -/


/-- The restriction of a reflexive, non-degenerate bilinear form on the orthogonal complement of
the span of a singleton is also non-degenerate. -/
theorem restrictOrthogonalSpanSingletonNondegenerate (B : BilinForm K V) (b₁ : B.Nondegenerate)
    (b₂ : B.IsRefl) {x : V} (hx : ¬B.IsOrtho x x) :
    Nondegenerate <| B.restrict <| B.orthogonal (K ∙ x) := by
  refine' fun m hm => Submodule.coe_eq_zero.1 (b₁ m.1 fun n => _)
  have : n ∈ (K ∙ x) ⊔ B.orthogonal (K ∙ x) :=
    (span_singleton_sup_orthogonal_eq_top hx).symm ▸ Submodule.mem_top
  rcases Submodule.mem_sup.1 this with ⟨y, hy, z, hz, rfl⟩
  specialize hm ⟨z, hz⟩
  rw [restrict] at hm
  erw [add_right, show B m.1 y = 0 by rw [b₂]; exact m.2 y hy, hm, add_zero]
#align bilin_form.restrict_orthogonal_span_singleton_nondegenerate LinearMap.BilinForm.restrictOrthogonalSpanSingletonNondegenerate

end BilinForm
