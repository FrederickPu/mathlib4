/-
Copyright (c) 2024 Newell Jensen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Newell Jensen, Mitchell Lee
-/
import Mathlib.Data.Matrix.Notation
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Coxeter Systems

This file defines Coxeter systems and Coxeter groups.

A Coxeter system is a pair `(W, S)` where `W` is a group generated by a set of
reflections (involutions) `S = {s₁,s₂,...,sₙ}`, subject to relations determined
by a Coxeter matrix `M = (mᵢⱼ)`.  The Coxeter matrix is a symmetric matrix with
entries `mᵢⱼ` representing the order of the product `sᵢsⱼ` for `i ≠ j` and `mᵢᵢ = 1`.

When `(W, S)` is a Coxeter system, one also says, by abuse of language, that `W` is a
Coxeter group.  A Coxeter group `W` is determined by the presentation
`W = ⟨s₁,s₂,...,sₙ | ∀ i j, (sᵢsⱼ)^mᵢⱼ = 1⟩`, where `1` is the identity element of `W`.

The finite Coxeter groups are classified (TODO) as the four infinite families:

* `Aₙ, Bₙ, Dₙ, I₂ₘ`

And the exceptional systems:

* `E₆, E₇, E₈, F₄, G₂, H₃, H₄`

## Implementation details

In this file a Coxeter system, designated as `CoxeterSystem M W`, is implemented as a
structure which effectively records the isomorphism between a group `W` and the corresponding
group presentation derived from a Coxeter matrix `M`.  From another perspective, it serves as
a set of generators for `W`, tailored to the underlying type of `M`, while ensuring compliance
with the relations specified by the Coxeter matrix `M`.

A type class `IsCoxeterGroup` is introduced, for groups that are isomorphic to a group
presentation corresponding to a Coxeter matrix which is registered in a Coxeter system.

In most texts on Coxeter groups, each entry $M_{i,i'}$ of the Coxeter matrix can be either a
positive integer or $\infty$. A value of $\infty$ indicates that there is no relation between the
corresponding simple reflections. In our treatment of Coxeter groups, we use the value $0$ instead
of $\infty$. The Coxeter relation $(s_i s_{i'})^{M_{i, i'}}$ is automatically the identity if
$M_{i, i'} = 0$.

## Main definitions

* `Matrix.IsCoxeter` : A matrix `IsCoxeter` if it is a symmetric matrix with diagonal
  entries equal to one and off-diagonal entries distinct from one.
* `Matrix.CoxeterGroup` : The group presentation corresponding to a Coxeter matrix.
* `CoxeterSystem` : A structure recording the isomorphism between a group `W` and the
  group presentation corresponding to a Coxeter matrix, i.e. `Matrix.CoxeterGroup M`.
* `equivCoxeterGroup` : Coxeter groups of isomorphic types are isomorphic.
* `IsCoxeterGroup` : A group is a Coxeter group if it is registered in a Coxeter system.
* `CoxeterMatrix.Aₙ` : Coxeter matrix for the symmetry group of the regular n-simplex.
* `CoxeterMatrix.Bₙ` : Coxeter matrix for the symmetry group of the regular n-hypercube
  and its dual, the regular n-orthoplex (or n-cross-polytope).
* `CoxeterMatrix.Dₙ` : Coxeter matrix for the symmetry group of the n-demicube.
* `CoxeterMatrix.I₂ₘ` : Coxeter matrix for the symmetry group of the regular (m + 2)-gon.
* `CoxeterMatrix.E₆` : Coxeter matrix for the symmetry group of the E₆ root polytope.
* `CoxeterMatrix.E₇` : Coxeter matrix for the symmetry group of the E₇ root polytope.
* `CoxeterMatrix.E₈` : Coxeter matrix for the symmetry group of the E₈ root polytope.
* `CoxeterMatrix.F₄` : Coxeter matrix for the symmetry group of the regular 4-polytope,
  the 24-cell.
* `CoxeterMatrix.G₂` : Coxeter matrix for the symmetry group of the regular hexagon.
* `CoxeterMatrix.H₃` : Coxeter matrix for the symmetry group of the regular dodecahedron
  and icosahedron.
* `CoxeterMatrix.H₄` : Coxeter matrix for the symmetry group of the regular 4-polytopes,
  the 120-cell and 600-cell.
* `CoxeterSystem.simpleReflection `: The simple reflection corresponding to an index `i : B`.
* `CoxeterSystem.lift`: Given `f : B → G`, where `G` is a monoid and `f` is a function whose values
satisfy the Coxeter relations, extend it to a monoid homomorphism `f' : W → G` satisfying
`f' (s i) = f i` for all `i`.
* `CoxeterSystem.wordProd`: Given a `List B`, returns the product of the corresponding simple
reflections.

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*](bourbaki1968) chapter IV
  pages 4--5, 13--15

* [J. Baez, *Coxeter and Dynkin Diagrams*](https://math.ucr.edu/home/baez/twf_dynkin.pdf)

## TODO

* The canonical map from the type to the Coxeter group `W` is an injection.
* A group `W` registered in a Coxeter system is a Coxeter group.
* A Coxeter group is an instance of `IsCoxeterGroup`.
* Introduce some ways to actually construct some Coxeter groups. For example, given a Coxeter matrix
$M : B \times B \to \mathbb{N}$, a real vector space $V$, a basis $\{\alpha_i : i \in B\}$
and a bilinear form $\langle \cdot, \cdot \rangle \colon V \times V \to \mathbb{R}$ satisfying
$$\langle \alpha_i, \alpha_{i'}\rangle = - \cos(\pi / M_{i,i'}),$$ one can form the subgroup of
$GL(V)$ generated by the reflections in the $\alpha_i$, and it is a Coxeter group. We can use this
to combinatorially describe the Coxeter groups of type $A$, $B$, $D$, and $I$.
* State and prove Matsumoto's theorem.
* Classify the finite Coxeter groups.

## Tags

coxeter system, coxeter group
-/


universe u

noncomputable section

variable {B : Type*} [DecidableEq B]

variable (M : Matrix B B ℕ)

/-- A matrix `IsCoxeter` if it is a symmetric matrix with diagonal entries equal to one
and off-diagonal entries distinct from one. -/
structure Matrix.IsCoxeter : Prop where
  symmetric : M.IsSymm := by aesop
  diagonal : ∀ i : B, M i i  = 1 := by aesop
  off_diagonal : ∀ i i' : B, i ≠ i' → M i i' ≠ 1 := by aesop

theorem Matrix.reindex_isCoxeter {B B' : Type*} [DecidableEq B] [DecidableEq B'] (M : Matrix B B ℕ)
    (e : B ≃ B') (hM : M.IsCoxeter) : (Matrix.reindex e e M).IsCoxeter where
  symmetric := by dsimp only [Matrix.IsSymm]; rw [Matrix.transpose_reindex, hM.symmetric]
  diagonal := by intro b; dsimp [Matrix.reindex]; exact hM.diagonal (e.symm b)
  off_diagonal := by intro i i' hii'; dsimp [Matrix.reindex]; apply hM.off_diagonal; aesop

namespace CoxeterGroup

namespace Relations

/-- The relations corresponding to a Coxeter matrix. -/
def ofMatrix : B × B → FreeGroup B :=
 Function.uncurry fun b₁ b₂ => (FreeGroup.of b₁ * FreeGroup.of b₂) ^ M b₁ b₂

/-- The set of relations corresponding to a Coxeter matrix. -/
def toSet : Set (FreeGroup B) :=
  Set.range <| ofMatrix M

end Relations

end CoxeterGroup

/-- The group presentation corresponding to a Coxeter matrix. -/
def Matrix.CoxeterGroup := PresentedGroup (CoxeterGroup.Relations.toSet M)

instance : Group (Matrix.CoxeterGroup M) :=
  QuotientGroup.Quotient.group _

namespace CoxeterGroup

/-- The canonical map from `B` to the Coxeter group with generators `b : B`. The term `b`
is mapped to the equivalence class of the image of `b` in `CoxeterGroup M`. -/
def of (b : B) : Matrix.CoxeterGroup M := PresentedGroup.of b

@[simp]
theorem of_apply (b : B) : of M b = PresentedGroup.of (rels := Relations.toSet M) b :=
  rfl

end CoxeterGroup

/-- A Coxeter system `CoxeterSystem W` is a structure recording the isomorphism between
a group `W` and the group presentation corresponding to a Coxeter matrix. Equivalently, this
can be seen as a list of generators of `W` parameterized by the underlying type of `M`, which
satisfy the relations of the Coxeter matrix `M`. -/
structure CoxeterSystem (W : Type*) [Group W]  where
  /-- `CoxeterSystem.ofMulEquiv` constructs a Coxeter system given a proof that `M` is a Coxeter
  matrix and an equivalence with the group
  presentation corresponding to a Coxeter matrix `M`. -/
  ofMulEquiv ::
    isCoxeter : M.IsCoxeter
    /-- `mulEquiv` is the isomorphism between the group `W` and the group presentation
    corresponding to a Coxeter matrix `M`. -/
    mulEquiv : W ≃* Matrix.CoxeterGroup M

/-- A group is a Coxeter group if it admits a Coxeter system for some Coxeter matrix `M`. -/
class IsCoxeterGroup (W : Type u) [Group W] : Prop where
  nonempty_system : ∃ (B : Type u), ∃ (M : Matrix B B ℕ), Nonempty (CoxeterSystem M W)

namespace CoxeterSystem

open Matrix

variable {B B' W H : Type*} [DecidableEq B] [DecidableEq B'] [Group W] [Group H]

variable {M : Matrix B B ℕ}

/-- A Coxeter system for `W` with Coxeter matrix `M` indexed by `B`, is associated to
a map `B → W` recording the images of the indices. -/
instance funLike : FunLike (CoxeterSystem M W) B W where
  coe cs := fun b => cs.mulEquiv.symm (.of b)
  coe_injective' := by
    rintro ⟨_, cs⟩ ⟨_, cs'⟩ hcs'
    have H : (cs.symm : CoxeterGroup M →* W) = (cs'.symm : CoxeterGroup M →* W) := by
      unfold CoxeterGroup
      ext i; exact congr_fun hcs' i
    have : cs.symm = cs'.symm := by ext x; exact DFunLike.congr_fun H x
    rw [ofMulEquiv.injEq, ← MulEquiv.symm_symm cs, ← MulEquiv.symm_symm cs', this]

@[simp]
theorem mulEquiv_apply_coe (cs : CoxeterSystem M W) (b : B) : cs.mulEquiv (cs b) = .of b :=
  cs.mulEquiv.eq_symm_apply.mp rfl

/-- The map sending a Coxeter system to its associated map `B → W` is injective. -/
theorem ext' {cs₁ cs₂ : CoxeterSystem M W} (H : ⇑cs₁ = ⇑cs₂) : cs₁ = cs₂ := DFunLike.coe_injective H

/-- Extensionality rule for Coxeter systems. -/
theorem ext {cs₁ cs₂ : CoxeterSystem M W} (H : ∀ b, cs₁ b = cs₂ b) : cs₁ = cs₂ :=
  ext' <| by ext; apply H

/-- The canonical Coxeter system of the Coxeter group over `X`. -/
def ofCoxeterGroup (X : Type*) (D : Matrix X X ℕ) (hD : IsCoxeter D) :
    CoxeterSystem D (CoxeterGroup D) where
  isCoxeter := hD
  mulEquiv := .refl _

@[simp]
theorem ofCoxeterGroup_apply {X : Type*} (D : Matrix X X ℕ) (hD : IsCoxeter D) (x : X) :
    CoxeterSystem.ofCoxeterGroup X D hD x = CoxeterGroup.of D x :=
  rfl

theorem map_relations_eq_reindex_relations (e : B ≃ B') :
    (MulEquiv.toMonoidHom (FreeGroup.freeGroupCongr e)) '' CoxeterGroup.Relations.toSet M =
    CoxeterGroup.Relations.toSet (reindex e e M) := by
  simp [CoxeterGroup.Relations.toSet, CoxeterGroup.Relations.ofMatrix]
  apply le_antisymm
  · rw [Set.le_iff_subset]; intro _
    simp only [Set.mem_image, Set.mem_range, Prod.exists, Function.uncurry_apply_pair,
      forall_exists_index, and_imp]
    intro _ hb b _ heq; rw [← heq]
    use (e hb); use (e b); aesop
  · rw [Set.le_iff_subset]; intro hb'
    simp only [Set.mem_range, Prod.exists, Function.uncurry_apply_pair, Set.mem_image,
      forall_exists_index]
    intro b1' b2' heq; rw [← heq]
    use ((FreeGroup.freeGroupCongr e).symm hb')
    exact ⟨by use (e.symm b1'); use (e.symm b2'); aesop, by aesop⟩

/-- Coxeter groups of isomorphic types are isomorphic. -/
def equivCoxeterGroup (e : B ≃ B') : CoxeterGroup M ≃* CoxeterGroup (reindex e e M) :=
  QuotientGroup.congr (Subgroup.normalClosure (CoxeterGroup.Relations.toSet M))
    (Subgroup.normalClosure (CoxeterGroup.Relations.toSet (reindex e e M)))
    (FreeGroup.freeGroupCongr e) (by
      have := Subgroup.map_normalClosure (CoxeterGroup.Relations.toSet M)
        (FreeGroup.freeGroupCongr e).toMonoidHom (FreeGroup.freeGroupCongr e).surjective
      rwa [map_relations_eq_reindex_relations] at this)

theorem equivCoxeterGroup_apply_of (b : B) (M : Matrix B B ℕ) (e : B ≃ B') :
    (equivCoxeterGroup e) (CoxeterGroup.of M b) = CoxeterGroup.of (reindex e e M) (e b) :=
  rfl

theorem equivCoxeterGroup_symm_apply_of (b' : B') (M : Matrix B B ℕ) (e : B ≃ B') :
    (equivCoxeterGroup e).symm (CoxeterGroup.of (reindex e e M) b') =
    CoxeterGroup.of M (e.symm b') :=
  rfl

/-- Reindex a Coxeter system through a bijection of the indexing sets. -/
@[simps]
protected def reindex (cs : CoxeterSystem M W) (e : B ≃ B') :
    CoxeterSystem (reindex e e M) W :=
  ofMulEquiv (M.reindex_isCoxeter e cs.isCoxeter) (cs.mulEquiv.trans (equivCoxeterGroup e))

@[simp]
theorem reindex_apply (cs : CoxeterSystem M W) (e : B ≃ B') (b' : B') :
    cs.reindex e b' = cs (e.symm b') :=
  rfl

/-- Pushing a Coxeter system through a group isomorphism. -/
@[simps]
protected def map (cs : CoxeterSystem M W) (e : W ≃* H) : CoxeterSystem M H :=
  ofMulEquiv cs.isCoxeter (e.symm.trans cs.mulEquiv)

@[simp]
theorem map_apply (cs : CoxeterSystem M W) (e : W ≃* H) (b : B) : cs.map e b = e (cs b) :=
  rfl

end CoxeterSystem

namespace CoxeterMatrix

open Matrix

variable (n : ℕ)

/-- The Coxeter matrix of family A(n).

The corresponding Coxeter-Dynkin diagram is:
```
    o --- o --- o ⬝ ⬝ ⬝ ⬝ o --- o
```
-/
abbrev Aₙ : Matrix (Fin n) (Fin n) ℕ :=
  Matrix.of fun i j : Fin n =>
    if i = j then 1
      else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2)

theorem isCoxeter_Aₙ : IsCoxeter (Aₙ n) where
  symmetric := by
    simp [Matrix.IsSymm]; aesop

/-- The Coxeter matrix of family Bₙ.

The corresponding Coxeter-Dynkin diagram is:
```
       4
    o --- o --- o ⬝ ⬝ ⬝ ⬝ o --- o
```
-/
abbrev Bₙ : Matrix (Fin n) (Fin n) ℕ :=
  Matrix.of fun i j : Fin n =>
    if i = j then 1
      else (if i = n - 1 ∧ j = n - 2 ∨ j = n - 1 ∧ i = n - 2 then 4
        else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2))

theorem isCoxeter_Bₙ : IsCoxeter (Bₙ n) where
  symmetric := by simp [Matrix.IsSymm]; aesop

/-- The Coxeter matrix of family Dₙ.

The corresponding Coxeter-Dynkin diagram is:
```
    o
     \
      o --- o ⬝ ⬝ ⬝ ⬝ o --- o
     /
    o
```
-/
abbrev Dₙ : Matrix (Fin n) (Fin n) ℕ :=
  Matrix.of fun i j : Fin n =>
    if i = j then 1
      else (if i = n - 1 ∧ j = n - 3 ∨ j = n - 1 ∧ i = n - 3 then 3
        else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2))

theorem isCoxeter_Dₙ : IsCoxeter (Dₙ n) where
  symmetric := by simp [Matrix.IsSymm]; aesop

/-- The Coxeter matrix of m-indexed family I₂(m).

The corresponding Coxeter-Dynkin diagram is:
```
     m + 2
    o --- o
```
-/
abbrev I₂ₘ (m : ℕ) : Matrix (Fin 2) (Fin 2) ℕ :=
  Matrix.of fun i j => if i = j then 1 else m + 2

theorem isCoxeter_I₂ₘ (m : ℕ) : IsCoxeter (I₂ₘ m) where
  symmetric := by simp [Matrix.IsSymm]; aesop

/-- The Coxeter matrix of system E₆.

The corresponding Coxeter-Dynkin diagram is:
```
                o
                |
    o --- o --- o --- o --- o
```
-/
def E₆ : Matrix (Fin 6) (Fin 6) ℕ :=
  !![1, 2, 3, 2, 2, 2;
     2, 1, 2, 3, 2, 2;
     3, 2, 1, 3, 2, 2;
     2, 3, 3, 1, 3, 2;
     2, 2, 2, 3, 1, 3;
     2, 2, 2, 2, 3, 1]

theorem isCoxeter_E₆ : IsCoxeter E₆ where
  symmetric := by simp [Matrix.IsSymm]; decide
  diagonal := by decide
  off_diagonal := by decide

/-- The Coxeter matrix of system E₇.

The corresponding Coxeter-Dynkin diagram is:
```
                o
                |
    o --- o --- o --- o --- o --- o
```
-/
def E₇ : Matrix (Fin 7) (Fin 7) ℕ :=
  !![1, 2, 3, 2, 2, 2, 2;
     2, 1, 2, 3, 2, 2, 2;
     3, 2, 1, 3, 2, 2, 2;
     2, 3, 3, 1, 3, 2, 2;
     2, 2, 2, 3, 1, 3, 2;
     2, 2, 2, 2, 3, 1, 3;
     2, 2, 2, 2, 2, 3, 1]

theorem isCoxeter_E₇ : IsCoxeter E₇ where
  symmetric := by simp [Matrix.IsSymm]; decide
  diagonal := by decide
  off_diagonal := by decide

/-- The Coxeter matrix of system E₈.

The corresponding Coxeter-Dynkin diagram is:
```
                o
                |
    o --- o --- o --- o --- o --- o --- o
```
-/
def E₈ : Matrix (Fin 8) (Fin 8) ℕ :=
  !![1, 2, 3, 2, 2, 2, 2, 2;
     2, 1, 2, 3, 2, 2, 2, 2;
     3, 2, 1, 3, 2, 2, 2, 2;
     2, 3, 3, 1, 3, 2, 2, 2;
     2, 2, 2, 3, 1, 3, 2, 2;
     2, 2, 2, 2, 3, 1, 3, 2;
     2, 2, 2, 2, 2, 3, 1, 3;
     2, 2, 2, 2, 2, 2, 3, 1]

theorem isCoxeter_E₈ : IsCoxeter E₈ where
  symmetric := by simp [Matrix.IsSymm]; decide
  diagonal := by decide
  off_diagonal := by decide

/-- The Coxeter matrix of system F₄.

The corresponding Coxeter-Dynkin diagram is:
```
             4
    o --- o --- o --- o
```
-/
def F₄ : Matrix (Fin 4) (Fin 4) ℕ :=
  !![1, 3, 2, 2;
     3, 1, 4, 2;
     2, 4, 1, 3;
     2, 2, 3, 1]

theorem isCoxeter_F₄ : IsCoxeter F₄ where
  symmetric := by simp [Matrix.IsSymm]; decide
  diagonal := by decide
  off_diagonal := by decide

/-- The Coxeter matrix of system G₂.

The corresponding Coxeter-Dynkin diagram is:
```
       6
    o --- o
```
-/
def G₂ : Matrix (Fin 2) (Fin 2) ℕ :=
  !![1, 6;
     6, 1]

theorem isCoxeter_G₂ : IsCoxeter G₂ where
  symmetric := by simp [Matrix.IsSymm]; decide
  diagonal := by decide
  off_diagonal := by decide

/-- The Coxeter matrix of system H₃.

The corresponding Coxeter-Dynkin diagram is:
```
       5
    o --- o --- o
```
-/
def H₃ : Matrix (Fin 3) (Fin 3) ℕ :=
  !![1, 3, 2;
     3, 1, 5;
     2, 5, 1]

theorem isCoxeter_H₃ : IsCoxeter H₃ where
  symmetric := by simp [Matrix.IsSymm]; decide
  diagonal := by decide
  off_diagonal := by decide

/-- The Coxeter matrix of system H₄.

The corresponding Coxeter-Dynkin diagram is:
```
       5
    o --- o --- o --- o
```
-/
def H₄ : Matrix (Fin 4) (Fin 4) ℕ :=
  !![1, 3, 2, 2;
     3, 1, 3, 2;
     2, 3, 1, 5;
     2, 2, 5, 1]

theorem isCoxeter_H₄ : IsCoxeter H₄ where
  symmetric := by simp [Matrix.IsSymm]; decide
  diagonal := by decide
  off_diagonal := by decide

end CoxeterMatrix

namespace CoxeterSystem

open Matrix List Function

variable {B : Type*} [DecidableEq B]
variable {M : Matrix B B ℕ}
variable {W : Type*} [Group W]
variable (cs : CoxeterSystem M W)

/-! ### Simple reflections and lifting homomorphisms -/

/-- The simple reflection of `W` corresponding to the index `i`. -/
def simpleReflection (i : B) : W := cs.mulEquiv.symm (PresentedGroup.of i)

local prefix:100 "s" => cs.simpleReflection

private lemma coxeterGroup_simple_mul_self (i : B) :
    (QuotientGroup.mk ((FreeGroup.of i) * (FreeGroup.of i)) : CoxeterGroup M) = 1 := by
  have : (FreeGroup.of i) * (FreeGroup.of i) ∈ CoxeterGroup.Relations.toSet M := by
    use (i, i)
    dsimp [CoxeterGroup.Relations.ofMatrix]
    rw [cs.isCoxeter.diagonal i, pow_one]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact Subgroup.subset_normalClosure this

@[simp] theorem simple_mul_self (i : B) : s i * s i = 1 := by
  dsimp [simpleReflection]
  rw [← _root_.map_mul, PresentedGroup.of, ← QuotientGroup.mk_mul]
  rw [cs.coxeterGroup_simple_mul_self i]
  simp

@[simp] theorem mul_simple_mul_self {w : W} (i : B) : w * s i * s i = w := by
  simp [mul_assoc]

@[simp] theorem simple_mul_self_mul {w : W} (i : B) : s i * (s i * w) = w := by
  simp [← mul_assoc]


@[simp] theorem simple_sqr (i : B) : s i ^ 2 = 1 := by
  rw [pow_two]
  exact cs.simple_mul_self i

@[simp] theorem simple_inv (i : B) : (s i)⁻¹ = s i :=
  (eq_inv_of_mul_eq_one_right (cs.simple_mul_self i)).symm

@[simp] theorem simple_mul_pow (i i' : B) : ((s i) * (s i')) ^ M i i' = 1 := by
  dsimp [simpleReflection]
  rw [← _root_.map_mul, ← map_pow, PresentedGroup.of, PresentedGroup.of,
      ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow]
  have : (FreeGroup.of i * FreeGroup.of i') ^ M i i' ∈ CoxeterGroup.Relations.toSet M := by
    use (i, i')
    rfl
  have : (QuotientGroup.mk ((FreeGroup.of i * FreeGroup.of i') ^ M i i') : CoxeterGroup M) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.subset_normalClosure this
  rw [this]
  simp

@[simp] theorem simple_mul_pow' (i i' : B) : ((s i') * (s i)) ^ M i i' = 1 := by
  rw [cs.isCoxeter.symmetric.apply i' i]
  exact cs.simple_mul_pow i' i

/-- The proposition that the values of the function `f : B → G` satisfy the Coxeter relations
corresponding to the matrix `M`. -/
def IsLiftable {G : Type*} [Monoid G] (M : Matrix B B ℕ) (f : B → G) : Prop :=
    ∀ i i' : B, (f i * f i') ^ M i i' = 1

private theorem relations_liftable {G : Type*} [Group G] {f : B → G} (hf : IsLiftable M f) :
    ∀ r ∈ CoxeterGroup.Relations.toSet M, (FreeGroup.lift f) r = 1 := by
  rintro r ⟨⟨i, i'⟩, rfl⟩
  dsimp [CoxeterGroup.Relations.ofMatrix]
  rw [map_pow, _root_.map_mul, FreeGroup.lift.of, FreeGroup.lift.of]
  exact hf i i'

private def groupLift {G : Type*} [Group G] {f : B → G} (hf : IsLiftable M f) : W →* G :=
  MonoidHom.comp (PresentedGroup.toGroup (relations_liftable hf)) cs.mulEquiv.toMonoidHom

private def restrictUnit {G : Type*} [Monoid G] {f : B → G} (hf : IsLiftable M f) : B → Gˣ :=
  fun i ↦ {
    val := f i,
    inv := f i,
    val_inv := by
      have := hf i i
      rwa [cs.isCoxeter.diagonal, pow_one] at this,
    inv_val := by
      have := hf i i
      rwa [cs.isCoxeter.diagonal, pow_one] at this
  }
/-- Extend the function `f : B → G` to a monoid homomorphism
`f' : W → G` satisfying `f' (s i) = f i` for all `i`.
-/
def lift {G : Type*} [Monoid G] {f : B → G} (hf : IsLiftable M f) : W →* G :=
  MonoidHom.comp (Units.coeHom G) (cs.groupLift
      (show ∀ i i' : B, ((cs.restrictUnit hf) i * (cs.restrictUnit hf) i') ^ M i i' = 1 by
    intro i i'
    apply Units.ext
    simp
    exact hf i i'))

private theorem toMonoidHom_symm (a : PresentedGroup (CoxeterGroup.Relations.toSet M)):
    (MulEquiv.toMonoidHom cs.mulEquiv : W →* PresentedGroup (CoxeterGroup.Relations.toSet M))
    ((MulEquiv.symm cs.mulEquiv) a) = a := calc
  _ = cs.mulEquiv ((MulEquiv.symm cs.mulEquiv) a) := by rfl
  _ = _                                           := by simp

theorem lift_apply_simple {G : Type*} [Monoid G] {f : B → G}
    (hf : IsLiftable M f) (i : B) : cs.lift hf (s i) = f i := by
  dsimp only [simpleReflection, lift, groupLift, MonoidHom.comp_apply]
  rw [← MonoidHom.toFun_eq_coe]
  rw [toMonoidHom_symm cs (PresentedGroup.of i)]
  simp
  rfl

/-! ### Words -/
/-- The product of the simple reflections of `W` corresponding to the indices in `ω`.-/
def wordProd (ω : List B) : W := prod (map cs.simpleReflection ω)

local prefix:100 "π" => cs.wordProd

@[simp] theorem wordProd_nil :
    π [] = 1 := by simp [wordProd]

@[simp] theorem wordProd_cons (i : B) (ω : List B) :
    π (i :: ω) = s i * π ω := by simp [wordProd]

@[simp] theorem wordProd_concat (i : B) (ω : List B) :
    π (ω.concat i) = π ω * s i := by simp [wordProd]

@[simp] theorem wordProd_append (ω ω' : List B) :
    π (ω ++ ω') = π ω * π ω' := by simp [wordProd]

@[simp] theorem wordProd_reverse (ω : List B) :
    π (reverse ω) = (π ω)⁻¹ := by
  induction' ω with x ω' ih
  · simp
  · simp; exact ih

private lemma freeGroup_wordProd (ω : List (B × Bool)) :
    prod (map ((@PresentedGroup.of B (CoxeterGroup.Relations.toSet M)) ∘ Prod.fst) ω)
    = QuotientGroup.mk (FreeGroup.mk ω) := by
  induction' ω with x ω' ih
  · simp [← FreeGroup.one_eq_mk]
  · rw [← List.singleton_append, ← FreeGroup.mul_mk, QuotientGroup.mk_mul, ← ih]
    simp
    rcases x with ⟨i, b⟩
    rcases b
    · have : [(i, false)] = FreeGroup.invRev [(i, true)] := by simp [FreeGroup.invRev]
      rw [this, ← FreeGroup.inv_mk, ← FreeGroup.of, QuotientGroup.mk_inv]
      simp
      rw [PresentedGroup.of]
      apply eq_inv_of_mul_eq_one_right
      rw [← QuotientGroup.mk_mul]
      exact cs.coxeterGroup_simple_mul_self i
    · rfl

theorem wordProd_surjective : Surjective (cs.wordProd) := by
  intro u
  let v : CoxeterGroup M := cs.mulEquiv.toFun u
  rcases (QuotientGroup.mk'_surjective _) v with ⟨w, hw⟩
  simp at hw -- hw: ↑w = v
  let ω := List.map Prod.fst w.toWord
  use ω
  simp [ω, wordProd]
  calc
    prod (List.map (simpleReflection cs ∘ Prod.fst) (FreeGroup.toWord w))
    _ = prod (List.map (
          cs.mulEquiv.symm
          ∘ (@PresentedGroup.of B (CoxeterGroup.Relations.toSet M))
          ∘ Prod.fst)
        (FreeGroup.toWord w))           := by congr
    _ = prod (List.map (
          cs.mulEquiv.symm
          ∘ ((@PresentedGroup.of B (CoxeterGroup.Relations.toSet M))
          ∘ Prod.fst))
        (FreeGroup.toWord w))           := by congr
    _ = prod (List.map cs.mulEquiv.symm
        (List.map ((@PresentedGroup.of B (CoxeterGroup.Relations.toSet M)) ∘ Prod.fst)
          (FreeGroup.toWord w)))        := by rw[List.map_map]
    _ = cs.mulEquiv.symm (prod (List.map
            ((@PresentedGroup.of B (CoxeterGroup.Relations.toSet M)) ∘ Prod.fst)
        (FreeGroup.toWord w)))          := by rw[map_list_prod]
    _ = cs.mulEquiv.symm (QuotientGroup.mk (FreeGroup.mk (FreeGroup.toWord w)))
                                        := by rw[cs.freeGroup_wordProd]
    _ = cs.mulEquiv.symm (QuotientGroup.mk w)
                                        := by rw[FreeGroup.mk_toWord]
    _ = u                               := by rw[hw]; dsimp [v]; simp

end CoxeterSystem