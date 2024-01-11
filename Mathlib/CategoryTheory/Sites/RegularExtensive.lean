/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Filippo A. E. Nuccio, Riccardo Brasca
-/
import Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.Preadditive.Projective
import Mathlib.CategoryTheory.Sites.Coherent
import Mathlib.CategoryTheory.Sites.Preserves
/-!

# The Regular and Extensive Coverages

This file defines two coverages on a category `C`.

The first one is called the *regular* coverage and for that to exist, the category `C` must satisfy
a condition called `Preregular C`. This means that effective epimorphisms can be "pulled back". The
covering sieves of this coverage are generated by presieves consisting of a single effective
epimorphism.

The second one is called the *extensive* coverage and for that to exist, the category `C` must
satisfy a condition called `FinitaryPreExtensive C`. This means `C` has finite coproducts and that
those are preserved by pullbacks. The covering sieves of this coverage are generated by presieves
consisting finitely many arrows that together induce an isomorphism from the coproduct to the
target. This condition is weaker than `FinitaryExtensive`, where in addition finite coproducts are
disjoint.

## Main results

* `instance : Precoherent C` given `Preregular C` and `FinitaryPreExtensive C`.

* `extensive_union_regular_generates_coherent`: the union of the regular and extensive coverages
  generates the coherent topology on `C` if `C` is precoherent, preextensive and preregular.

* `isSheaf_iff_equalizerCondition`: In a preregular category with pullbacks, the sheaves for the
  regular topology are precisely the presheaves satisfying an equaliser condition with respect to
  effective epimorphisms.

* `isSheaf_of_projective`: In a preregular category in which every object is projective, every
  presheaf is a sheaf for the regular topology.

* `isSheaf_iff_preservesFiniteProducts`: In a finitary extensive category, the sheaves for the
  extensive topology are precisely those preserving finite products.

-/

universe v u w

namespace CategoryTheory

open Limits

variable (C : Type u) [Category.{v} C]

/--
The condition `Preregular C` is property that effective epis can be "pulled back" along any
morphism. This is satisfied e.g. by categories that have pullbacks that preserve effective
epimorphisms (like `Profinite` and `CompHaus`), and categories where every object is projective
(like  `Stonean`).
-/
class Preregular : Prop where
  /--
  For `X`, `Y`, `Z`, `f`, `g` like in the diagram, where `g` is an effective epi, there exists
  an object `W`, an effective epi `h : W ⟶ X` and a morphism `i : W ⟶ Z` making the diagram
  commute.
  ```
  W --i-→ Z
  |       |
  h       g
  ↓       ↓
  X --f-→ Y
  ```
  -/
  exists_fac : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ Y) [EffectiveEpi g],
    (∃ (W : C) (h : W ⟶ X) (_ : EffectiveEpi h) (i : W ⟶ Z), i ≫ g = h ≫ f)

instance [Precoherent C] [HasFiniteCoproducts C] : Preregular C where
  exists_fac {X Y Z} f g _ := by
    have hp := Precoherent.pullback f PUnit (fun () ↦ Z) (fun () ↦ g)
    simp only [exists_const] at hp
    rw [← effectiveEpi_iff_effectiveEpiFamily g] at hp
    obtain ⟨β, _, X₂, π₂, h, ι, hι⟩ := hp inferInstance
    refine ⟨∐ X₂, Sigma.desc π₂, inferInstance, Sigma.desc ι, ?_⟩
    ext b
    simpa using hι b

/--
The regular coverage on a regular category `C`.
-/
def regularCoverage [Preregular C] : Coverage C where
  covering B := { S | ∃ (X : C) (f : X ⟶ B), S = Presieve.ofArrows (fun (_ : Unit) ↦ X)
    (fun (_ : Unit) ↦ f) ∧ EffectiveEpi f }
  pullback := by
    intro X Y f S ⟨Z, π, hπ, h_epi⟩
    have := Preregular.exists_fac f π
    obtain ⟨W, h, _, i, this⟩ := this
    refine ⟨Presieve.singleton h, ⟨?_, ?_⟩⟩
    · exact ⟨W, h, by {rw [Presieve.ofArrows_pUnit h]}, inferInstance⟩
    · intro W g hg
      cases hg
      refine ⟨Z, i, π, ⟨?_, this⟩⟩
      cases hπ
      rw [Presieve.ofArrows_pUnit]
      exact Presieve.singleton.mk

/--
The extensive coverage on an extensive category `C`

TODO: use general colimit API instead of `IsIso (Sigma.desc π)`
-/
def extensiveCoverage [FinitaryPreExtensive C] : Coverage C where
  covering B := { S | ∃ (α : Type) (_ : Fintype α) (X : α → C) (π : (a : α) → (X a ⟶ B)),
    S = Presieve.ofArrows X π ∧ IsIso (Sigma.desc π) }
  pullback := by
    intro X Y f S ⟨α, hα, Z, π, hS, h_iso⟩
    let Z' : α → C := fun a ↦ pullback f (π a)
    let π' : (a : α) → Z' a ⟶ Y := fun a ↦ pullback.fst
    refine ⟨@Presieve.ofArrows C _ _ α Z' π', ⟨?_, ?_⟩⟩
    · constructor
      exact ⟨hα, Z', π', ⟨by simp only, FinitaryPreExtensive.sigma_desc_iso (fun x => π x) f h_iso⟩⟩
    · intro W g hg
      rcases hg with ⟨a⟩
      refine ⟨Z a, pullback.snd, π a, ?_, by rw [CategoryTheory.Limits.pullback.condition]⟩
      rw [hS]
      exact Presieve.ofArrows.mk a

theorem effectiveEpi_desc_iff_effectiveEpiFamily [FinitaryPreExtensive C] {α : Type} [Fintype α]
    {B : C} (X : α → C) (π : (a : α) → X a ⟶ B) :
    EffectiveEpi (Sigma.desc π) ↔ EffectiveEpiFamily X π := by
  exact ⟨fun h ↦ ⟨⟨@effectiveEpiFamilyStructOfEffectiveEpiDesc _ _ _ _ X π _ h _ _ (fun g ↦
    (FinitaryPreExtensive.sigma_desc_iso (fun a ↦ Sigma.ι X a) g inferInstance).epi_of_iso)⟩⟩,
    fun _ ↦ inferInstance⟩

instance [FinitaryPreExtensive C] [Preregular C] : Precoherent C where
  pullback {B₁ B₂} f α _ X₁ π₁ h := by
    refine ⟨α, inferInstance, ?_⟩
    obtain ⟨Y, g, _, g', hg⟩ := Preregular.exists_fac f (Sigma.desc π₁)
    let X₂ := fun a ↦ pullback g' (Sigma.ι X₁ a)
    let π₂ := fun a ↦ pullback.fst (f := g') (g := Sigma.ι X₁ a) ≫ g
    let π' := fun a ↦ pullback.fst (f := g') (g := Sigma.ι X₁ a)
    have _ := FinitaryPreExtensive.sigma_desc_iso (fun a ↦ Sigma.ι X₁ a) g' inferInstance
    refine ⟨X₂, π₂, ?_, ?_⟩
    · have : (Sigma.desc π' ≫ g) = Sigma.desc π₂ := by ext; simp
      rw [← effectiveEpi_desc_iff_effectiveEpiFamily, ← this]
      infer_instance
    · refine ⟨id, fun b ↦ pullback.snd, fun b ↦ ?_⟩
      simp only [id_eq, Category.assoc, ← hg]
      rw [← Category.assoc, pullback.condition]
      simp

/-- The union of the extensive and regular coverages generates the coherent topology on `C`. -/
lemma extensive_regular_generate_coherent [Preregular C] [FinitaryPreExtensive C] :
    ((extensiveCoverage C) ⊔ (regularCoverage C)).toGrothendieck =
    (coherentTopology C) := by
  ext B S
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · induction h with
    | of Y T hT =>
      apply Coverage.saturate.of
      simp only [Coverage.sup_covering, Set.mem_union] at hT
      exact Or.elim hT
        (fun ⟨α, x, X, π, ⟨h, _⟩⟩ ↦ ⟨α, x, X, π, ⟨h, inferInstance⟩⟩)
        (fun ⟨Z, f, ⟨h, _⟩⟩ ↦ ⟨Unit, inferInstance, fun _ ↦ Z, fun _ ↦ f, ⟨h, inferInstance⟩⟩)
    | top => apply Coverage.saturate.top
    | transitive Y T => apply Coverage.saturate.transitive Y T<;> [assumption; assumption]
  · induction h with
    | of Y T hT =>
      obtain ⟨I, hI, X, f, ⟨h, hT⟩⟩ := hT
      let φ := fun (i : I) ↦ Sigma.ι X i
      let F := Sigma.desc f
      let Z := Sieve.generate T
      let Xs := (∐ fun (i : I) => X i)
      let Zf := Sieve.generate (Presieve.ofArrows (fun (_ : Unit) ↦ Xs) (fun (_ : Unit) ↦ F))
      apply Coverage.saturate.transitive Y Zf
      · apply Coverage.saturate.of
        simp only [Coverage.sup_covering, extensiveCoverage, regularCoverage, Set.mem_union,
          Set.mem_setOf_eq]
        exact Or.inr ⟨Xs, F, ⟨rfl, inferInstance⟩⟩
      · intro R g hZfg
        dsimp at hZfg
        rw [Presieve.ofArrows_pUnit] at hZfg
        obtain ⟨W, ψ, σ, ⟨hW, hW'⟩⟩ := hZfg
        induction hW
        rw [← hW', Sieve.pullback_comp Z]
        suffices Sieve.pullback ψ ((Sieve.pullback F) Z) ∈ GrothendieckTopology.sieves
          ((extensiveCoverage C) ⊔ (regularCoverage C)).toGrothendieck R by assumption
        apply GrothendieckTopology.pullback_stable'
        suffices Coverage.saturate ((extensiveCoverage C) ⊔ (regularCoverage C)) Xs
          (Z.pullback F) by assumption
        suffices : Sieve.generate (Presieve.ofArrows X φ) ≤ Z.pullback F
        · apply Coverage.saturate_of_superset _ this
          apply Coverage.saturate.of
          simp only [Coverage.sup_covering, extensiveCoverage, regularCoverage, Set.mem_union,
            Set.mem_setOf_eq]
          refine Or.inl ⟨I, hI, X, φ, ⟨rfl, ?_⟩⟩
          suffices Sigma.desc φ = 𝟙 _ by rw [this]; infer_instance
          ext
          simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app, Category.comp_id]
        intro Q q hq
        simp only [Sieve.pullback_apply, Sieve.generate_apply]
        simp only [Sieve.generate_apply] at hq
        obtain ⟨E, e, r, hq⟩ := hq
        refine' ⟨E, e, r ≫ F, ⟨_, _⟩⟩
        · rw [h]
          induction hq.1
          simp only [colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app]
          exact Presieve.ofArrows.mk _
        · rw [← hq.2]
          simp only [Category.assoc]
    | top => apply Coverage.saturate.top
    | transitive Y T => apply Coverage.saturate.transitive Y T<;> [assumption; assumption]

section RegularSheaves

variable {C}

open Opposite Presieve

/-- A presieve is *regular* if it consists of a single effective epimorphism. -/
class Presieve.regular {X : C} (R : Presieve X) : Prop where
  /-- `R` consists of a single epimorphism. -/
  single_epi : ∃ (Y : C) (f : Y ⟶ X), R = Presieve.ofArrows (fun (_ : Unit) ↦ Y)
    (fun (_ : Unit) ↦ f) ∧ EffectiveEpi f

namespace regularCoverage

/--
The map to the explicit equalizer used in the sheaf condition.
-/
def MapToEqualizer (P : Cᵒᵖ ⥤ Type (max u v)) {W X B : C} (f : X ⟶ B)
    (g₁ g₂ : W ⟶ X) (w : g₁ ≫ f = g₂ ≫ f) :
    P.obj (op B) → { x : P.obj (op X) | P.map g₁.op x = P.map g₂.op x } := fun t ↦
  ⟨P.map f.op t, by simp only [Set.mem_setOf_eq, ← FunctorToTypes.map_comp_apply, ← op_comp, w]⟩

/--
The sheaf condition with respect to regular presieves, given the existence of the relavant pullback.
-/
def EqualizerCondition (P : Cᵒᵖ ⥤ Type (max u v)) : Prop :=
  ∀ (X B : C) (π : X ⟶ B) [EffectiveEpi π] [HasPullback π π], Function.Bijective
    (MapToEqualizer P π (pullback.fst (f := π) (g := π)) (pullback.snd (f := π) (g := π))
    pullback.condition)

lemma EqualizerCondition.isSheafFor {B : C} {S : Presieve B} [S.regular] [S.hasPullbacks]
    {F : Cᵒᵖ ⥤ Type (max u v)}
    (hF : EqualizerCondition F) : S.IsSheafFor F := by
  obtain ⟨X, π, hS, πsurj⟩ := Presieve.regular.single_epi (R := S)
  subst hS
  rw [isSheafFor_arrows_iff_pullbacks]
  intro y h
  have : (Presieve.singleton π).hasPullbacks := by rw [← ofArrows_pUnit]; infer_instance
  have : HasPullback π π := hasPullbacks.has_pullbacks Presieve.singleton.mk Presieve.singleton.mk
  specialize hF X B π
  rw [Function.bijective_iff_existsUnique] at hF
  obtain ⟨t, ht, ht'⟩ := hF ⟨y (), h () ()⟩
  refine ⟨t, fun _ ↦ ?_, fun x h ↦ ht' x ?_⟩
  · simpa [MapToEqualizer] using ht
  · simpa [MapToEqualizer] using h ()

lemma equalizerCondition_of_regular {F : Cᵒᵖ ⥤ Type (max u v)}
    (hSF : ∀ {B : C} (S : Presieve B) [S.regular] [S.hasPullbacks], S.IsSheafFor F) :
    EqualizerCondition F := by
  intro X B π _ _
  have : (ofArrows (fun _ ↦ X) (fun _ ↦ π)).regular := ⟨X, π, rfl, inferInstance⟩
  have : (ofArrows (fun () ↦ X) (fun _ ↦ π)).hasPullbacks := ⟨
      fun hf _ hg ↦ (by cases hf; cases hg; infer_instance)⟩
  specialize hSF (ofArrows (fun () ↦ X) (fun _ ↦ π))
  rw [isSheafFor_arrows_iff_pullbacks] at hSF
  rw [Function.bijective_iff_existsUnique]
  intro ⟨x, hx⟩
  obtain ⟨t, ht, ht'⟩ := hSF (fun _ ↦ x) (fun _ _ ↦ hx)
  refine ⟨t, ?_, fun y h ↦ ht' y ?_⟩
  · simpa [MapToEqualizer] using ht ()
  · simpa [MapToEqualizer] using h

lemma isSheafFor_regular_of_projective {X : C} (S : Presieve X) [S.regular] [Projective X]
    (F : Cᵒᵖ ⥤ Type (max u v)) : S.IsSheafFor F := by
  obtain ⟨Y, f, rfl, hf⟩ := Presieve.regular.single_epi (R := S)
  rw [isSheafFor_arrows_iff]
  refine fun x hx ↦ ⟨F.map (Projective.factorThru (𝟙 _) f).op <| x (), fun _ ↦ ?_, fun y h ↦ ?_⟩
  · simpa using (hx () () Y (𝟙 Y) (f ≫ (Projective.factorThru (𝟙 _) f)) (by simp)).symm
  · simp only [← h (), ← FunctorToTypes.map_comp_apply, ← op_comp, Projective.factorThru_comp,
      op_id, FunctorToTypes.map_id_apply]

lemma EqualizerCondition.isSheaf_iff (F : Cᵒᵖ ⥤ Type (max u v))
    [∀ ⦃X Y : C⦄ (π : X ⟶ Y) [EffectiveEpi π], HasPullback π π] [Preregular C] :
    Presieve.IsSheaf (regularCoverage C).toGrothendieck F ↔ EqualizerCondition F := by
  rw [Presieve.isSheaf_coverage]
  refine ⟨fun h ↦ equalizerCondition_of_regular fun S ⟨Y, f, hh⟩ _ ↦ h S ⟨Y, f, hh⟩, ?_⟩
  rintro h X S ⟨Y, f, rfl, hf⟩
  exact @isSheafFor _ _ _ _ ⟨Y, f, rfl, hf⟩ ⟨fun g _ h ↦ by cases g; cases h; infer_instance⟩ _ h

lemma isSheaf_of_projective (F : Cᵒᵖ ⥤ Type (max u v)) [Preregular C] [∀ (X : C), Projective X] :
    IsSheaf (regularCoverage C).toGrothendieck F :=
  (isSheaf_coverage _ _).mpr fun S ⟨_, h⟩ ↦ have : S.regular := ⟨_, h⟩
    isSheafFor_regular_of_projective _ _

/-- Every Yoneda-presheaf is a sheaf for the regular topology. -/
theorem isSheaf_yoneda_obj [Preregular C] (W : C)  :
    Presieve.IsSheaf (regularCoverage C).toGrothendieck (yoneda.obj W) := by
  rw [isSheaf_coverage]
  intro X S ⟨_, hS⟩
  have : S.regular := ⟨_, hS⟩
  obtain ⟨Y, f, rfl, hf⟩ := Presieve.regular.single_epi (R := S)
  have h_colim := isColimitOfEffectiveEpiStruct f hf.effectiveEpi.some
  rw [← Sieve.generateSingleton_eq, ← Presieve.ofArrows_pUnit] at h_colim
  intro x hx
  let x_ext := Presieve.FamilyOfElements.sieveExtend x
  have hx_ext := Presieve.FamilyOfElements.Compatible.sieveExtend hx
  let S := Sieve.generate (Presieve.ofArrows (fun () ↦ Y) (fun () ↦ f))
  obtain ⟨t, t_amalg, t_uniq⟩ :=
    (Sieve.forallYonedaIsSheaf_iff_colimit S).mpr ⟨h_colim⟩ W x_ext hx_ext
  refine ⟨t, ?_, ?_⟩
  · convert Presieve.isAmalgamation_restrict (Sieve.le_generate
      (Presieve.ofArrows (fun () ↦ Y) (fun () ↦ f))) _ _ t_amalg
    exact (Presieve.restrict_extend hx).symm
  · exact fun y hy ↦ t_uniq y <| Presieve.isAmalgamation_sieveExtend x y hy

/-- The regular topology on any preregular category is subcanonical. -/
theorem subcanonical [Preregular C] : Sheaf.Subcanonical (regularCoverage C).toGrothendieck :=
  Sheaf.Subcanonical.of_yoneda_isSheaf _ isSheaf_yoneda_obj

end regularCoverage

end RegularSheaves

section ExtensiveSheaves

variable [FinitaryPreExtensive C] {C}

/-- A presieve is *extensive* if it is finite and its arrows induce an isomorphism from the
coproduct to the target. -/
class Presieve.extensive {X : C} (R : Presieve X) :
    Prop where
  /-- `R` consists of a finite collection of arrows that together induce an isomorphism from the
  coproduct of their sources. -/
  arrows_nonempty_isColimit : ∃ (α : Type) (_ : Fintype α) (Z : α → C) (π : (a : α) → (Z a ⟶ X)),
    R = Presieve.ofArrows Z π ∧ Nonempty (IsColimit (Cofan.mk X π))

instance {X : C} (S : Presieve X) [S.extensive] : S.hasPullbacks where
  has_pullbacks := by
    obtain ⟨_, _, _, _, rfl, ⟨hc⟩⟩ := Presieve.extensive.arrows_nonempty_isColimit (R := S)
    intro _ _ _ _ _ hg
    cases hg
    apply FinitaryPreExtensive.hasPullbacks_of_is_coproduct hc

instance {α : Type} [Fintype α] {Z : α → C} {F : C ⥤ Type w}
    [PreservesFiniteProducts F] : PreservesLimit (Discrete.functor fun a => (Z a)) F :=
  (PreservesFiniteProducts.preserves α).preservesLimit

open Presieve Opposite

/--
A finite product preserving presheaf is a sheaf for the extensive topology on a category which is
`FinitaryPreExtensive`.
-/
theorem isSheafFor_extensive_of_preservesFiniteProducts {X : C} (S : Presieve X) [S.extensive]
    (F : Cᵒᵖ ⥤ Type max u v) [PreservesFiniteProducts F] : S.IsSheafFor F  := by
  obtain ⟨_, _, Z, π, rfl, ⟨hc⟩⟩ := extensive.arrows_nonempty_isColimit (R := S)
  have : (ofArrows Z (Cofan.mk X π).inj).hasPullbacks :=
    (inferInstance : (ofArrows Z π).hasPullbacks)
  exact isSheafFor_of_preservesProduct _ _ hc

instance {α : Type} [Fintype α] (Z : α → C) : (ofArrows Z (fun i ↦ Sigma.ι Z i)).extensive :=
  ⟨⟨α, inferInstance, Z, (fun i ↦ Sigma.ι Z i), rfl, ⟨coproductIsCoproduct _⟩⟩⟩

/--
A presheaf on a category which is `FinitaryExtensive` is a sheaf iff it preserves finite products.
-/
theorem isSheaf_iff_preservesFiniteProducts [FinitaryExtensive C] (F : Cᵒᵖ ⥤ Type max u v) :
    Presieve.IsSheaf (extensiveCoverage C).toGrothendieck F ↔
    Nonempty (PreservesFiniteProducts F) := by
  refine ⟨fun hF ↦ ⟨⟨fun α _ ↦ ⟨fun {K} ↦ ?_⟩⟩⟩, fun hF ↦ ?_⟩
  · rw [Presieve.isSheaf_coverage] at hF
    let Z : α → C := fun i ↦ unop (K.obj ⟨i⟩)
    have : (Presieve.ofArrows Z (Cofan.mk (∐ Z) (Sigma.ι Z)).inj).hasPullbacks :=
      (inferInstance : (Presieve.ofArrows Z (Sigma.ι Z)).hasPullbacks)
    have : ∀ (i : α), Mono (Cofan.inj (Cofan.mk (∐ Z) (Sigma.ι Z)) i) :=
      (inferInstance : ∀ (i : α), Mono (Sigma.ι Z i))
    let i : K ≅ Discrete.functor (fun i ↦ op (Z i)) := Discrete.natIsoFunctor
    let _ : PreservesLimit (Discrete.functor (fun i ↦ op (Z i))) F :=
        Presieve.preservesProductOfIsSheafFor F ?_ initialIsInitial _ (coproductIsCoproduct Z)
        (FinitaryExtensive.isPullback_initial_to_sigma_ι Z)
        (hF (Presieve.ofArrows Z (fun i ↦ Sigma.ι Z i)) ?_)
    · exact preservesLimitOfIsoDiagram F i.symm
    · apply hF
      refine ⟨Empty, inferInstance, Empty.elim, IsEmpty.elim inferInstance, rfl, ⟨default,?_, ?_⟩⟩
      · ext b
        cases b
      · simp only [eq_iff_true_of_subsingleton]
    · refine ⟨α, inferInstance, Z, (fun i ↦ Sigma.ι Z i), rfl, ?_⟩
      suffices Sigma.desc (fun i ↦ Sigma.ι Z i) = 𝟙 _ by rw [this]; infer_instance
      ext
      simp
  · let _ := hF.some
    rw [Presieve.isSheaf_coverage]
    intro X R ⟨Y, α, Z, π, hR, hi⟩
    have : IsIso (Sigma.desc (Cofan.inj (Cofan.mk X π))) := hi
    have : R.extensive := ⟨Y, α, Z, π, hR, ⟨Cofan.isColimitOfIsIsoSigmaDesc (Cofan.mk X π)⟩⟩
    exact isSheafFor_extensive_of_preservesFiniteProducts R F

end ExtensiveSheaves

end CategoryTheory