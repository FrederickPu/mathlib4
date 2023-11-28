/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Data.Countable.Small
import Mathlib.CategoryTheory.FinCategory
/-!
# Countable categories

A category is countable in this sense if it has countably many objects and countably many morphisms.

-/

universe w v

open Classical

noncomputable section

namespace CategoryTheory

instance discreteCountable {α : Type*} [Countable α] : Countable (Discrete α) :=
  Countable.of_equiv α discreteEquiv.symm

/-- A category with countably many objects and morphisms. -/
class CountableCategory (J : Type*) [SmallCategory J] : Prop where
  countableObj : Countable J := by infer_instance
  countableHom : ∀ j j' : J, Countable (j ⟶ j') := by infer_instance

attribute [instance] CountableCategory.countableObj CountableCategory.countableHom

instance countablerCategoryDiscreteOfCountable (J : Type*) [Countable J] :
    CountableCategory (Discrete J) where

namespace CountableCategory

variable (α : Type*) [Countable α] [SmallCategory α] [CountableCategory α]

/-- A countable category `α` is equivalent to a category with objects in `Type`. -/
abbrev ObjAsType : Type :=
  InducedCategory α (equivShrink.{0} α).symm

instance {i j : ObjAsType α} : Countable (i ⟶ j) :=
  CountableCategory.countableHom ((equivShrink.{0} α).symm i) _

/-- The constructed category is indeed equivalent to `α`. -/
noncomputable def objAsTypeEquiv : ObjAsType α ≌ α :=
  (inducedFunctor (equivShrink.{0} α).symm).asEquivalence

end CountableCategory

instance (α : Type*) [SmallCategory α] [FinCategory α] : CountableCategory α where

open Opposite

/-- The opposite of a countable category is countable. -/
instance countableCategoryOpposite {J : Type*} [SmallCategory J] [CountableCategory J] :
    CountableCategory Jᵒᵖ where
  countableObj := Countable.of_equiv _ equivToOpposite
  countableHom j j' := Countable.of_equiv _ (opEquiv j j').symm

/-- Applying `ULift` to morphisms and objects of a category preserves countability. -/
instance countableCategoryUlift {J : Type v} [SmallCategory J] [CountableCategory J] :
    CountableCategory.{max w v} (ULiftHom.{w, max w v} (ULift.{w, v} J)) where
  countableObj := instCountableULift
  countableHom := fun _ _ => instCountableULift

end CategoryTheory
