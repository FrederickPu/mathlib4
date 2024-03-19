/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes

/-!
#
-/

open CategoryTheory.Limits

universe w' w v u

namespace CategoryTheory.FunctorToTypes

variable {C : Type u} [Category.{v} C]

variable (F G : C ⥤ Type v)

def internalHom : C ⥤ Type max u v where
  obj a := (prod (coyoneda.obj (.op a)) F) ⟶ G
  map {X Y} f g := {
    app := by
      rintro b ⟨p1, p2⟩
      exact g.app b ⟨(coyoneda.map (.op f)).app b p1, p2⟩
    naturality := by
      intro W Z g
      ext l
      sorry
  }
