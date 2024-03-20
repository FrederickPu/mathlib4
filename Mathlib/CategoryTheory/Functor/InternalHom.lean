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

variable (F G : Cᵒᵖ ⥤ Type v)

def internalHom : Cᵒᵖ ⥤ Type max u v where
  obj a := prod (yoneda.obj a.unop) F ⟶ G
  map {X Y} f H := {
    app := fun b p => H.app b ⟨(yoneda.map f.unop).app b p.1, p.2⟩
    naturality := fun W Z h => by
      ext l
      have := congr_fun (H.naturality h) (l.1 ≫ f.unop, l.2)
      simp [prod]
      aesop
  }
