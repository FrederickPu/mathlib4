/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Algebra.Order.Nonneg.Field
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Rat.Order

#align_import data.rat.basic from "leanprover-community/mathlib"@"a59dad53320b73ef180174aae867addd707ef00e"

/-!
# Field Structure on the Rational Numbers

## Summary

We put the (discrete) field structure on the type `ℚ` of rational numbers that
was defined in `Mathlib.Data.Rat.Defs`.

## Main Definitions

- `Rat.instField` is the field structure on `ℚ`.

## Implementation notes

We have to define the field structure in a separate file to avoid cyclic imports:
the `Field` class contains a map from `ℚ` (see `Field`'s docstring for the rationale),
so we have a dependency `Rat.field → Field → Rat` that is reflected in the import
hierarchy `Mathlib.Data.Rat.basic → Mathlib.Algebra.Field.Defs → Std.Data.Rat`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom
-/

namespace Rat

instance instField : Field ℚ where
  toCommRing := commRing
  __ := commGroupWithZero
  nnratCast := (↑)
  nnratCast_def q := by
    rw [← NNRat.den_coe, ← Int.cast_natCast q.num, ← NNRat.num_coe]; exact(num_div_den _).symm
  ratCast_def a b h1 h2 := (num_div_den _).symm

-- Extra instances to short-circuit type class resolution
instance instDivisionRing : DivisionRing ℚ := by infer_instance

instance instLinearOrderedField : LinearOrderedField ℚ where
  toLinearOrderedCommRing := instLinearOrderedCommRing
  __ := instField

end Rat

-- The `LinearOrderedSemifield` and `LinearOrderedCommGroupWithZero` instances are shortcut
-- instances for performance
deriving instance CanonicallyLinearOrderedSemifield, LinearOrderedSemifield,
  LinearOrderedCommGroupWithZero for NNRat
