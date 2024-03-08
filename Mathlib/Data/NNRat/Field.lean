import Mathlib.Algebra.Order.Nonneg.Field
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Rat.Field

-- The `LinearOrderedCommGroupWithZero` instance is a shortcut instance for performance
deriving instance CanonicallyLinearOrderedSemifield, LinearOrderedCommGroupWithZero for NNRat
