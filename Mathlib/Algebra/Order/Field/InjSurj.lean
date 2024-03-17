/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import Mathlib.Algebra.Order.Field.Defs
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.Ring.InjSurj

#align_import algebra.order.field.inj_surj from "leanprover-community/mathlib"@"ee0c179cd3c8a45aa5bffbf1b41d8dbede452865"

/-!
# Pulling back linearly ordered fields along injective maps.

-/


open Function OrderDual

variable {ι α β : Type*}

namespace Function
variable [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [Pow β ℕ] [SMul ℕ β] [SMul ℚ≥0 β]
  [SMul ℤ β] [SMul ℚ β] [NatCast β] [IntCast β] [NNRatCast β] [RatCast β] [Inv β] [Div β] [Pow β ℤ]
  [Sup β] [Inf β]

-- See note [reducible non-instances]
/-- Pullback a `LinearOrderedSemifield` under an injective map. -/
@[reducible]
def Injective.linearOrderedSemifield [LinearOrderedSemifield α] (f : β → α) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (nnqsmul : ∀ (x) (q : ℚ≥0), f (q • x) = q • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (nnratCast : ∀ q : ℚ≥0, f q = q)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedSemifield β where
  toLinearOrderedCommSemiring :=
    hf.linearOrderedCommSemiring f zero one add mul nsmul npow natCast hsup hinf
  __ := hf.semifield f zero one add mul inv div nsmul nnqsmul npow zpow natCast nnratCast
#align function.injective.linear_ordered_semifield Function.Injective.linearOrderedSemifield


-- See note [reducible non-instances]
/-- Pullback a `LinearOrderedField` under an injective map. -/
@[reducible]
def Injective.linearOrderedField [LinearOrderedField α] (f : β → α) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (nnqsmul : ∀ (x) (q : ℚ≥0), f (q • x) = q • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (qsmul : ∀ (x) (n : ℚ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n) (nnratCast : ∀ q : ℚ≥0, f q = q)
    (ratCast : ∀ q : ℚ, f q = q) (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y))
    (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) : LinearOrderedField β where
  toLinearOrderedCommRing := hf.linearOrderedCommRing f zero one add mul neg sub nsmul zsmul npow
    natCast intCast hsup hinf
  __ := hf.field f zero one add mul neg sub inv div nsmul nnqsmul zsmul qsmul npow zpow natCast
    intCast nnratCast ratCast
#align function.injective.linear_ordered_field Function.Injective.linearOrderedField

end Function
