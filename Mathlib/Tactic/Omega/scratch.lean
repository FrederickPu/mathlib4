import Std.Data.Int.Basic
import Std.Data.Rat.Basic
import Mathlib.Tactic.Use
import Std.Tactic.Simpa
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.SplitIfs
import Mathlib.Util.Time

-- We follow "The Omega Test: a fast and practical integer programming algorithm for dependence analysis."

set_option autoImplicit true

namespace Array

@[simp] theorem zip_data {A : Array α} {B : Array β} : (A.zip B).data = A.data.zip B.data := sorry

end Array

open Nat

instance (L : List (Option α)) : Decidable (none ∈ L) := sorry

def Nat.arrayGCD (x : Array Nat) : Nat := x.foldr gcd 0
def Int.arrayGCD (x : Array Int) : Nat := x.foldr (fun a b => gcd a.natAbs b) 0

#time example : Nat.gcd (17*19*101^2*1024) (17*19*101*4*39) = 130492 := rfl
#time example : Int.arrayGCD #[45, -15, 85] = 5 := rfl
#time example : Int.arrayGCD #[17*19*101*101*1024, -17*19*101*4*39, 17*19*39] = 323 := rfl

def Int.bmod (x : Int) (m : Nat) : Int :=
  let r := x % m
  if r < m / 2 then
    r
  else
    r - m

example : Int.bmod 12 7 = -2 := rfl

namespace Omega

structure LinearCombo where
  constantTerm : Int
  coefficients : Array Int
  gcd : Nat
  -- gcd = Int.arrayGCD coefficients
  smallIdx : Fin coefficients.size
  -- coefficients[smallIdx] ≠ 0
  -- ∀ c ∈ coefficients, c = 0 ∨ c.natAbs ≥ coefficients[smallIdx]

structure Problem where
  impossible : Bool
  equalities : List LinearCombo
  inequalities : List LinearCombo

namespace LinearCombo

def eval (lc : LinearCombo) (values : Array Int) : Int := Id.run do
  let mut r := lc.constantTerm
  for c in lc.coefficients, x in values do
    r := r + c * x
  return r

def evalRat (lc : LinearCombo) (values : Array Rat) : Rat := Id.run do
  let mut r : Rat := lc.constantTerm
  for c in lc.coefficients, x in values do
    r := r + c * x
  return r

variable {lc : LinearCombo}

theorem eval_eq : lc.eval values =
    (lc.coefficients.zip values).foldl (fun r ⟨c, x⟩ => r + c * x) lc.constantTerm :=  by
  sorry

theorem evalRat_eq : lc.evalRat values =
    (lc.coefficients.zip values).foldl (fun r ⟨c, x⟩ => r + c * x) (lc.constantTerm : Rat) :=  by
  sorry

example : List.zip (a :: as) (b :: bs) = (a, b) :: List.zip as bs := by
  simp -- Fine, `List.zip_cons_cons` is missing

example : List.foldl f x (List.zip (a :: as) (b :: bs)) = f (List.foldl f x (List.zip as bs)) (a, b) := by
  simp -- `simp?` says `simp only [List.foldl]`, but this isn't even marked with `@[simp]`.
  -- Goal has become
  -- List.foldl f (f x (a, b)) (List.zipWith Prod.mk as bs) = f (List.foldl f x (List.zip as bs)) (a, b)
  -- Note that `List.zip` has been unfolded to `List.zipWith Prod.mk`!
  sorry

theorem evalRat_cast (lc : LinearCombo) (values : Array Int) :
    lc.evalRat (values.map fun x : Int => (x : Rat)) = lc.eval values := by
  rw [eval_eq, evalRat_eq]
  simp [Array.foldl_eq_foldl_data]
  rcases lc with ⟨const, ⟨coeffs⟩⟩
  rcases values with ⟨values⟩
  dsimp
  induction coeffs generalizing const values with
  | nil => simp
  | cons c coeffs cih =>
    rcases values with _ | ⟨v, values⟩
    · simp
    · specialize cih (const + c * v) _ values
      sorry
      dsimp?




def satZero (lc : LinearCombo) : Prop :=
  ∃ values, lc.eval values = 0

def satRatZero (lc : LinearCombo) : Prop :=
  ∃ values, lc.evalRat values = 0

def satNonneg (lc : LinearCombo) : Prop :=
  ∃ values, lc.eval values ≥ 0

def satRatNoneg (lc : LinearCombo) : Prop :=
  ∃ values, lc.evalRat values ≥ 0

variable {lc : LinearCombo}

theorem satZero_of_satRatZero : lc.satZero → lc.satRatZero := by
  rintro ⟨values, w⟩
  use values.map fun x : Int => (x : Rat)
  rw [evalRat_cast, w]
  rfl

theorem satNoneg_of_satRatNonneg : lc.satNonneg → lc.satRatNoneg := by
  rintro ⟨values, w⟩
  use values.map fun x : Int => (x : Rat)
  rw [evalRat_cast]
  sorry

def normalizeEquality : LinearCombo → Option LinearCombo
  | {constantTerm, coefficients, gcd, smallIdx} =>
    if constantTerm % gcd = 0 then
      some
      { constantTerm := constantTerm / gcd,
        coefficients := coefficients.map (· / gcd),
        gcd := 1,
        smallIdx := Fin.cast (by simp) smallIdx }
    else
      none

def normalizeInequality : LinearCombo → LinearCombo
  | {constantTerm, coefficients, gcd, smallIdx} =>
    { -- Recall `Int.fdiv` is division with floor rounding.
      constantTerm := Int.fdiv constantTerm gcd
      coefficients := coefficients.map (· / gcd)
      gcd := 1,
        smallIdx := Fin.cast (by simp) smallIdx }

theorem not_sat_of_normalizeEquality_isNone {lc : LinearCombo} :
    normalizeEquality lc = none → ¬ lc.satZero := sorry
theorem sat_iff_normalizeEquality_sat {lc lc' : LinearCombo} :
    (lc' ∈ lc.normalizeEquality) → lc'.satZero ↔ lc.satZero := sorry
theorem sat_iff_normalizeInequality_sat {lc : LinearCombo} :
    lc.normalizeInequality.satNonneg ↔ lc.satNonneg := sorry

-- Do we need statements here about satisfiability over `Rat`?

end LinearCombo

open LinearCombo

namespace Problem

def bot : Problem := { impossible := true, equalities := [], inequalities := [] }

def sat (p : Problem) : Prop :=
  p.impossible = false ∧ (∀ lc ∈ p.equalities, lc.satZero) ∧ (∀ lc ∈ p.inequalities, lc.satNonneg)

@[simp] theorem not_bot_sat : ¬ bot.sat := by
  simp [bot, sat]

def normalize (p : Problem) : Problem :=
  if p.impossible then
     bot
  else
    let normalizedEqualities := p.equalities.map LinearCombo.normalizeEquality
    if none ∈ normalizedEqualities then
      bot
    else
      { impossible := false,
        equalities := normalizedEqualities.filterMap fun x => x
        inequalities := p.inequalities.map LinearCombo.normalizeInequality }

theorem normalize_sat_iff_sat {p : Problem} : p.normalize.sat ↔ p.sat := by
  rw [normalize]
  split_ifs with h₁
  · simp [sat, h₁]
  · simp only [List.mem_map]
    split_ifs with h₂
    · simp at h₂
      obtain ⟨e, m, w⟩ := h₂
      replace w := not_sat_of_normalizeEquality_isNone w
      simp only [sat, h₁]
      -- trivial from here
      simp
      intro w'
      specialize w' _ m
      apply False.elim
      exact w w'
    · simp only [sat, h₁]
      refine Iff.and (by trivial) (Iff.and ?_ ?_)
      · sorry
      · sorry




end Problem
