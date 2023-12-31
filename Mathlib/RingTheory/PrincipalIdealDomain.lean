/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Morenikeji Neri
-/
import Mathlib.Algebra.EuclideanDomain.Instances
import Mathlib.RingTheory.UniqueFactorizationDomain

#align_import ring_theory.principal_ideal_domain from "leanprover-community/mathlib"@"6010cf523816335f7bae7f8584cb2edaace73940"

/-!
# Principal ideal rings and principal ideal domains

A principal ideal ring (PIR) is a ring in which all left ideals are principal. A
principal ideal domain (PID) is an integral domain which is a principal ideal ring.

# Main definitions

Note that for principal ideal domains, one should use
`[IsDomain R] [IsPrincipalIdealRing R]`. There is no explicit definition of a PID.
Theorems about PID's are in the `principal_ideal_ring` namespace.

- `IsPrincipalIdealRing`: a predicate on rings, saying that every left ideal is principal.
- `generator`: a generator of a principal ideal (or more generally submodule)
- `to_unique_factorization_monoid`: a PID is a unique factorization domain

# Main results

- `to_maximal_ideal`: a non-zero prime ideal in a PID is maximal.
- `EuclideanDomain.to_principal_ideal_domain` : a Euclidean domain is a PID.

-/


universe u v

variable {R : Type u} {M : Type v}

open Set Function

open Submodule

open Classical

section

variable [Ring R] [AddCommGroup M] [Module R M]

-- Porting note: renamed field to `principal'` and added `principal` to fix explicit argument
/-- An `R`-submodule of `M` is principal if it is generated by one element. -/
@[mk_iff]
class Submodule.IsPrincipal (S : Submodule R M) : Prop where
  principal' : ∃ a, S = span R {a}
#align submodule.is_principal Submodule.IsPrincipal

theorem Submodule.IsPrincipal.principal (S : Submodule R M) [Submodule.IsPrincipal S] :
    ∃ a, S = span R {a} :=
  Submodule.IsPrincipal.principal'
#align submodule.is_principal.principal Submodule.IsPrincipal.principal

instance bot_isPrincipal : (⊥ : Submodule R M).IsPrincipal :=
  ⟨⟨0, by simp⟩⟩
#align bot_is_principal bot_isPrincipal

instance top_isPrincipal : (⊤ : Submodule R R).IsPrincipal :=
  ⟨⟨1, Ideal.span_singleton_one.symm⟩⟩
#align top_is_principal top_isPrincipal

variable (R)

/-- A ring is a principal ideal ring if all (left) ideals are principal. -/
@[mk_iff isPrincipalIdealRing_iff]
class IsPrincipalIdealRing (R : Type u) [Ring R] : Prop where
  principal : ∀ S : Ideal R, S.IsPrincipal
#align is_principal_ideal_ring IsPrincipalIdealRing

attribute [instance] IsPrincipalIdealRing.principal

instance (priority := 100) DivisionRing.isPrincipalIdealRing (K : Type u) [DivisionRing K] :
    IsPrincipalIdealRing K where
  principal S := by
    rcases Ideal.eq_bot_or_top S with (rfl | rfl)
    apply bot_isPrincipal
    apply top_isPrincipal
#align division_ring.is_principal_ideal_ring DivisionRing.isPrincipalIdealRing

end

namespace Submodule.IsPrincipal

variable [AddCommGroup M]

section Ring

variable [Ring R] [Module R M]

/-- `generator I`, if `I` is a principal submodule, is an `x ∈ M` such that `span R {x} = I` -/
noncomputable def generator (S : Submodule R M) [S.IsPrincipal] : M :=
  Classical.choose (principal S)
#align submodule.is_principal.generator Submodule.IsPrincipal.generator

theorem span_singleton_generator (S : Submodule R M) [S.IsPrincipal] : span R {generator S} = S :=
  Eq.symm (Classical.choose_spec (principal S))
#align submodule.is_principal.span_singleton_generator Submodule.IsPrincipal.span_singleton_generator

theorem _root_.Ideal.span_singleton_generator (I : Ideal R) [I.IsPrincipal] :
    Ideal.span ({generator I} : Set R) = I :=
  Eq.symm (Classical.choose_spec (principal I))
#align ideal.span_singleton_generator Ideal.span_singleton_generator

@[simp]
theorem generator_mem (S : Submodule R M) [S.IsPrincipal] : generator S ∈ S := by
  conv_rhs => rw [← span_singleton_generator S]
  exact subset_span (mem_singleton _)
#align submodule.is_principal.generator_mem Submodule.IsPrincipal.generator_mem

theorem mem_iff_eq_smul_generator (S : Submodule R M) [S.IsPrincipal] {x : M} :
    x ∈ S ↔ ∃ s : R, x = s • generator S := by
  simp_rw [@eq_comm _ x, ← mem_span_singleton, span_singleton_generator]
#align submodule.is_principal.mem_iff_eq_smul_generator Submodule.IsPrincipal.mem_iff_eq_smul_generator

theorem eq_bot_iff_generator_eq_zero (S : Submodule R M) [S.IsPrincipal] :
    S = ⊥ ↔ generator S = 0 := by rw [← @span_singleton_eq_bot R M, span_singleton_generator]
#align submodule.is_principal.eq_bot_iff_generator_eq_zero Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero

end Ring

section CommRing

variable [CommRing R] [Module R M]

theorem mem_iff_generator_dvd (S : Ideal R) [S.IsPrincipal] {x : R} : x ∈ S ↔ generator S ∣ x :=
  (mem_iff_eq_smul_generator S).trans (exists_congr fun a => by simp only [mul_comm, smul_eq_mul])
#align submodule.is_principal.mem_iff_generator_dvd Submodule.IsPrincipal.mem_iff_generator_dvd

theorem prime_generator_of_isPrime (S : Ideal R) [Submodule.IsPrincipal S] [is_prime : S.IsPrime]
    (ne_bot : S ≠ ⊥) : Prime (generator S) :=
  ⟨fun h => ne_bot ((eq_bot_iff_generator_eq_zero S).2 h), fun h =>
    is_prime.ne_top (S.eq_top_of_isUnit_mem (generator_mem S) h), fun _ _ => by
    simpa only [← mem_iff_generator_dvd S] using is_prime.2⟩
#align submodule.is_principal.prime_generator_of_is_prime Submodule.IsPrincipal.prime_generator_of_isPrime

-- Note that the converse may not hold if `ϕ` is not injective.
theorem generator_map_dvd_of_mem {N : Submodule R M} (ϕ : M →ₗ[R] R) [(N.map ϕ).IsPrincipal] {x : M}
    (hx : x ∈ N) : generator (N.map ϕ) ∣ ϕ x := by
  rw [← mem_iff_generator_dvd, Submodule.mem_map]
  exact ⟨x, hx, rfl⟩
#align submodule.is_principal.generator_map_dvd_of_mem Submodule.IsPrincipal.generator_map_dvd_of_mem

-- Note that the converse may not hold if `ϕ` is not injective.
theorem generator_submoduleImage_dvd_of_mem {N O : Submodule R M} (hNO : N ≤ O) (ϕ : O →ₗ[R] R)
    [(ϕ.submoduleImage N).IsPrincipal] {x : M} (hx : x ∈ N) :
    generator (ϕ.submoduleImage N) ∣ ϕ ⟨x, hNO hx⟩ := by
  rw [← mem_iff_generator_dvd, LinearMap.mem_submoduleImage_of_le hNO]
  exact ⟨x, hx, rfl⟩
#align submodule.is_principal.generator_submodule_image_dvd_of_mem Submodule.IsPrincipal.generator_submoduleImage_dvd_of_mem

end CommRing

end Submodule.IsPrincipal

namespace IsPrime

open Submodule.IsPrincipal Ideal

-- TODO -- for a non-ID one could perhaps prove that if p < q are prime then q maximal;
-- 0 isn't prime in a non-ID PIR but the Krull dimension is still <= 1.
-- The below result follows from this, but we could also use the below result to
-- prove this (quotient out by p).
theorem to_maximal_ideal [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] {S : Ideal R}
    [hpi : IsPrime S] (hS : S ≠ ⊥) : IsMaximal S :=
  isMaximal_iff.2
    ⟨(ne_top_iff_one S).1 hpi.1, by
      intro T x hST hxS hxT
      cases' (mem_iff_generator_dvd _).1 (hST <| generator_mem S) with z hz
      cases hpi.mem_or_mem (show generator T * z ∈ S from hz ▸ generator_mem S) with
      | inl h =>
        have hTS : T ≤ S
        rwa [← T.span_singleton_generator, Ideal.span_le, singleton_subset_iff]
        exact (hxS <| hTS hxT).elim
      | inr h =>
        cases' (mem_iff_generator_dvd _).1 h with y hy
        have : generator S ≠ 0 := mt (eq_bot_iff_generator_eq_zero _).2 hS
        rw [← mul_one (generator S), hy, mul_left_comm, mul_right_inj' this] at hz
        exact hz.symm ▸ T.mul_mem_right _ (generator_mem T)⟩
#align is_prime.to_maximal_ideal IsPrime.to_maximal_ideal

end IsPrime

section

open EuclideanDomain

variable [EuclideanDomain R]

theorem mod_mem_iff {S : Ideal R} {x y : R} (hy : y ∈ S) : x % y ∈ S ↔ x ∈ S :=
  ⟨fun hxy => div_add_mod x y ▸ S.add_mem (S.mul_mem_right _ hy) hxy, fun hx =>
    (mod_eq_sub_mul_div x y).symm ▸ S.sub_mem hx (S.mul_mem_right _ hy)⟩
#align mod_mem_iff mod_mem_iff

-- see Note [lower instance priority]
instance (priority := 100) EuclideanDomain.to_principal_ideal_domain : IsPrincipalIdealRing R where
  principal S :=
    ⟨if h : { x : R | x ∈ S ∧ x ≠ 0 }.Nonempty then
        have wf : WellFounded (EuclideanDomain.r : R → R → Prop) := EuclideanDomain.r_wellFounded
        have hmin : WellFounded.min wf { x : R | x ∈ S ∧ x ≠ 0 } h ∈ S ∧
            WellFounded.min wf { x : R | x ∈ S ∧ x ≠ 0 } h ≠ 0 :=
          WellFounded.min_mem wf { x : R | x ∈ S ∧ x ≠ 0 } h
        ⟨WellFounded.min wf { x : R | x ∈ S ∧ x ≠ 0 } h,
          Submodule.ext fun x => ⟨fun hx =>
            div_add_mod x (WellFounded.min wf { x : R | x ∈ S ∧ x ≠ 0 } h) ▸
              (Ideal.mem_span_singleton.2 <| dvd_add (dvd_mul_right _ _) <| by
                have : x % WellFounded.min wf { x : R | x ∈ S ∧ x ≠ 0 } h ∉
                    { x : R | x ∈ S ∧ x ≠ 0 } :=
                  fun h₁ => WellFounded.not_lt_min wf _ h h₁ (mod_lt x hmin.2)
                have : x % WellFounded.min wf { x : R | x ∈ S ∧ x ≠ 0 } h = 0 := by
                  simp only [not_and_or, Set.mem_setOf_eq, not_ne_iff] at this
                  exact this.neg_resolve_left <| (mod_mem_iff hmin.1).2 hx
                simp [*]),
              fun hx =>
                let ⟨y, hy⟩ := Ideal.mem_span_singleton.1 hx
                hy.symm ▸ S.mul_mem_right _ hmin.1⟩⟩
      else ⟨0, Submodule.ext fun a => by
            rw [← @Submodule.bot_coe R R _ _ _, span_eq, Submodule.mem_bot]
            exact ⟨fun haS => by_contra fun ha0 => h ⟨a, ⟨haS, ha0⟩⟩,
              fun h₁ => h₁.symm ▸ S.zero_mem⟩⟩⟩
#align euclidean_domain.to_principal_ideal_domain EuclideanDomain.to_principal_ideal_domain

end

theorem IsField.isPrincipalIdealRing {R : Type*} [CommRing R] (h : IsField R) :
    IsPrincipalIdealRing R :=
  @EuclideanDomain.to_principal_ideal_domain R (@Field.toEuclideanDomain R h.toField)
#align is_field.is_principal_ideal_ring IsField.isPrincipalIdealRing

namespace PrincipalIdealRing

open IsPrincipalIdealRing

-- see Note [lower instance priority]
instance (priority := 100) isNoetherianRing [Ring R] [IsPrincipalIdealRing R] :
    IsNoetherianRing R :=
  isNoetherianRing_iff.2
    ⟨fun s : Ideal R => by
      rcases (IsPrincipalIdealRing.principal s).principal with ⟨a, rfl⟩
      rw [← Finset.coe_singleton]
      exact ⟨{a}, SetLike.coe_injective rfl⟩⟩
#align principal_ideal_ring.is_noetherian_ring PrincipalIdealRing.isNoetherianRing

theorem isMaximal_of_irreducible [CommRing R] [IsPrincipalIdealRing R] {p : R}
    (hp : Irreducible p) : Ideal.IsMaximal (span R ({p} : Set R)) :=
  ⟨⟨mt Ideal.span_singleton_eq_top.1 hp.1, fun I hI => by
      rcases principal I with ⟨a, rfl⟩
      erw [Ideal.span_singleton_eq_top]
      rcases Ideal.span_singleton_le_span_singleton.1 (le_of_lt hI) with ⟨b, rfl⟩
      refine' (of_irreducible_mul hp).resolve_right (mt (fun hb => _) (not_le_of_lt hI))
      erw [Ideal.span_singleton_le_span_singleton, IsUnit.mul_right_dvd hb]⟩⟩
#align principal_ideal_ring.is_maximal_of_irreducible PrincipalIdealRing.isMaximal_of_irreducible

variable [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]

theorem irreducible_iff_prime {p : R} : Irreducible p ↔ Prime p :=
  ⟨fun hp => (Ideal.span_singleton_prime hp.ne_zero).1 <| (isMaximal_of_irreducible hp).isPrime,
    Prime.irreducible⟩
#align principal_ideal_ring.irreducible_iff_prime PrincipalIdealRing.irreducible_iff_prime

theorem associates_irreducible_iff_prime : ∀ {p : Associates R}, Irreducible p ↔ Prime p :=
  fun {p} => (Associates.irreducible_iff_prime_iff.1 fun _ => irreducible_iff_prime) p
#align principal_ideal_ring.associates_irreducible_iff_prime PrincipalIdealRing.associates_irreducible_iff_prime

section

open Classical

/-- `factors a` is a multiset of irreducible elements whose product is `a`, up to units -/
noncomputable def factors (a : R) : Multiset R :=
  if h : a = 0 then ∅ else Classical.choose (WfDvdMonoid.exists_factors a h)
#align principal_ideal_ring.factors PrincipalIdealRing.factors

theorem factors_spec (a : R) (h : a ≠ 0) :
    (∀ b ∈ factors a, Irreducible b) ∧ Associated (factors a).prod a := by
  unfold factors; rw [dif_neg h]
  exact Classical.choose_spec (WfDvdMonoid.exists_factors a h)
#align principal_ideal_ring.factors_spec PrincipalIdealRing.factors_spec

theorem ne_zero_of_mem_factors {R : Type v} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {a b : R} (ha : a ≠ 0) (hb : b ∈ factors a) : b ≠ 0 :=
  Irreducible.ne_zero ((factors_spec a ha).1 b hb)
#align principal_ideal_ring.ne_zero_of_mem_factors PrincipalIdealRing.ne_zero_of_mem_factors

theorem mem_submonoid_of_factors_subset_of_units_subset (s : Submonoid R) {a : R} (ha : a ≠ 0)
    (hfac : ∀ b ∈ factors a, b ∈ s) (hunit : ∀ c : Rˣ, (c : R) ∈ s) : a ∈ s := by
  rcases (factors_spec a ha).2 with ⟨c, hc⟩
  rw [← hc]
  exact mul_mem (multiset_prod_mem _ hfac) (hunit _)
#align principal_ideal_ring.mem_submonoid_of_factors_subset_of_units_subset PrincipalIdealRing.mem_submonoid_of_factors_subset_of_units_subset

/-- If a `RingHom` maps all units and all factors of an element `a` into a submonoid `s`, then it
also maps `a` into that submonoid. -/
theorem ringHom_mem_submonoid_of_factors_subset_of_units_subset {R S : Type*} [CommRing R]
    [IsDomain R] [IsPrincipalIdealRing R] [Semiring S] (f : R →+* S) (s : Submonoid S) (a : R)
    (ha : a ≠ 0) (h : ∀ b ∈ factors a, f b ∈ s) (hf : ∀ c : Rˣ, f c ∈ s) : f a ∈ s :=
  mem_submonoid_of_factors_subset_of_units_subset (s.comap f.toMonoidHom) ha h hf
#align principal_ideal_ring.ring_hom_mem_submonoid_of_factors_subset_of_units_subset PrincipalIdealRing.ringHom_mem_submonoid_of_factors_subset_of_units_subset

-- see Note [lower instance priority]
/-- A principal ideal domain has unique factorization -/
instance (priority := 100) to_uniqueFactorizationMonoid : UniqueFactorizationMonoid R :=
  { (IsNoetherianRing.wfDvdMonoid : WfDvdMonoid R) with
    irreducible_iff_prime := PrincipalIdealRing.irreducible_iff_prime }
#align principal_ideal_ring.to_unique_factorization_monoid PrincipalIdealRing.to_uniqueFactorizationMonoid

end

end PrincipalIdealRing

section Surjective

open Submodule

variable {S N : Type*} [Ring R] [AddCommGroup M] [AddCommGroup N] [Ring S]

variable [Module R M] [Module R N]

theorem Submodule.IsPrincipal.of_comap (f : M →ₗ[R] N) (hf : Function.Surjective f)
    (S : Submodule R N) [hI : IsPrincipal (S.comap f)] : IsPrincipal S :=
  ⟨⟨f (IsPrincipal.generator (S.comap f)), by
      rw [← Set.image_singleton, ← Submodule.map_span, IsPrincipal.span_singleton_generator,
        Submodule.map_comap_eq_of_surjective hf]⟩⟩
#align submodule.is_principal.of_comap Submodule.IsPrincipal.of_comap

theorem Ideal.IsPrincipal.of_comap (f : R →+* S) (hf : Function.Surjective f) (I : Ideal S)
    [hI : IsPrincipal (I.comap f)] : IsPrincipal I :=
  ⟨⟨f (IsPrincipal.generator (I.comap f)), by
      rw [Ideal.submodule_span_eq, ← Set.image_singleton, ← Ideal.map_span,
        Ideal.span_singleton_generator, Ideal.map_comap_of_surjective f hf]⟩⟩
#align ideal.is_principal.of_comap Ideal.IsPrincipal.of_comap

/-- The surjective image of a principal ideal ring is again a principal ideal ring. -/
theorem IsPrincipalIdealRing.of_surjective [IsPrincipalIdealRing R] (f : R →+* S)
    (hf : Function.Surjective f) : IsPrincipalIdealRing S :=
  ⟨fun I => Ideal.IsPrincipal.of_comap f hf I⟩
#align is_principal_ideal_ring.of_surjective IsPrincipalIdealRing.of_surjective

end Surjective

section

open Ideal

variable [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [GCDMonoid R]

theorem span_gcd (x y : R) : span ({gcd x y} : Set R) = span ({x, y} : Set R) := by
  obtain ⟨d, hd⟩ := IsPrincipalIdealRing.principal (span ({x, y} : Set R))
  rw [submodule_span_eq] at hd
  rw [hd]
  suffices Associated d (gcd x y) by
    obtain ⟨D, HD⟩ := this
    rw [← HD]
    exact span_singleton_mul_right_unit D.isUnit _
  apply associated_of_dvd_dvd
  · rw [dvd_gcd_iff]
    constructor <;> rw [← Ideal.mem_span_singleton, ← hd, Ideal.mem_span_pair]
    · use 1, 0
      rw [one_mul, zero_mul, add_zero]
    · use 0, 1
      rw [one_mul, zero_mul, zero_add]
  · obtain ⟨r, s, rfl⟩ : ∃ r s, r * x + s * y = d := by
      rw [← Ideal.mem_span_pair, hd, Ideal.mem_span_singleton]
    apply dvd_add <;> apply dvd_mul_of_dvd_right
    exacts [gcd_dvd_left x y, gcd_dvd_right x y]
#align span_gcd span_gcd

theorem gcd_dvd_iff_exists (a b : R) {z} : gcd a b ∣ z ↔ ∃ x y, z = a * x + b * y := by
  simp_rw [mul_comm a, mul_comm b, @eq_comm _ z, ← Ideal.mem_span_pair, ← span_gcd,
    Ideal.mem_span_singleton]
#align gcd_dvd_iff_exists gcd_dvd_iff_exists

/-- **Bézout's lemma** -/
theorem exists_gcd_eq_mul_add_mul (a b : R) : ∃ x y, gcd a b = a * x + b * y := by
  rw [← gcd_dvd_iff_exists]
#align exists_gcd_eq_mul_add_mul exists_gcd_eq_mul_add_mul

theorem gcd_isUnit_iff (x y : R) : IsUnit (gcd x y) ↔ IsCoprime x y := by
  rw [IsCoprime, ← Ideal.mem_span_pair, ← span_gcd, ← span_singleton_eq_top, eq_top_iff_one]
#align gcd_is_unit_iff gcd_isUnit_iff

-- this should be proved for UFDs surely?
theorem isCoprime_of_dvd (x y : R) (nonzero : ¬(x = 0 ∧ y = 0))
    (H : ∀ z ∈ nonunits R, z ≠ 0 → z ∣ x → ¬z ∣ y) : IsCoprime x y := by
  rw [← gcd_isUnit_iff]
  by_contra h
  refine' H _ h _ (gcd_dvd_left _ _) (gcd_dvd_right _ _)
  rwa [Ne, gcd_eq_zero_iff]
#align is_coprime_of_dvd isCoprime_of_dvd

-- this should be proved for UFDs surely?
theorem dvd_or_coprime (x y : R) (h : Irreducible x) : x ∣ y ∨ IsCoprime x y := by
  refine' or_iff_not_imp_left.2 fun h' => _
  apply isCoprime_of_dvd
  · rintro ⟨rfl, rfl⟩
    simp at h
  · rintro z nu - ⟨w, rfl⟩ dy
    refine' h' (dvd_trans _ dy)
    simpa using mul_dvd_mul_left z (isUnit_iff_dvd_one.1 <| (of_irreducible_mul h).resolve_left nu)
#align dvd_or_coprime dvd_or_coprime

theorem isCoprime_of_irreducible_dvd {x y : R} (nonzero : ¬(x = 0 ∧ y = 0))
    (H : ∀ z : R, Irreducible z → z ∣ x → ¬z ∣ y) : IsCoprime x y := by
  apply isCoprime_of_dvd x y nonzero
  intro z znu znz zx zy
  obtain ⟨i, h1, h2⟩ := WfDvdMonoid.exists_irreducible_factor znu znz
  apply H i h1 <;>
    · apply dvd_trans h2
      assumption
#align is_coprime_of_irreducible_dvd isCoprime_of_irreducible_dvd

theorem isCoprime_of_prime_dvd {x y : R} (nonzero : ¬(x = 0 ∧ y = 0))
    (H : ∀ z : R, Prime z → z ∣ x → ¬z ∣ y) : IsCoprime x y :=
  isCoprime_of_irreducible_dvd nonzero fun z zi => H z <| GCDMonoid.prime_of_irreducible zi
#align is_coprime_of_prime_dvd isCoprime_of_prime_dvd

theorem Irreducible.coprime_iff_not_dvd {p n : R} (pp : Irreducible p) :
    IsCoprime p n ↔ ¬p ∣ n := by
  constructor
  · intro co H
    apply pp.not_unit
    rw [isUnit_iff_dvd_one]
    apply IsCoprime.dvd_of_dvd_mul_left co
    rw [mul_one n]
    exact H
  · intro nd
    apply isCoprime_of_irreducible_dvd
    · rintro ⟨hp, -⟩
      exact pp.ne_zero hp
    rintro z zi zp zn
    exact nd ((zi.associated_of_dvd pp zp).symm.dvd.trans zn)
#align irreducible.coprime_iff_not_dvd Irreducible.coprime_iff_not_dvd

theorem Prime.coprime_iff_not_dvd {p n : R} (pp : Prime p) : IsCoprime p n ↔ ¬p ∣ n :=
  pp.irreducible.coprime_iff_not_dvd
#align prime.coprime_iff_not_dvd Prime.coprime_iff_not_dvd

theorem Irreducible.dvd_iff_not_coprime {p n : R} (hp : Irreducible p) : p ∣ n ↔ ¬IsCoprime p n :=
  iff_not_comm.2 hp.coprime_iff_not_dvd
#align irreducible.dvd_iff_not_coprime Irreducible.dvd_iff_not_coprime

theorem Irreducible.coprime_pow_of_not_dvd {p a : R} (m : ℕ) (hp : Irreducible p) (h : ¬p ∣ a) :
    IsCoprime a (p ^ m) :=
  (hp.coprime_iff_not_dvd.2 h).symm.pow_right
#align irreducible.coprime_pow_of_not_dvd Irreducible.coprime_pow_of_not_dvd

theorem Irreducible.coprime_or_dvd {p : R} (hp : Irreducible p) (i : R) : IsCoprime p i ∨ p ∣ i :=
  (_root_.em _).imp_right hp.dvd_iff_not_coprime.2
#align irreducible.coprime_or_dvd Irreducible.coprime_or_dvd

theorem exists_associated_pow_of_mul_eq_pow' {a b c : R} (hab : IsCoprime a b) {k : ℕ}
    (h : a * b = c ^ k) : ∃ d : R, Associated (d ^ k) a :=
  exists_associated_pow_of_mul_eq_pow ((gcd_isUnit_iff _ _).mpr hab) h
#align exists_associated_pow_of_mul_eq_pow' exists_associated_pow_of_mul_eq_pow'

end

section PrincipalOfPrime

open Set Ideal

variable (R) [CommRing R]

/-- `nonPrincipals R` is the set of all ideals of `R` that are not principal ideals. -/
def nonPrincipals :=
  { I : Ideal R | ¬I.IsPrincipal }
#align non_principals nonPrincipals

theorem nonPrincipals_def {I : Ideal R} : I ∈ nonPrincipals R ↔ ¬I.IsPrincipal :=
  Iff.rfl
#align non_principals_def nonPrincipals_def

variable {R}

theorem nonPrincipals_eq_empty_iff : nonPrincipals R = ∅ ↔ IsPrincipalIdealRing R := by
  simp [Set.eq_empty_iff_forall_not_mem, isPrincipalIdealRing_iff, nonPrincipals_def]
#align non_principals_eq_empty_iff nonPrincipals_eq_empty_iff

/-- Any chain in the set of non-principal ideals has an upper bound which is non-principal.
(Namely, the union of the chain is such an upper bound.)
-/
theorem nonPrincipals_zorn (c : Set (Ideal R)) (hs : c ⊆ nonPrincipals R)
    (hchain : IsChain (· ≤ ·) c) {K : Ideal R} (hKmem : K ∈ c) :
    ∃ I ∈ nonPrincipals R, ∀ J ∈ c, J ≤ I := by
  refine' ⟨sSup c, _, fun J hJ => le_sSup hJ⟩
  rintro ⟨x, hx⟩
  have hxmem : x ∈ sSup c := hx.symm ▸ Submodule.mem_span_singleton_self x
  obtain ⟨J, hJc, hxJ⟩ := (Submodule.mem_sSup_of_directed ⟨K, hKmem⟩ hchain.directedOn).1 hxmem
  have hsSupJ : sSup c = J := le_antisymm (by simp [hx, Ideal.span_le, hxJ]) (le_sSup hJc)
  specialize hs hJc
  rw [← hsSupJ, hx, nonPrincipals_def] at hs
  exact hs ⟨⟨x, rfl⟩⟩
#align non_principals_zorn nonPrincipals_zorn

/-- If all prime ideals in a commutative ring are principal, so are all other ideals. -/
theorem IsPrincipalIdealRing.of_prime (H : ∀ P : Ideal R, P.IsPrime → P.IsPrincipal) :
    IsPrincipalIdealRing R := by
  -- Suppose the set of `nonPrincipals` is not empty.
  rw [← nonPrincipals_eq_empty_iff, Set.eq_empty_iff_forall_not_mem]
  intro J hJ
  -- We will show a maximal element `I ∈ nonPrincipals R` (which exists by Zorn) is prime.
  obtain ⟨I, Ibad, -, Imax⟩ := zorn_nonempty_partialOrder₀ (nonPrincipals R) nonPrincipals_zorn _ hJ
  have Imax' : ∀ {J}, I < J → J.IsPrincipal := by
    intro J hJ
    by_contra He
    exact hJ.ne (Imax _ ((nonPrincipals_def R).2 He) hJ.le).symm
  by_cases hI1 : I = ⊤
  · subst hI1
    exact Ibad top_isPrincipal
  -- Let `x y : R` with `x * y ∈ I` and suppose WLOG `y ∉ I`.
  refine' Ibad (H I ⟨hI1, fun {x y} hxy => or_iff_not_imp_right.mpr fun hy => _⟩)
  obtain ⟨a, ha⟩ : (I ⊔ span {y}).IsPrincipal :=
    Imax' (left_lt_sup.mpr (mt I.span_singleton_le_iff_mem.mp hy))
  -- Then `x ∈ I.colon (span {y})`, which is equal to `I` if it's not principal.
  suffices He : ¬(I.colon (span {y})).IsPrincipal
  · rw [← Imax _ ((nonPrincipals_def R).2 He) fun a ha =>
        Ideal.mem_colon_singleton.2 (mul_mem_right _ _ ha)]
    exact Ideal.mem_colon_singleton.2 hxy
  -- So suppose for the sake of contradiction that both `I ⊔ span {y}` and `I.colon (span {y})`
  -- are principal.
  rintro ⟨b, hb⟩
  -- We will show `I` is generated by `a * b`.
  refine (nonPrincipals_def _).1 Ibad ⟨a * b, ?_⟩
  refine'
    le_antisymm (α := Ideal R) (fun i hi => _) <| (span_singleton_mul_span_singleton a b).ge.trans _
  · have hisup : i ∈ I ⊔ span {y} := Ideal.mem_sup_left hi
    have : y ∈ I ⊔ span {y} := Ideal.mem_sup_right (Ideal.mem_span_singleton_self y)
    erw [ha, mem_span_singleton'] at hisup this
    obtain ⟨v, rfl⟩ := this
    obtain ⟨u, rfl⟩ := hisup
    have hucolon : u ∈ I.colon (span {v * a}) := by
      rw [Ideal.mem_colon_singleton, mul_comm v, ← mul_assoc]
      exact mul_mem_right _ _ hi
    erw [hb, mem_span_singleton'] at hucolon
    obtain ⟨z, rfl⟩ := hucolon
    exact mem_span_singleton'.2 ⟨z, by ring⟩
  · rw [← Ideal.submodule_span_eq, ← ha, Ideal.sup_mul, sup_le_iff,
      span_singleton_mul_span_singleton, mul_comm y, Ideal.span_singleton_le_iff_mem]
    exact ⟨mul_le_right, Ideal.mem_colon_singleton.1 <| hb.symm ▸ Ideal.mem_span_singleton_self b⟩
#align is_principal_ideal_ring.of_prime IsPrincipalIdealRing.of_prime

end PrincipalOfPrime
