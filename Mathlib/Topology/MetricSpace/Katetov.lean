/-
Copyright (c) 2024 Luigi Massacci. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luigi Massacci
-/

import Mathlib.Algebra.Order.Pointwise
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.Algebra.Order.AbsoluteValue
import Mathlib.Init.Algebra.Classes
import Mathlib.Analysis.Complex.Basic
/-!
# Katetov Maps

In this file we define Katetov maps (i.e. one point extensions of a metric) and establish
basic properties of their space. We embed a metric space in its space of Katetov maps via
the Kuratowski embedding.

## Notation

 - `E(X)` is the type of Katetov maps on `X`.

## References

* [melleray_urysohn_2008]
-/

variable {α : Type _} [MetricSpace α]

/-- A real valued function from a metric space is katetov if
  it satisfies the following inequalities: -/
@[mk_iff]
structure IsKatetov (f : α → ℝ) : Prop where
  /-- Proposition that `f` is 1-Lipschitz -/
  abs_sub_le_dist : ∀ x y, |f x - f y| ≤ dist x y
  /-- Second defining inequality of a Katetov map  -/
  dist_le_add : ∀ x y, dist x y ≤ f x + f y

/-- The type of Katetov maps from `α` -/
structure KatetovMap (α : Type*) [MetricSpace α] where
  /-- The function `α → ℝ` -/
  protected toFun : α → ℝ
  /-- Proposition that `toFun` is a Katetov map -/
  protected IsKatetovtoFun : IsKatetov toFun

/-- The type of Katetov maps from `α`. -/
notation "E(" α ")" => KatetovMap α

section


/-- `KatetovMapClass F α` states that `F` is a type of Katetov maps. -/
class KatetovMapClass (F : Type*) (α : Type*) [MetricSpace α] [FunLike F α  ℝ] : Prop where
  map_katetov (f : F) : IsKatetov f

end

export KatetovMapClass (map_katetov)

section KatetovMapClass

variable {F α : Type*} [MetricSpace α] [FunLike F α  ℝ]
variable [KatetovMapClass F α]

/-- Coerce a bundled morphism with a `KatetovMapClass` instance to a `KatetovMap`. -/
@[coe] def toKatetovMap (f : F) : E(α) := ⟨f, map_katetov f⟩

instance : CoeTC F E(α) := ⟨toKatetovMap⟩

end KatetovMapClass

namespace KatetovMap

variable {α : Type*} [MetricSpace α]

instance funLike : FunLike E(α) α ℝ where
  coe := KatetovMap.toFun
  coe_injective' f g h := by cases f; cases g; congr

instance toKatetovMapClass : KatetovMapClass E(α) α where
  map_katetov := KatetovMap.IsKatetovtoFun

@[simp]
theorem toFun_eq_coe {f : E(α)} : f.toFun = (f : α → ℝ) := rfl

instance : CanLift (α → ℝ) E(α) DFunLike.coe IsKatetov := ⟨fun f hf ↦ ⟨⟨f, hf⟩, rfl⟩⟩

/-- See Topology/ContinuousFunction.Basic -/
def Simps.apply (f : E(α)) : α → ℝ := f

initialize_simps_projections KatetovMap (toFun → apply)

@[simp]
protected theorem coe_coe {F : Type*} [FunLike F α ℝ] [KatetovMapClass F α] (f : F) :
    ⇑(f : E(α)) = f := rfl

@[ext]
theorem ext {f g : E(α)} (h : ∀ a, f a = g a) : f = g := DFunLike.ext _ _ h

/-- Copy of a `KatetovMap` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. See Topology/ContinuousFunction.Basic -/
protected def copy (f : E(α)) (f' : α → ℝ) (h : f' = f) : E(α) where
  toFun := f'
  IsKatetovtoFun := h.symm ▸ f.IsKatetovtoFun

@[simp]
theorem coe_copy (f : E(α)) (f' : α → ℝ) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : E(α)) (f' : α → ℝ) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable {f g : E(α)}

theorem katetov_set_coe (s : Set E(α)) (f : s) : IsKatetov (f : α → ℝ) :=
  f.1.IsKatetovtoFun

theorem coe_injective : @Function.Injective E(α) (α → ℝ) (↑) :=
  fun f g h ↦ by cases f; cases g; congr

@[simp]
theorem coe_mk (f : α → ℝ) (h : IsKatetov f) : ⇑(⟨f, h⟩ : E(α)) = f :=
  rfl

end KatetovMap

lemma abs_sub_dist_le (x₀ : α) (f : E(α)) (x : α) : |f x - dist x x₀| ≤ f x₀ := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · linarith [(map_katetov f).dist_le_add x x₀]
  · linarith [le_of_abs_le <| (map_katetov f).abs_sub_le_dist x x₀]

theorem bounded_dist_set {f g : E(α)} : BddAbove {|f x - g x| | x : α} := by
  by_cases hn : Nonempty α
  · have x₀ := Classical.choice ‹Nonempty α›
    refine ⟨f x₀ + g x₀, fun _ ⟨x, hx⟩ ↦ ?_⟩; rw [← hx]
    have h : |f x - g x| ≤ |f x - dist x x₀| + |g x - dist x x₀|:= by
      rw [← abs_sub_comm (dist x x₀) (g x)]; apply abs_sub_le (f x) (dist x x₀) (g x)
    apply le_trans h <| add_le_add (abs_sub_dist_le x₀ f x) (abs_sub_dist_le x₀ g x)
  · refine ⟨0, fun _ ⟨x, _⟩ ↦ False.elim (hn ⟨x⟩)⟩

lemma eq_zero_of_sSup_eq_zero (s : Set ℝ) (hb : BddAbove s) (snonneg : ∀ x ∈ s, 0 ≤ x)
    (hsup : sSup s = 0) : ∀ x ∈ s, x = 0 := by
  refine (fun x xs ↦ le_antisymm (by rw [← hsup]; exact le_csSup hb xs) (snonneg x xs))

theorem katetov_nonneg (f : E(α)) (x : α) : 0 ≤ f x := by
  have : 0 ≤ f x + f x := by rw [← dist_self x]; exact (map_katetov f).dist_le_add x x
  apply nonneg_add_self_iff.mp this

theorem empty_sSup_of_empty (h : IsEmpty α) (f g : E(α)) :
    ¬Set.Nonempty {|f x - g x| | x : α} := by
  by_contra hc
  obtain ⟨_, x, _⟩ := hc
  exact IsEmpty.false x

noncomputable instance: MetricSpace E(α) where
  dist f g := sSup {|f x - g x| | x : α}
  dist_self f := by
    by_cases h : Nonempty α
    · simp [dist]
    · simp [dist, sSup]
      have hf := empty_sSup_of_empty (not_nonempty_iff.mp h) f f
      simp only [sub_self, abs_zero] at hf
      simp_all only [false_and, dite_false, IsEmpty.forall_iff]
  dist_comm f g := by simp [dist, abs_sub_comm]
  dist_triangle f g h := by
    by_cases hc : Nonempty α
    · simp [dist]
      apply Real.sSup_le
      · rintro val ⟨x, rfl⟩
        rw [← csSup_add]
        · apply le_trans <| abs_sub_le (f x) (g x) (h x)
          apply le_csSup (by apply BddAbove.add <;> apply bounded_dist_set)
          refine Set.mem_add.mpr ⟨|f x - g x|, (by simp), (by simp)⟩
        · have x₀ := Classical.choice ‹Nonempty α›
          use |f x₀ - g x₀|; simp
        · apply bounded_dist_set
        · have x₀ := Classical.choice ‹Nonempty α›
          use |g x₀ - h x₀|; simp
        · apply bounded_dist_set
      · apply add_nonneg <;>
        { apply Real.sSup_nonneg; rintro val ⟨x, rfl⟩; apply abs_nonneg}
    · simp [dist, sSup]
      have hfh := empty_sSup_of_empty (not_nonempty_iff.mp hc) f h
      have hfg := empty_sSup_of_empty (not_nonempty_iff.mp hc) f g
      have hgh:= empty_sSup_of_empty (not_nonempty_iff.mp hc) g h
      simp_all only [false_and, dite_false]
      simp only [add_zero, le_refl]
  eq_of_dist_eq_zero := by
    intro f g h
    simp [dist] at h
    apply eq_zero_of_sSup_eq_zero at h
    · ext x; exact eq_of_sub_eq_zero <| abs_eq_zero.mp (h |f x - g x| ⟨x, rfl⟩)
    · apply bounded_dist_set
    · rintro _ ⟨x, rfl⟩; exact abs_nonneg _
  edist_dist x y:= by exact ENNReal.coe_nnreal_eq _

#check Complex.mk

theorem dist_coe_le_dist (f g : E(α)) (x : α) : dist (f x) (g x) ≤ dist f g :=
  by refine le_csSup bounded_dist_set (by simp [dist])

theorem dist_le {C :ℝ} (C0 : (0 : ℝ) ≤ C) (f g : E(α)):
    dist f g ≤ C ↔ ∀ x : α, dist (f x) (g x) ≤ C := by
  refine ⟨fun h x => le_trans (dist_coe_le_dist _ _ x) h, fun H ↦ ?_⟩
  simp [dist]; apply Real.sSup_le (by simp [*] at *; assumption) (C0)


noncomputable instance : CompleteSpace E(α) :=
  Metric.complete_of_cauchySeq_tendsto fun (u : ℕ → E(α)) (hf : CauchySeq u) => by
    rcases cauchySeq_iff_le_tendsto_0.1 hf with ⟨b, b0, b_bound, b_lim⟩
    have u_bdd := fun x n m N hn hm => le_trans (dist_coe_le_dist _ _ x) (b_bound n m N hn hm)
    have ux_cau : ∀ x, CauchySeq fun n => u n x :=
      fun x => cauchySeq_iff_le_tendsto_0.2 ⟨b, b0, u_bdd x, b_lim⟩
    choose f hf using fun x => cauchySeq_tendsto_of_complete (ux_cau x)
    have fF_bdd : ∀ x N, dist (u N x) (f x) ≤ b N :=
      fun x N => le_of_tendsto (tendsto_const_nhds.dist (hf x))
        (Filter.eventually_atTop.2 ⟨N, fun n hn => u_bdd x N n N (le_refl N) hn⟩)
    have kat_f : IsKatetov f := by
      have h : ∀ x y,∀ ε > 0, |f x - f y| ≤ 2*ε + dist x y ∧ dist x y ≤ f x + f y + 2*ε:= by
        intro x y ε εpos
        rcases Metric.tendsto_atTop.mp (hf x) ε εpos with ⟨Nx, hNx⟩
        rcases Metric.tendsto_atTop.mp (hf y) ε εpos with ⟨Ny, hNy⟩
        simp [dist] at *
        set N := max Nx Ny
        specialize hNx N (le_max_left _ _)
        specialize hNy N (le_max_right _ _)
        constructor
        · calc
          _ = _ := by rw [← add_zero (f x), (show 0 = u N x - u N x + u N y - u N y by ring)]
          _ = |(f x - (u N) x) + ((u N) y - f y) + ((u N x) - (u N y))|     := by ring_nf
          _ ≤ |(f x - (u N) x)| + |((u N) y - f y)| + |((u N x) - (u N y))| := by
              repeat apply (abs_add ..).trans; gcongr; try exact abs_add _ _
          _ ≤ 2*ε + dist x y := by
              rw [abs_sub_comm (f x)]
              linarith [(map_katetov (u N)).abs_sub_le_dist x y]
        · calc
          _ ≤ u N x + u N y := (map_katetov (u N)).dist_le_add x y
          _ = _ := by rw [← add_zero (u N y), show 0 = f x - f x + f y - f y by ring]
          _ = f x + f y + (u N x - f x) + (u N y - f y) := by ring
          _ ≤ _ := by linarith [le_of_lt (lt_of_abs_lt hNx), le_of_lt (lt_of_abs_lt hNy)]
      constructor <;>
        { refine fun x y ↦ le_of_forall_pos_le_add (fun ε εpos ↦ ?_)
          linarith [h x y (ε/2) (half_pos εpos)]}
    · use ⟨f, kat_f⟩
      refine' tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) _ b_lim)
      refine (fun N ↦ (dist_le (b0 N) (u N) ⟨f, kat_f⟩).mpr (fun x => fF_bdd x N))

namespace KatetovKuratowskiEmbedding

/-- The Katetov map from an empty type -/
def instKatetovMapOfEmpty (α : Type*) [MetricSpace α] [IsEmpty α] : E(α) := by
  refine ⟨fun x ↦ (IsEmpty.false x).elim, ?_⟩
  constructor <;> {intro x; exact (IsEmpty.false x).elim}

theorem empty_unique [IsEmpty α] (f g : E(α)) : f = g := by
  ext x; exact (IsEmpty.false x).elim


theorem exists_isometric_embedding (α : Type*) [MetricSpace α] : ∃ f : α → E(α), Isometry f := by
    by_cases h : Nonempty α
    · refine ⟨fun x : α ↦ ⟨fun y ↦ dist x y, ?_⟩, ?_⟩
      · constructor <;> (intro y z; rw [dist_comm x y])
        · rw [dist_comm x z]; exact abs_dist_sub_le y z x
        · exact dist_triangle y x z
      · refine Isometry.of_dist_eq (fun x y ↦ le_antisymm ?_ ?_)
        · refine Real.sSup_le ?_ dist_nonneg
          · simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff]
            refine fun z ↦ abs_dist_sub_le x y z
        · refine (Real.le_sSup_iff bounded_dist_set ?_).mpr  ?_
          · have x₀ := Classical.choice ‹Nonempty α›
            use |dist x x₀ - dist y x₀|; simp
          · simp only [KatetovMap.coe_mk, Set.mem_setOf_eq, exists_exists_eq_and]
            refine fun ε εpos ↦ ⟨x, ?_⟩
            rw [dist_self, zero_sub, abs_neg, dist_comm, abs_of_nonneg (dist_nonneg)]
            exact add_lt_of_neg_right (dist y x) εpos
    · refine ⟨fun _ ↦ @instKatetovMapOfEmpty _ _ (not_nonempty_iff.mp h), fun x ↦ ?_⟩
      exact ((not_nonempty_iff.mp h).false x).elim

end KatetovKuratowskiEmbedding

open KatetovKuratowskiEmbedding

/-- The Katetov-Kuratowski embedding is an isometric embedding of a metric space into its space
  of Katetov maps.-/
noncomputable def katetovKuratowskiEmbedding (α : Type*) [MetricSpace α] : α ↪ E(α) := by
  choose f h using exists_isometric_embedding α; refine ⟨f, h.injective⟩

protected theorem katetovKuratowskiEmbedding.isometry (α : Type*) [MetricSpace α] :
    Isometry (katetovKuratowskiEmbedding α) :=
    Classical.choose_spec <| exists_isometric_embedding α


namespace KatetovExtension

open Pointwise

lemma abs_inf_dist_le_sup {α : Type*} {f g : α → ℝ} (hα : Nonempty α)
 (fpos : ∀ x, 0 ≤ f x) (gpos : ∀ x, 0 ≤ g x) (hb : BddAbove (Set.range |f - g|)):
    |sInf {f x | x} - sInf {g x | x}| ≤ sSup {|f x - g x| | x} := by
    refine abs_le.mpr ⟨?_, ?_⟩
    · have : sInf {g x | x} - sSup {|f x - g x| | x} ≤ sInf {f x | x} := by
        rw [← csInf_sub _ _ _ (by exact hb)]
        · apply le_csInf
          · have z₀ := Classical.choice hα
            refine ⟨f z₀, by simp⟩
          · rintro _ ⟨x, rfl⟩
            refine @csInf_le_of_le _ _ ({x | ∃ x_1, g x_1 = x} - {x | ∃ x_1, |f x_1 - g x_1| = x})
              (f x) (g x - |f x - g x|) ?_ ?_ ?_
            · simp_rw [sub_eq_add_neg]
              apply BddBelow.add ?_ (BddAbove.neg hb)
              · refine ⟨0, ?_⟩;rintro _ ⟨x, rfl⟩; apply gpos
            · apply Set.mem_sub.mpr
              refine ⟨g x, (by simp), |f x - g x|, by simp, by ring⟩
            · nth_rewrite 1 [← abs_of_nonneg (gpos x), abs_sub_comm _ _]
              calc
              _ ≤ |g x - (g x - f x)| := by exact abs_sub_abs_le_abs_sub (g x) _
              _ = f x := by ring_nf; rw [abs_of_nonneg (fpos x)]
        · have z₀ := Classical.choice hα
          refine ⟨g z₀, by simp⟩
        · refine ⟨0, ?_⟩; rintro _ ⟨x, rfl⟩; apply gpos
        · have z₀ := Classical.choice hα
          refine ⟨|f z₀ - g z₀|, by simp⟩
      linarith [this]
    · have : sInf {f x | x} - sSup {|f x - g x| | x} ≤ sInf {g x | x} := by
        rw [← csInf_sub _ _ _ (by exact hb)]
        · apply le_csInf
          · have z₀ := Classical.choice hα
            refine ⟨g z₀, by simp⟩
          · rintro _ ⟨x, rfl⟩
            refine @csInf_le_of_le _ _ ({x | ∃ x_1, f x_1 = x} - {x | ∃ x_1, |f x_1 - g x_1| = x})
              (g x) (f x - |f x - g x|) ?_ ?_ ?_
            · simp_rw [sub_eq_add_neg]
              apply BddBelow.add ?_ (BddAbove.neg hb)
              · refine ⟨0, ?_⟩; rintro _ ⟨x, rfl⟩; apply fpos
            · apply Set.mem_sub.mpr ⟨f x, (by simp), |f x - g x|, by simp, by ring⟩
            · nth_rewrite 1 [← abs_of_nonneg (fpos x)]
              calc
              _ ≤ |f x - (f x - g x)| := by exact abs_sub_abs_le_abs_sub (f x) _
              _ = g x := by ring_nf; rw [abs_of_nonneg (gpos x)]
        · have z₀ := Classical.choice hα
          refine ⟨f z₀, by simp⟩
        · refine ⟨0, ?_⟩; rintro _ ⟨x, rfl⟩; apply fpos
        · have z₀ := Classical.choice hα
          refine ⟨|f z₀ - g z₀|, by simp⟩
      linarith [this]

-- if s empty return dist?
noncomputable def katetovExtension {α : Type*} (s : Set α) [MetricSpace α]
    (f : E(s)) : E(α) := by
  by_cases hs : Nonempty s
  · refine ⟨fun x ↦ sInf {(f z) + dist x z | z : s }, ?_⟩
    constructor <;> intro x y
    · --rw [sub_eq_add_neg, ← csSup_neg]
      calc
      _ ≤ sSup {|f z + dist x z - (f z + dist y z)| | z : s} := by
        refine abs_inf_dist_le_sup hs ?_ ?_ ?_
        · refine fun x ↦ add_nonneg (katetov_nonneg f x) (dist_nonneg)
        · refine fun x ↦ add_nonneg (katetov_nonneg f x) (dist_nonneg)
        · use dist x y
          rintro _ ⟨z, rfl⟩
          have : |(fun z ↦ f z + dist x z) - fun z ↦ f z + dist y z| z
            = |(f z + dist x z) - (f z + dist y z)| := by rfl
          rw [this]
          ring_nf
          apply abs_dist_sub_le
      _ = sSup {|dist x (z : α) - dist y (z : α)| | z : s} := by ring_nf
      _ ≤ _ := by
        apply Real.sSup_le
        · rintro _ ⟨z, hz, rfl⟩
          apply abs_dist_sub_le x y z
        · exact dist_nonneg
    · rw [← csInf_add]
      · set c : ℝ := sInf {dist x z + dist z z₁ + dist z₁ y | (z ∈ s) (z₁ ∈ s)} with hc
        calc
        _ ≤ c := by
          apply le_csInf
          · have z₀ := Classical.choice hs
            refine ⟨dist x z₀ + dist z₀ z₀ + (dist (z₀ : α) y),
              Set.mem_setOf.mpr ⟨z₀, Subtype.coe_prop z₀, ⟨z₀, Subtype.coe_prop z₀, rfl⟩⟩⟩
          · rintro b ⟨z, hz, z₁, hz₁, rfl⟩
            repeat apply (dist_triangle ..).trans; gcongr; try exact dist_triangle _ _
            exact dist_triangle x _ _
        _ ≤ _ := by
          apply le_csInf
          · have z₀ := Classical.choice hs
            refine ⟨(f z₀) + dist x z₀ + (f z₀) + dist y z₀,
              Set.mem_add.mpr ⟨(f z₀) + dist x z₀, by aesop, ⟨(f z₀) + dist y z₀, by aesop, by ring⟩⟩⟩
          · rintro b ⟨_, ⟨z, rfl⟩, _, ⟨z₁, rfl⟩, rfl⟩
            dsimp
            rw [hc]
            refine @csInf_le_of_le _ _ _ (f z + dist x ↑z + (f z₁ + dist y ↑z₁))
              (dist x z + dist z z₁ + dist (z₁ : α) y) ?_ ?_ ?_
            · refine ⟨0, Set.mem_setOf.mpr ?_⟩
              rintro a ⟨z, hz, z₁, hz₁, rfl⟩
              apply add_nonneg (add_nonneg dist_nonneg dist_nonneg) dist_nonneg
            · aesop
            · rw [dist_comm y z₁]
              linarith [(map_katetov f).dist_le_add z z₁]
      · have z₀ := Classical.choice hs
        refine ⟨(f z₀) + dist x z₀, Set.mem_setOf.mpr ⟨z₀, rfl⟩⟩
      · refine ⟨0, Set.mem_setOf.mpr ?_⟩
        rintro a ⟨z, rfl⟩
        apply add_nonneg (katetov_nonneg _ _) dist_nonneg
      · have z₀ := Classical.choice hs
        refine ⟨(f z₀) + dist y z₀, Set.mem_setOf.mpr ⟨z₀, rfl⟩⟩
      · refine ⟨0, Set.mem_setOf.mpr ?_⟩
        rintro a ⟨z, rfl⟩
        apply add_nonneg (katetov_nonneg _ _) dist_nonneg
  · by_cases hα : Nonempty α
    · have z₀ := Classical.choice hα
      exact katetovKuratowskiEmbedding α z₀
    · exact @instKatetovMapOfEmpty _ _ (not_nonempty_iff.mp hα)

def restrict {α : Type*} (s : Set α) [MetricSpace α] (f : E(α)) : E(s) := by
  refine ⟨fun x ↦ f x, ?_⟩
  constructor <;> intro x y
  · exact (map_katetov f).abs_sub_le_dist x y
  · exact (map_katetov f).dist_le_add x y

theorem eq_restrict_support {α : Type*} (s : Set α) [MetricSpace α] (f : E(s)) :
  restrict s (katetovExtension s f) = f := by
  ext x
  simp [katetovExtension, restrict]
  by_cases hs : Nonempty s
  · simp [hs]
    apply le_antisymm
    · apply csInf_le
      · refine ⟨f x + dist x x, Set.mem_setOf.mpr ?_⟩
        simp
        rintro _ z hz rfl
        rw [show dist (x : α ) z = dist x ⟨z, hz⟩ by aesop]
        linarith [le_trans (le_abs_self _) ((map_katetov f).abs_sub_le_dist x ⟨z, hz⟩)]
      · refine ⟨x, ?_⟩
        simp only [Subtype.coe_eta, dist_self, add_zero, Subtype.coe_prop, exists_const]
    · apply le_csInf
      · refine ⟨f x + dist x x, Set.mem_setOf.mpr ?_⟩
        simp
        refine ⟨x, ?_⟩
        simp only [Subtype.coe_eta, dist_self, add_zero, Subtype.coe_prop, exists_const]
      · simp
        rintro _ z hz rfl
        rw [show dist (x : α ) z = dist x ⟨z, hz⟩ by aesop]
        linarith [le_trans (le_abs_self _) ((map_katetov f).abs_sub_le_dist x ⟨z, hz⟩)]
  · exact False.elim (hs ⟨x⟩)

-- structure FinsuppKatetovMap (α : Type*) [MetricSpace α] extends KatetovMap α  where
--   kat_ext: ∃ s : Set α, Set.Finite s ∧
--     ⟨toFun, IsKatetovtoFun⟩  = katetovExtension s (restrict s ⟨toFun, IsKatetovtoFun⟩)

-- /-- The type of Katetov maps from `α`. -/
-- notation "E(" α ", ω)" => FinsuppKatetovMap α

-- theorem embed_finsupp (α : Type*) [MetricSpace α] : E(α, ω) ↪ E(α) := by
--   refine ⟨fun f ↦ ⟨f.toFun, f.IsKatetovtoFun⟩ , ?_⟩
--   intro f g h

theorem exists_isometric_embedding (α : Type*) [MetricSpace α] (s : Set α) :
  ∃ f : E(s) → E(α), Isometry f := by
    by_cases hα  : Nonempty α
    · by_cases  hs : Nonempty s
      · refine ⟨fun f ↦ katetovExtension s f, ?_⟩
        refine Isometry.of_dist_eq (fun f g ↦ le_antisymm ?_ ?_)
        · refine Real.sSup_le ?_ dist_nonneg
          simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff]
          refine fun x ↦ ?_
          simp [katetovExtension]
          simp [hs]
          have hpos : ∀ f : E(s),∀ z : s, 0 ≤ f z + dist x z := by
            refine fun f z ↦ add_nonneg (katetov_nonneg _ _) (dist_nonneg)
          have : (fun z ↦ f z + dist x z) - (fun z ↦ g z + dist x z) = fun z ↦ f z - g z := by
              aesop
          have hb : BddAbove (Set.range |(fun z ↦ f z + dist x z) - (fun z ↦ g z + dist x z)|) := by
            simp_rw [this]
            exact bounded_dist_set
          have := abs_inf_dist_le_sup hs (hpos f) (hpos g) hb
          refine le_trans (by simp) (le_trans this ?_)
          ring_nf
          exact le_refl _
        · refine Real.sSup_le ?_ dist_nonneg
          simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff]
          refine fun x ↦ ?_
          simp [katetovExtension]
          simp [hs]
          refine le_csSup_of_le bounded_dist_set ?_ (le_refl |f x - g x|)
          refine ⟨x, ?_⟩
          simp
          have : ∀ f : E(s), sInf {f ⟨a, h⟩ + dist (x : α) a | (a : α) (h : a ∈ s)} = f x:= by
            intro f; refine le_antisymm ?_ ?_
            · apply csInf_le
              · refine ⟨0, Set.mem_setOf.mpr ?_⟩
                rintro _ ⟨z, hz, rfl⟩
                exact add_nonneg (katetov_nonneg _ _) (dist_nonneg)
              · refine Set.mem_setOf.mpr ⟨x, by simp⟩
            · apply le_csInf
              · refine ⟨f x + dist (x : α) (x : α), Set.mem_setOf.mpr ⟨(x : α), by simp⟩⟩
              · rintro _ ⟨z, hz, rfl⟩
                rw [show dist (x : α ) z = dist x ⟨z, hz⟩ by aesop]
                linarith [le_of_abs_le <| (map_katetov f).abs_sub_le_dist x ⟨z, hz⟩]
          simp_rw [this f, this g]
      · have x₀ := Classical.choice ‹Nonempty α›
        refine ⟨fun _ ↦ katetovKuratowskiEmbedding _ x₀, ?_⟩
        refine Isometry.of_dist_eq (fun f g ↦ ?_)
        simp
        have : IsEmpty s := by aesop
        exact empty_unique f g
    · have : IsEmpty α := by aesop
      refine ⟨fun _ ↦ instKatetovMapOfEmpty α, ?_⟩
      refine Isometry.of_dist_eq (fun f g ↦ ?_)
      have : IsEmpty s := by aesop
      simp
      exact empty_unique f g

end KatetovExtension





-- /-- The type of finitely supported Katetov maps from `α` -/
-- structure FinsuppKatetovMap (α : Type*) [MetricSpace α] extends KatetovMap α, Finsupp α ℝ




-- -- example (F : Type*) (α : Type*) [MetricSpace α] [FunLike F α  ℝ] [FinsuppKatetovMapClass F α] :
-- --   (FinsuppKatetovMapClass.toKatetovMapClass) = FinsuppKatetovMapClass.toFinsupp := rfl

-- namespace FinsuppKatetovMap

-- variable {α : Type*} [MetricSpace α]

-- instance funLike : FunLike E(α, ω) α ℝ where
--   coe := FinsuppKatetovMap.toFun
--   coe_injective' f g h := by cases f; cases g; congr


-- @[simp]
-- theorem toFun_eq_coe {f : E(α, ω)} : f.toFun = (f : α → ℝ) := rfl

-- instance : CanLift (α → ℝ) E(α) DFunLike.coe IsKatetov := ⟨fun f hf ↦ ⟨⟨f, hf⟩, rfl⟩⟩

-- /-- See Topology/ContinuousFunction.Basic -/
-- def Simps.apply (f : E(α)) : α → ℝ := f

-- initialize_simps_projections KatetovMap (toFun → apply)

-- @[ext]
-- theorem ext {f g : E(α)} (h : ∀ a, f a = g a) : f = g := DFunLike.ext _ _ h

-- /-- Copy of a `KatetovMap` with a new `toFun` equal to the old one. Useful to fix definitional
-- equalities. See Topology/ContinuousFunction.Basic -/
-- protected def copy (f : E(α)) (f' : α → ℝ) (h : f' = f) : E(α) where
--   toFun := f'
--   IsKatetovtoFun := h.symm ▸ f.IsKatetovtoFun

-- @[simp]
-- theorem coe_copy (f : E(α)) (f' : α → ℝ) (h : f' = f) : ⇑(f.copy f' h) = f' :=
--   rfl

-- theorem copy_eq (f : E(α)) (f' : α → ℝ) (h : f' = f) : f.copy f' h = f :=
--   DFunLike.ext' h

-- variable {f g : E(α)}

-- theorem katetov_set_coe (s : Set E(α)) (f : s) : IsKatetov (f : α → ℝ) :=
--   f.1.IsKatetovtoFun

-- theorem coe_injective : @Function.Injective E(α) (α → ℝ) (↑) :=
--   fun f g h ↦ by cases f; cases g; congr

-- @[simp]
-- theorem coe_mk (f : α → ℝ) (h : IsKatetov f) : ⇑(⟨f, h⟩ : E(α)) = f :=
--   rfl

-- end FinsuppKatetovMap
