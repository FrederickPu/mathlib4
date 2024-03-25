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

variable {α : Type*} [MetricSpace α]

/-- A real valued function from a metric space is Katetov if it satisfies
    the following inequalities: -/
@[mk_iff]
structure IsKatetov (f : α → ℝ) : Prop where
  /-- `f` is 1-Lipschitz -/
  abs_sub_le_dist : ∀ x y, |f x - f y| ≤ dist x y
  /-- `f` obeys the Katetov "triangle inequality"  -/
  dist_le_add : ∀ x y, dist x y ≤ f x + f y

/-- The type of Katetov maps from `α`
-/
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

-- set_option trace.Meta.synthInstance true
example : PseudoMetricSpace ℝ := by infer_instance

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

lemma abs_sub_dist_le {f : E(α)} {x y: α} : |f x - dist x y| ≤ f y := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · exact neg_le_sub_iff_le_add.mpr <| (map_katetov f).dist_le_add x y
  · exact sub_le_comm.mpr <| le_of_abs_le <| (map_katetov f).abs_sub_le_dist x y

theorem bounded_sub {f g : E(α)} : BddAbove {|f x - g x| | x : α} := by
  by_cases hn : Nonempty α
  · let x₀ := Classical.choice ‹Nonempty α›
    refine ⟨f x₀ + g x₀, fun _ ⟨x, hx⟩ ↦ ?_⟩; rw [← hx]
    calc
    _ ≤ |f x - dist x x₀| + |dist x x₀ - g x| := abs_sub_le (f x) (dist x x₀) (g x)
    _ = |f x - dist x x₀| + |g x - dist x x₀| := by rw [← abs_sub_comm _ (g x)]
    _ ≤ f x₀ + g x₀ := add_le_add abs_sub_dist_le abs_sub_dist_le
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

noncomputable instance : MetricSpace E(α) where
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
          apply le_csSup (by apply BddAbove.add <;> apply bounded_sub)
          refine Set.mem_add.mpr ⟨|f x - g x|, (by simp), (by simp)⟩
        · have x₀ := Classical.choice ‹Nonempty α›
          use |f x₀ - g x₀|; simp
        · apply bounded_sub
        · have x₀ := Classical.choice ‹Nonempty α›
          use |g x₀ - h x₀|; simp
        · apply bounded_sub
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
    · apply bounded_sub
    · rintro _ ⟨x, rfl⟩; exact abs_nonneg _
  edist_dist x y:= by exact ENNReal.coe_nnreal_eq _

theorem dist_coe_le_dist (f g : E(α)) (x : α) : dist (f x) (g x) ≤ dist f g :=
  by refine le_csSup bounded_sub (by simp [dist])

theorem dist_le {C :ℝ} (C0 : (0 : ℝ) ≤ C) (f g : E(α)):
    dist f g ≤ C ↔ ∀ x : α, dist (f x) (g x) ≤ C := by
  refine ⟨fun h x => le_trans (dist_coe_le_dist _ _ x) h, fun H ↦ ?_⟩
  simp [dist]; apply Real.sSup_le (by simp [*] at *; assumption) (C0)

noncomputable instance : CompleteSpace E(α) :=
  Metric.complete_of_cauchySeq_tendsto fun (u : ℕ → E(α)) (hf : CauchySeq u) => by
    rcases cauchySeq_iff_le_tendsto_0.1 hf with ⟨b, b0, b_bound, b_lim⟩
    have u_bdd := fun x n m N hn hm => le_trans (dist_coe_le_dist _ _ x) (b_bound n m N hn hm)
    have ux_cau : ∀ x : α, CauchySeq fun n => u n x :=
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
          _ = f x + f y + (u N x - f x) + (u N y - f y) := by
              rw [← add_zero (u N y), show 0 = f x - f x + f y - f y by ring]; ring_nf
          _ ≤ f x + f y + 2*ε := by linarith [le_of_lt (lt_of_abs_lt hNx), le_of_lt (lt_of_abs_lt hNy)]
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

-- to change to have dis
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
        · refine (Real.le_sSup_iff bounded_sub ?_).mpr  ?_
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
            refine @csInf_le_of_le _ _ ({g x | x} - {|f x - g x| | x})
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

noncomputable def extend {α β : Type*} [MetricSpace α] [MetricSpace β] (ρ : β → α)
  (hρ : Isometry ρ) (f : E(β)) : E(α) := by
  by_cases hs : Nonempty β
  · refine ⟨fun x ↦ sInf {(f z) + dist x (ρ z) | z : β}, ?_⟩
    constructor <;> intro x y
    · calc
      _ ≤ sSup {|f z + dist x (ρ z) - (f z + dist y (ρ z))| | z : β} := by
        refine abs_inf_dist_le_sup hs ?_ ?_ ?_
        · refine fun x ↦ add_nonneg (katetov_nonneg f x) (dist_nonneg)
        · refine fun x ↦ add_nonneg (katetov_nonneg f x) (dist_nonneg)
        · use dist x y
          rintro _ ⟨z, rfl⟩
          simp [show |(fun z ↦ f z + dist x (ρ z)) - fun z ↦ f z + dist y (ρ z)| z
            = |(f z + dist x (ρ z)) - (f z + dist y (ρ z))| by rfl, abs_dist_sub_le]
      _ = sSup {|dist x (ρ z) - dist y (ρ z)| | z : β} := by ring_nf
      _ ≤ _ := by
        refine Real.sSup_le ?_ dist_nonneg
        · rintro _ ⟨z, hz, rfl⟩
          apply abs_dist_sub_le x y (ρ z)
    · rw [← csInf_add]
      · set c : ℝ := sInf {dist x  (ρ z) + dist z z₁ + dist (ρ z₁) y | (z : β) (z₁ : β)} with hc
        calc
        _ ≤ c := by
          apply le_csInf
          · have z₀ := Classical.choice hs
            refine ⟨dist x (ρ z₀) + dist z₀ z₀ + (dist (ρ z₀) y),
              Set.mem_setOf.mpr ⟨z₀,⟨z₀, by simp⟩⟩⟩
          · rintro b ⟨z, z₁, rfl⟩
            repeat apply (dist_triangle ..).trans; gcongr; try exact dist_triangle _ _
            rw [hρ.dist_eq]
        _ ≤ _ := by
          apply le_csInf
          · have z₀ := Classical.choice hs
            refine ⟨(f z₀) + dist x (ρ z₀) + (f z₀) + dist y (ρ z₀),
              Set.mem_add.mpr ⟨(f z₀) + dist x (ρ z₀), by aesop, ⟨(f z₀) + dist y (ρ z₀), by aesop, by ring⟩⟩⟩
          · rintro b ⟨_, ⟨z, rfl⟩, _, ⟨z₁, rfl⟩, rfl⟩
            simp [hc]
            refine @csInf_le_of_le _ _ _ (f z + dist x (ρ z) + (f z₁ + dist y (ρ z₁)))
              (dist x (ρ z) + dist z z₁ + dist (ρ z₁) y) ?_ ?_ ?_
            · refine ⟨0, Set.mem_setOf.mpr ?_⟩
              rintro a ⟨z, hz, z₁, hz₁, rfl⟩
              apply add_nonneg (add_nonneg dist_nonneg dist_nonneg) dist_nonneg
            · aesop
            · rw [dist_comm y (ρ z₁)]
              linarith [(map_katetov f).dist_le_add z z₁]
      · have z₀ := Classical.choice hs
        refine ⟨(f z₀) + dist x (ρ z₀), Set.mem_setOf.mpr ⟨z₀, rfl⟩⟩
      · refine ⟨0, Set.mem_setOf.mpr ?_⟩
        rintro a ⟨z, rfl⟩
        apply add_nonneg (katetov_nonneg _ _) dist_nonneg
      · have z₀ := Classical.choice hs
        refine ⟨(f z₀) + dist y (ρ z₀), Set.mem_setOf.mpr ⟨z₀, rfl⟩⟩
      · refine ⟨0, Set.mem_setOf.mpr ?_⟩
        rintro a ⟨z, rfl⟩
        apply add_nonneg (katetov_nonneg _ _) dist_nonneg
  · by_cases hα : Nonempty α
    · have z₀ := Classical.choice hα
      exact katetovKuratowskiEmbedding α z₀
    · exact @instKatetovMapOfEmpty _ _ (not_nonempty_iff.mp hα)


def restrict {α β: Type*} [MetricSpace α][MetricSpace β] (ρ : β → α) (hρ : Isometry ρ)
    (f : E(α)) : E(β) := by
  refine ⟨fun x ↦ f (ρ x), ?_⟩
  constructor <;> intro x y
  · rw [← hρ.dist_eq]; exact (map_katetov f).abs_sub_le_dist (ρ x) (ρ y)
  · rw [← hρ.dist_eq]; exact (map_katetov f).dist_le_add (ρ x) (ρ y)

theorem eq_restrict_support {α β: Type} [MetricSpace α][MetricSpace β] (ρ : β → α)
  (hρ : Isometry ρ) (f : E(β)) :
    restrict ρ hρ (extend ρ hρ f) = f := by
  ext x
  simp [extend, restrict]
  by_cases hs : Nonempty β
  · simp [hs]
    apply le_antisymm
    · refine csInf_le ?_ ⟨x, by simp⟩
      · refine ⟨f x + dist x x, Set.mem_setOf.mpr ?_⟩
        simp [hρ.dist_eq]
        intro z
        linarith [le_trans (le_abs_self _) ((map_katetov f).abs_sub_le_dist x z)]
    · refine le_csInf ⟨f x + dist x x, Set.mem_setOf.mpr ⟨x, by simp⟩⟩ ?_
      · simp [hρ.dist_eq]
        intro z
        linarith [le_trans (le_abs_self _) ((map_katetov f).abs_sub_le_dist x z)]
  · exact False.elim (hs ⟨x⟩)

theorem exists_isometric_embedding_of_subset (α β : Type) [MetricSpace α][MetricSpace β] (ρ : β → α)
  (hρ : Isometry ρ) :
  ∃ f : E(β) → E(α), Isometry f := by
    by_cases hα  : Nonempty α
    · by_cases  hs : Nonempty β
      · refine ⟨fun f ↦ extend ρ hρ f, ?_⟩
        refine Isometry.of_dist_eq (fun f g ↦ le_antisymm ?_ ?_)
        · refine Real.sSup_le ?_ dist_nonneg
          simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff]
          refine fun x ↦ ?_
          simp [extend, hs]
          have hpos : ∀ f : E(β), ∀ z : β, 0 ≤ f z + dist x (ρ z) := by
            refine fun f z ↦ add_nonneg (katetov_nonneg _ _) (dist_nonneg)
          have : (fun z ↦ f z + dist x (ρ z)) - (fun z ↦ g z + dist x (ρ z)) = fun z ↦ f z - g z := by
              aesop
          have hb : BddAbove (Set.range |(fun z ↦ f z + dist x (ρ z)) - (fun z ↦ g z + dist x (ρ z))|) := by
            simp_rw [this]
            exact bounded_sub
          have := abs_inf_dist_le_sup hs (hpos f) (hpos g) hb
          refine le_trans (by simp) (le_trans this ?_)
          ring_nf
          exact le_refl _
        · refine Real.sSup_le ?_ dist_nonneg
          simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff]
          refine fun x ↦ ?_
          simp [extend]
          simp [hs]
          refine le_csSup_of_le bounded_sub ?_ (le_refl |f x - g x|)
          refine ⟨(ρ x), ?_⟩
          simp
          have : ∀ f : E(β), sInf {f z + dist (ρ x) (ρ z) | (z : β)} = f x:= by
            intro f; refine le_antisymm ?_ ?_
            · apply csInf_le
              · refine ⟨0, Set.mem_setOf.mpr ?_⟩
                rintro _ ⟨z, hz, rfl⟩
                exact add_nonneg (katetov_nonneg _ _) (dist_nonneg)
              · refine Set.mem_setOf.mpr ⟨x, by simp⟩
            · apply le_csInf
              · refine ⟨f x + dist (ρ x) (ρ x), Set.mem_setOf.mpr ⟨x, by simp⟩⟩
              · rintro _ ⟨z, hz, rfl⟩
                rw [hρ.dist_eq]
                linarith [le_of_abs_le <| (map_katetov f).abs_sub_le_dist x z]
          simp_rw [this f, this g]
      · have x₀ := Classical.choice ‹Nonempty α›
        refine ⟨fun _ ↦ katetovKuratowskiEmbedding _ x₀, ?_⟩
        refine Isometry.of_dist_eq (fun f g ↦ ?_)
        simp
        have : IsEmpty β := by aesop
        exact empty_unique f g
    · have : IsEmpty α := by aesop
      refine ⟨fun _ ↦ instKatetovMapOfEmpty α, ?_⟩
      refine Isometry.of_dist_eq (fun f g ↦ ?_)
      have : IsEmpty β := by
        by_contra h
        exact IsEmpty.false <| ρ <| Classical.choice (not_isEmpty_iff.mp h)
      simp
      exact empty_unique f g

def FinSuppKatetovMaps : Set E(α) := ⋃ s : Finset α, Set.range (extend (fun (x : s) ↦ x) (isometry_id))

/-- The type of Katetov maps from `α`. -/
notation "E(" α ", ω)" => @FinSuppKatetovMaps α _
-- variable (α : Type) [MetricSpace α]

noncomputable instance : MetricSpace E(α, ω) := by infer_instance

theorem distance_isKatetov {α : Type*} [MetricSpace α] (x : α) : IsKatetov (fun y ↦ dist x y) := by
  constructor <;> (intro y z; rw [dist_comm x y])
  · rw [dist_comm x z]; exact abs_dist_sub_le y z x
  · exact dist_triangle y x z

def instKatetovMapFinSuppOfEmpty (α : Type*) [MetricSpace α] [IsEmpty α] : E(α, ω) := by
  set f := instKatetovMapOfEmpty α
  refine ⟨f, ?_⟩
  refine Set.mem_iUnion.mpr ⟨∅, ⟨@instKatetovMapOfEmpty {x | x ∈ (∅ : Finset α)} _ (by simp), ?_⟩⟩
  simp [extend, not_nonempty_iff.mpr]

theorem empty_uniqueFinSupp [IsEmpty α] (f g : E(α, ω)) : f = g := by
  ext x; exact (IsEmpty.false x).elim

theorem exists_isometric_embedding_of_FinSupp_subset (α β : Type) [MetricSpace α][MetricSpace β] (ρ : β → α)
  (hρ : Isometry ρ) :
  ∃ f : E(β, ω) → E(α, ω), Isometry f := by
    by_cases hα  : Nonempty α
    · by_cases  hs : Nonempty β
      · refine ⟨fun f ↦ ⟨extend ρ hρ f, ?_⟩, ?_⟩
        · apply Set.mem_iUnion.mpr
          sorry
        refine Isometry.of_dist_eq (fun f g ↦ le_antisymm ?_ ?_)
        · refine Real.sSup_le ?_ dist_nonneg
          simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff]
          refine fun x ↦ ?_
          simp [extend, hs]
          have hpos : ∀ f : E(β, ω), ∀ z : β, 0 ≤ (f : E(β)) z + dist x (ρ z) := by
            refine fun (f : E(β, ω)) (z : β) ↦ add_nonneg ((katetov_nonneg _ _)) (dist_nonneg)
          have : (fun z ↦ (f : E(β)) z + dist x (ρ z)) - (fun z ↦ (g : E(β)) z + dist x (ρ z)) = fun z ↦ (f : E(β)) z - (g : E(β)) z := by
              aesop
          have hb : BddAbove (Set.range |(fun z ↦ (f : E(β)) z + dist x (ρ z)) - (fun z ↦ (g : E(β)) z + dist x (ρ z))|) := by
            simp_rw [this]
            exact bounded_sub
          have := abs_inf_dist_le_sup hs (hpos f) (hpos g) hb
          refine le_trans (by simp) (le_trans this ?_)
          ring_nf
          exact le_refl _
        · refine Real.sSup_le ?_ dist_nonneg
          simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff]
          refine fun x ↦ ?_
          simp [extend]
          simp [hs]
          refine le_csSup_of_le bounded_sub ?_ (le_refl |(f : E(β)) x - (g : E(β)) x|)
          refine ⟨(ρ x), ?_⟩
          simp
          have : ∀ f : E(β), sInf {(f : E(β)) z + dist (ρ x) (ρ z) | (z : β)} = f x:= by
            intro f; refine le_antisymm ?_ ?_
            · apply csInf_le
              · refine ⟨0, Set.mem_setOf.mpr ?_⟩
                rintro _ ⟨z, hz, rfl⟩
                exact add_nonneg (katetov_nonneg _ _) (dist_nonneg)
              · refine Set.mem_setOf.mpr ⟨x, by simp⟩
            · apply le_csInf
              · refine ⟨f x + dist (ρ x) (ρ x), Set.mem_setOf.mpr ⟨x, by simp⟩⟩
              · rintro _ ⟨z, hz, rfl⟩
                rw [hρ.dist_eq]
                linarith [le_of_abs_le <| (map_katetov f).abs_sub_le_dist x z]
          simp_rw [this f, this g]
      · have x₀ := Classical.choice ‹Nonempty α›
        refine ⟨fun _ ↦ ⟨katetovKuratowskiEmbedding _ x₀, ?_⟩, ?_⟩
        · apply Set.mem_iUnion.mpr
          refine ⟨{x₀}, ?_⟩
          apply Set.mem_range.mpr
          refine ⟨⟨fun y ↦ dist x₀ y, ?_⟩, ?_⟩
          · constructor <;> (intro y z; rw [dist_comm x₀ y])
            · rw [dist_comm x₀ z]; exact abs_dist_sub_le (y : α) (z : α) x₀
            · exact dist_triangle (y : α) x₀ z
          simp [extend]
          sorry -- swap katetovkuratowski embedding to be explicit
        refine Isometry.of_dist_eq (fun f g ↦ ?_)
        simp
        have : IsEmpty β := by aesop
        exact empty_uniqueFinSupp f g
    · have : IsEmpty α := by aesop
      refine ⟨fun _ ↦ instKatetovMapFinSuppOfEmpty α, ?_⟩
      refine Isometry.of_dist_eq (fun f g ↦ ?_)
      have : IsEmpty β := by
        by_contra h
        exact IsEmpty.false <| ρ <| Classical.choice (not_isEmpty_iff.mp h)
      simp
      exact empty_uniqueFinSupp f g



theorem exists_isometric_embedding (α : Type) [MetricSpace α] : ∃ f : α → E(α, ω), Isometry f := by
    by_cases h : Nonempty α
    · refine ⟨fun x : α ↦ ⟨⟨fun y ↦ dist x y, ?_⟩, ?_⟩, ?_⟩
      · constructor <;> (intro y z; rw [dist_comm x y])
        · rw [dist_comm x z]; exact abs_dist_sub_le y z x
        · exact dist_triangle y x z
      · apply Set.mem_iUnion.mpr
        refine ⟨{x}, ?_⟩
        apply Set.mem_range.mpr
        refine ⟨⟨fun y ↦ dist x y, ?_⟩, ?_⟩
        · constructor <;> (intro y z; rw [dist_comm x y])
          · rw [dist_comm x z]; exact abs_dist_sub_le (y : α) (z : α) x
          · exact dist_triangle (y : α) x z
        · ext z
          simp [extend, dist_comm]
      · refine Isometry.of_dist_eq (fun x y ↦ le_antisymm ?_ ?_)
        · refine Real.sSup_le ?_ dist_nonneg
          · simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff]
            refine fun z ↦ abs_dist_sub_le x y z
        · refine (Real.le_sSup_iff bounded_sub ?_).mpr  ?_
          · have x₀ := Classical.choice ‹Nonempty α›
            use |dist x x₀ - dist y x₀|; simp
          · simp only [KatetovMap.coe_mk, Set.mem_setOf_eq, exists_exists_eq_and]
            refine fun ε εpos ↦ ⟨x, ?_⟩
            rw [dist_self, zero_sub, abs_neg, dist_comm, abs_of_nonneg (dist_nonneg)]
            exact add_lt_of_neg_right (dist y x) εpos
    · refine ⟨fun _ ↦ ⟨@instKatetovMapOfEmpty _ _ (not_nonempty_iff.mp h), ?_⟩, fun y ↦ ?_⟩
      · exact ((not_nonempty_iff.mp h).false ‹α›).elim
      · exact ((not_nonempty_iff.mp h).false y).elim

noncomputable def embedding (α : Type) [MetricSpace α] : α ↪ E(α, ω) := by
  choose f h using exists_isometric_embedding α; refine ⟨f, h.injective⟩

protected theorem embedding.isometry (α : Type) [MetricSpace α] :
    Isometry (embedding α) :=
    Classical.choose_spec <| exists_isometric_embedding α


end KatetovExtension

open Set TopologicalSpace

#check TopologicalSpace.instSeparableSpaceForAllTopologicalSpace

set_option trace.Meta.synthInstance true
instance : TopologicalSpace (α → ℝ) := by infer_instance


instance inst_silly (α : Type*) [MetricSpace α] (hα : Fintype α)  : SeparableSpace (α → ℝ):= by
  apply TopologicalSpace.instSeparableSpaceForAllTopologicalSpace

instance sep_inst {α : Type*} [MetricSpace α] (hα : Fintype α) : SeparableSpace E(α):= by
  sorry

instance sep_range (α : Type*) [MetricSpace α] (s : Finset α) :
  IsSeparable (@range E(α) E(s) (KatetovExtension.extend (fun x ↦ ↑x) isometry_id)) := by
  have : SeparableSpace E(s) := by exact sep_inst (by infer_instance)
  apply TopologicalSpace.isSeparable_range
  sorry


instance (α : Type*) [MetricSpace α] [Countable α] : SeparableSpace E(α, ω) := by
    rw [KatetovExtension.FinSuppKatetovMaps]
    have := Set.countable_setOf_finite_subset (@Set.countable_univ α _)
    apply TopologicalSpace.IsSeparable.separableSpace
    apply TopologicalSpace.IsSeparable.iUnion (fun i ↦ @sep_range α _ i)

-- instance [SeparableSpace α] : SeparableSpace E(α, ω) := by
--     obtain ⟨s, hsc, hds⟩ := TopologicalSpace.exists_countable_dense α
-- now take E(s, ω), dump into E(α, ω) by extend : and for f : E(α, ω), get ε sup-approx in s of βᶠ, and extend to E(α, ω). this is ε close


-- noncomputable def KatetovSeq (α : Type u) [MetricSpace α]: ℕ → Type u  := fun n ↦
--   match n with
--   | 0 => α
--   | n + 1 => E(KatetovSeq n, ω) -- use sigma type
