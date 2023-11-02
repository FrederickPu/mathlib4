/-
Copyright (c) 2023 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Geometry.Manifold.SmoothManifoldWithCorners
import Mathlib.Tactic.RewriteSearch

/-!
# Charts are local diffeomorphisms

TODO: prove what I want to, then add a real docstring
-/

open Function Manifold Set SmoothManifoldWithCorners TopologicalSpace Topology
set_option autoImplicit false

variable
  -- Let `M` be a manifold over the pair `(E, H)`.
  {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  --[SmoothManifoldWithCorners I M]
  -- Let `N` be a smooth manifold over the pair `(F, G)`.
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Type*} [TopologicalSpace G]
  (J : ModelWithCorners ℝ F G) {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  --[SmoothManifoldWithCorners J N] {n : ℕ∞}

-- On any topological manifold (charted space on a normed space),
-- each chart is a structomorphism (from its source to its target).
variable {e : LocalHomeomorph M H} (he : e ∈ atlas H M)

/-- If `s` is a non-empty open subset of `M`, every chart of `s` is the restriction
 of some chart on `M`. -/
lemma chartOn_open_eq (s : Opens M) [Nonempty s] {e' : LocalHomeomorph s H} (he' : e' ∈ atlas H s) :
    ∃ x : s, e' = (chartAt H (x : M)).subtypeRestr s := by
  rcases he' with ⟨xset, ⟨x, hx⟩, he'⟩
  have : {LocalHomeomorph.subtypeRestr (chartAt H ↑x) s} = xset := hx
  exact ⟨x, mem_singleton_iff.mp (this ▸ he')⟩

-- XXX: can I unify this with `chartOn_open_eq`?
lemma chartOn_open_eq' (t : Opens H) [Nonempty t] {e' : LocalHomeomorph t H} (he' : e' ∈ atlas H t) :
    ∃ x : t, e' = (chartAt H ↑x).subtypeRestr t := by
  rcases he' with ⟨xset, ⟨x, hx⟩, he'⟩
  have : {LocalHomeomorph.subtypeRestr (chartAt H ↑x) t} = xset := hx
  exact ⟨x, mem_singleton_iff.mp (this ▸ he')⟩

-- Restricting a chart of `M` to an open subset `s` yields a chart in the maximal atlas of `s`.
-- xxx: is the HasGroupoid part needed? I think it is.
lemma fixed {G : StructureGroupoid H} (h: HasGroupoid M G) [ClosedUnderRestriction G] (s : Opens M) [Nonempty s] :
    e.subtypeRestr s ∈ G.maximalAtlas s := by
  rw [mem_maximalAtlas_iff]
  intro e' he'
  -- `e'` is the restriction of some chart of `M` at `x`
  obtain ⟨x, this⟩ := chartOn_open_eq s he'
  rw [this]
  let e'full := chartAt H (x : M)
  -- the unrestricted charts are in the groupoid,
  have aux : e.symm ≫ₕ e'full ∈ G := G.compatible he (chart_mem_atlas H (x : M))
  have aux' : e'full.symm ≫ₕ e ∈ G := G.compatible (chart_mem_atlas H (x : M)) he
  -- the composition is the restriction of the charts
  let r_corr := e.subtypeRestr_symm_trans_subtypeRestr s (chartAt H (x : M))
  let r'_corr := (chartAt H (x : M)).subtypeRestr_symm_trans_subtypeRestr s e
  -- hence the restriction also lies in the groupoid
  constructor
  · have : (e.symm ≫ₕ chartAt H ↑x).restr (e.target ∩ e.symm ⁻¹' s) ∈ G := by
      let t := (e.target ∩ e.symm ⁻¹' s)
      have htopen : IsOpen t := by
        apply IsOpen.inter e.open_target
        sorry -- easy, as s is open and e.symm is continuous on its source
        -- xxx: need version of IsOpen.preimage for ContinuousOn, then this is s.2.preimage e.cont_invFun
      apply G.locality
      intro x' hx'
      refine ⟨e.target ∩ e.symm ⁻¹' s, htopen, ?_, ?_ ⟩
      · rw [LocalHomeomorph.restr_source] at hx'
        have : x' ∈ interior (e.target ∩ ↑(LocalHomeomorph.symm e) ⁻¹' ↑s) := by
          sorry -- apply mem_right_inter or so
        apply (interior_subset this)
        -- xxx: why can't I rewrite by `htopen.interioreq` or so?
      · exact closedUnderRestriction' (closedUnderRestriction' aux htopen) htopen
    exact G.eq_on_source this r_corr
  · sorry -- completely similar to first part: FIXME extract into general lemma!
#exit


-- TODO: prove this! it's the main load-bearing part of the lemma below!
-- XXX: this lemma is false as-is; `fixed` is correct
lemma obvious_false (s : Opens M) [Nonempty s] : e.subtypeRestr s ∈ atlas H s := by
  -- can we argue that e = chartAt H x for some x,
  -- hence e.subtypeRestr s is the chart in s at x?
  -- then, would use  simp only [mem_iUnion, mem_singleton_iff]; rfl
  sorry

/-- Charts are structomorphisms. -/
-- xxx: do I need [ClosedUnderRestriction G]? in practice, is not an issue
lemma LocalHomeomorphism.toStructomorph {G : StructureGroupoid H} [ClosedUnderRestriction G]
    (h: HasGroupoid M G) : Structomorph G M H := by
  let s : Opens M := { carrier := e.source, is_open' := e.open_source }
  let t : Opens H := { carrier := e.target, is_open' := e.open_target }

  have : Nonempty s := sorry -- otherwise, trivial
  have : Nonempty t := sorry -- otherwise, trivial
  -- helper lemma: cannot pull out easily, but is conceptually independent
  have helper : ∀ c' : LocalHomeomorph t H, c' ∈ atlas H t →
      e.toHomeomorphSourceTarget.toLocalHomeomorph.trans c' ∈ atlas H s := by
    set e' := e.toHomeomorphSourceTarget.toLocalHomeomorph with eq -- source s, target t
    intro c' hc'
    -- Choose `x ∈ t` so c' is the restriction of `chartAt H x`.
    obtain ⟨x, hc'⟩ := chartOn_open_eq' t hc'
    -- As H has only one chart, this chart is the identity: i.e., c' is the inclusion.
    rw [hc', (chartAt_self_eq)]
    -- simplify: perhaps not needed, but definitely ok
    rw [LocalHomeomorph.subtypeRestr_def, LocalHomeomorph.trans_refl]

    -- now: argue that our expression equals this chart above
    let r := LocalHomeomorph.subtypeRestr e s
    set goal := (e' ≫ₕ Opens.localHomeomorphSubtypeCoe t)
    -- TODO: this should be reasonably obvious... means some missing simp lemma somewhere
    have congr_inv : ∀ y, goal.symm y = r.symm y := by
      intro y
      rw [LocalHomeomorph.coe_trans_symm]
      have aux : ∀ y' : t, e'.symm y' = e.symm ↑y' := by intro; rfl
      let aux := aux (t.localHomeomorphSubtypeCoe.symm y)
      -- also fails: rw [aux]
      calc (e'.symm ∘ t.localHomeomorphSubtypeCoe.symm) y
        _ = e'.symm (t.localHomeomorphSubtypeCoe.symm y) := rfl
        -- doesn't work, for some reason! _ = (e.symm) ↑(t.localHomeomorphSubtypeCoe.symm y) := by rw [aux] -- rfl
        _ = (e.toHomeomorphSourceTarget.toLocalHomeomorph).symm (t.localHomeomorphSubtypeCoe.symm y) := rfl
        _ = (e.toHomeomorphSourceTarget.symm.toLocalHomeomorph) (t.localHomeomorphSubtypeCoe.symm y) := by rw [← Homeomorph.symm_toLocalHomeomorph]
        _ = (e.symm.toHomeomorphSourceTarget.toLocalHomeomorph) (t.localHomeomorphSubtypeCoe.symm y) := rfl

        _ = (e.symm.toHomeomorphSourceTarget.toLocalHomeomorph) (t.localHomeomorphSubtypeCoe.symm y) := sorry--rfl
        --_ = (e'.trans (t.localHomeomorphSubtypeCoe)).symm y := rfl
        --_ = (e.toHomeomorphSourceTarget.toLocalHomeomorph.trans (t.localHomeomorphSubtypeCoe)).symm y := rfl

        _ = (e.symm.trans s.localHomeomorphSubtypeCoe.symm) y := sorry
        _ = (s.localHomeomorphSubtypeCoe.trans e).symm y := rfl
        _ = r.symm y := rfl
    have congr_to : ∀ y, goal y = r ↑y := by intro; rfl
    have h2 : goal = r := LocalHomeomorph.ext goal r congr_to congr_inv (by simp)
    exact mem_of_eq_of_mem h2 (obvious_false s)
  -- singleton_hasGroupoid should also show this, by the way
  -- have : HasGroupoid t G := t.instHasGroupoid G -- as G is closed under restrictions
  let ehom := e.toHomeomorphSourceTarget -- temporarily given a name, to make the goal readable
  have : Structomorph G s t := {
    ehom with
    mem_groupoid := by
      intro c c' hc hc'
      show (c.symm).trans (ehom.toLocalHomeomorph.trans c') ∈ G -- just our pretty-printed goal

      -- Setting: have s ⊆ M and t ⊆ H, e maps s to t.
      -- c : s → H is a chart of M; c': t → M is essentially the inclusion.

      -- The atlas on H on itself has only one chart (by `chartedSpaceSelf_atlas H`),
      -- hence c' (as a restriction of that) is the inclusion.
      have : ∀ x, c' x = x := sorry -- unsure how to formally prove this...
      -- This *almost* gives our claim: except that `e` is a chart on M and c is one on s,
      -- so they don't fit together nicely. (Composing with the inclusion makes that nice...)
      -- let r := G.compatible hc he
      -- This version is rigorous... except the sorry (i.e. helper above) might be too optimistic.
      exact G.compatible hc (helper c' hc')
  }
  sorry

-- /-- Each chart inverse is a structomorphism. -/
-- -- essentially re-use the proof above!
-- lemma LocalHomeomorphism.symm_toStructomorph {e : LocalHomeomorph M H} (he : e ∈ atlas H M)
--     {G : StructureGroupoid H} : Structomorph G M H := sorry

-- TODO: Generalise this to all extended charts, if `I` is boundaryless.
