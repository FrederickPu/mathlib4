import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Intervals.Basic

/-! ### piecewise -/

open Function

namespace Finset
variable {ι : Type*} {π : ι → Sort*} (s : Finset ι) (f g : ∀ i, π i)

/-- `s.piecewise f g` is the function equal to `f` on the finset `s`, and to `g` on its
complement. -/
def piecewise [∀ j, Decidable (j ∈ s)] : ∀ i, π i := fun i ↦ if i ∈ s then f i else g i
#align finset.piecewise Finset.piecewise

-- Porting note (#10618): @[simp] can prove this
theorem piecewise_insert_self [DecidableEq ι] {j : ι} [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g j = f j := by simp [piecewise]
#align finset.piecewise_insert_self Finset.piecewise_insert_self

@[simp]
theorem piecewise_empty [∀ i : ι, Decidable (i ∈ (∅ : Finset ι))] : piecewise ∅ f g = g := by
  ext i
  simp [piecewise]
#align finset.piecewise_empty Finset.piecewise_empty

variable [∀ j, Decidable (j ∈ s)]

-- TODO: fix this in norm_cast
@[norm_cast move]
theorem piecewise_coe [∀ j, Decidable (j ∈ (s : Set ι))] :
    (s : Set ι).piecewise f g = s.piecewise f g := by
  ext
  congr
#align finset.piecewise_coe Finset.piecewise_coe

@[simp]
theorem piecewise_eq_of_mem {i : ι} (hi : i ∈ s) : s.piecewise f g i = f i := by
  simp [piecewise, hi]
#align finset.piecewise_eq_of_mem Finset.piecewise_eq_of_mem

@[simp]
theorem piecewise_eq_of_not_mem {i : ι} (hi : i ∉ s) : s.piecewise f g i = g i := by
  simp [piecewise, hi]
#align finset.piecewise_eq_of_not_mem Finset.piecewise_eq_of_not_mem

theorem piecewise_congr {f f' g g' : ∀ i, π i} (hf : ∀ i ∈ s, f i = f' i)
    (hg : ∀ i ∉ s, g i = g' i) : s.piecewise f g = s.piecewise f' g' :=
  funext fun i => if_ctx_congr Iff.rfl (hf i) (hg i)
#align finset.piecewise_congr Finset.piecewise_congr

@[simp]
theorem piecewise_insert_of_ne [DecidableEq ι] {i j : ι} [∀ i, Decidable (i ∈ insert j s)]
    (h : i ≠ j) : (insert j s).piecewise f g i = s.piecewise f g i := by simp [piecewise, h]
#align finset.piecewise_insert_of_ne Finset.piecewise_insert_of_ne

theorem piecewise_insert [DecidableEq ι] (j : ι) [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g = update (s.piecewise f g) j (f j) := by
  classical simp only [← piecewise_coe, coe_insert, ← Set.piecewise_insert]
  ext
  congr
  simp
#align finset.piecewise_insert Finset.piecewise_insert

theorem piecewise_cases {i} (p : π i → Prop) (hf : p (f i)) (hg : p (g i)) :
    p (s.piecewise f g i) := by
  by_cases hi : i ∈ s <;> simpa [hi]
#align finset.piecewise_cases Finset.piecewise_cases

theorem piecewise_singleton [DecidableEq ι] (i : ι) : piecewise {i} f g = update g i (f i) := by
  rw [← insert_emptyc_eq, piecewise_insert, piecewise_empty]
#align finset.piecewise_singleton Finset.piecewise_singleton

theorem piecewise_piecewise_of_subset_left {s t : Finset ι} [∀ i, Decidable (i ∈ s)]
    [∀ i, Decidable (i ∈ t)] (h : s ⊆ t) (f₁ f₂ g : ∀ a, π a) :
    s.piecewise (t.piecewise f₁ f₂) g = s.piecewise f₁ g :=
  s.piecewise_congr (fun _i hi => piecewise_eq_of_mem _ _ _ (h hi)) fun _ _ => rfl
#align finset.piecewise_piecewise_of_subset_left Finset.piecewise_piecewise_of_subset_left

@[simp]
theorem piecewise_idem_left (f₁ f₂ g : ∀ a, π a) :
    s.piecewise (s.piecewise f₁ f₂) g = s.piecewise f₁ g :=
  piecewise_piecewise_of_subset_left (Subset.refl _) _ _ _
#align finset.piecewise_idem_left Finset.piecewise_idem_left

theorem piecewise_piecewise_of_subset_right {s t : Finset ι} [∀ i, Decidable (i ∈ s)]
    [∀ i, Decidable (i ∈ t)] (h : t ⊆ s) (f g₁ g₂ : ∀ a, π a) :
    s.piecewise f (t.piecewise g₁ g₂) = s.piecewise f g₂ :=
  s.piecewise_congr (fun _ _ => rfl) fun _i hi => t.piecewise_eq_of_not_mem _ _ (mt (@h _) hi)
#align finset.piecewise_piecewise_of_subset_right Finset.piecewise_piecewise_of_subset_right

@[simp]
theorem piecewise_idem_right (f g₁ g₂ : ∀ a, π a) :
    s.piecewise f (s.piecewise g₁ g₂) = s.piecewise f g₂ :=
  piecewise_piecewise_of_subset_right (Subset.refl _) f g₁ g₂
#align finset.piecewise_idem_right Finset.piecewise_idem_right

theorem update_eq_piecewise {β : Type*} [DecidableEq ι] (f : ι → β) (i : ι) (v : β) :
    update f i v = piecewise (singleton i) (fun _ => v) f :=
  (piecewise_singleton (fun _ => v) _ _).symm
#align finset.update_eq_piecewise Finset.update_eq_piecewise

theorem update_piecewise [DecidableEq ι] (i : ι) (v : π i) :
    update (s.piecewise f g) i v = s.piecewise (update f i v) (update g i v) := by
  ext j
  rcases em (j = i) with (rfl | hj) <;> by_cases hs : j ∈ s <;> simp [*]
#align finset.update_piecewise Finset.update_piecewise

theorem update_piecewise_of_mem [DecidableEq ι] {i : ι} (hi : i ∈ s) (v : π i) :
    update (s.piecewise f g) i v = s.piecewise (update f i v) g := by
  rw [update_piecewise]
  refine' s.piecewise_congr (fun _ _ => rfl) fun j hj => update_noteq _ _ _
  exact fun h => hj (h.symm ▸ hi)
#align finset.update_piecewise_of_mem Finset.update_piecewise_of_mem

theorem update_piecewise_of_not_mem [DecidableEq ι] {i : ι} (hi : i ∉ s) (v : π i) :
    update (s.piecewise f g) i v = s.piecewise f (update g i v) := by
  rw [update_piecewise]
  refine' s.piecewise_congr (fun j hj => update_noteq _ _ _) fun _ _ => rfl
  exact fun h => hi (h ▸ hj)
#align finset.update_piecewise_of_not_mem Finset.update_piecewise_of_not_mem

lemma piecewise_same : s.piecewise f f = f := by
  ext i
  by_cases h : i ∈ s <;> simp [h]

section Fintype
variable [Fintype ι]

@[simp]
theorem piecewise_univ [∀ i, Decidable (i ∈ (univ : Finset ι))] (f g : ∀ i, π i) :
    univ.piecewise f g = f := by
  ext i
  simp [piecewise]
#align finset.piecewise_univ Finset.piecewise_univ

theorem piecewise_compl [DecidableEq ι] (s : Finset ι) [∀ i, Decidable (i ∈ s)]
    [∀ i, Decidable (i ∈ sᶜ)] (f g : ∀ i, π i) :
    sᶜ.piecewise f g = s.piecewise g f := by
  ext i
  simp [piecewise]
#align finset.piecewise_compl Finset.piecewise_compl

@[simp]
theorem piecewise_erase_univ [DecidableEq ι] (i : ι) (f g : ∀ i, π i) :
    (Finset.univ.erase i).piecewise f g = Function.update f i (g i) := by
  rw [← compl_singleton, piecewise_compl, piecewise_singleton]
#align finset.piecewise_erase_univ Finset.piecewise_erase_univ

end Fintype

variable {π : ι → Type*}

theorem piecewise_mem_set_pi {t : Set ι} {t' : ∀ i, Set (π i)} {f g}
    (hf : f ∈ Set.pi t t') (hg : g ∈ Set.pi t t') : s.piecewise f g ∈ Set.pi t t' := by
  classical
    rw [← piecewise_coe]
    exact Set.piecewise_mem_pi (↑s) hf hg
#align finset.piecewise_mem_set_pi Finset.piecewise_mem_set_pi

theorem piecewise_le_of_le_of_le [∀ i, Preorder (π i)] {f g h : ∀ i, π i}
    (Hf : f ≤ h) (Hg : g ≤ h) : s.piecewise f g ≤ h := fun x =>
  piecewise_cases s f g (· ≤ h x) (Hf x) (Hg x)
#align finset.piecewise_le_of_le_of_le Finset.piecewise_le_of_le_of_le

theorem le_piecewise_of_le_of_le [∀ i, Preorder (π i)] {f g h : ∀ i, π i}
    (Hf : h ≤ f) (Hg : h ≤ g) : h ≤ s.piecewise f g := fun x =>
  piecewise_cases s f g (fun y => h x ≤ y) (Hf x) (Hg x)
#align finset.le_piecewise_of_le_of_le Finset.le_piecewise_of_le_of_le

theorem piecewise_le_piecewise' [∀ i, Preorder (π i)] {f g f' g' : ∀ i, π i}
    (Hf : ∀ x ∈ s, f x ≤ f' x) (Hg : ∀ x ∉ s, g x ≤ g' x) :
    s.piecewise f g ≤ s.piecewise f' g' := fun x => by by_cases hx : x ∈ s <;> simp [hx, *]
#align finset.piecewise_le_piecewise' Finset.piecewise_le_piecewise'

theorem piecewise_le_piecewise [∀ i, Preorder (π i)] {f g f' g' : ∀ i, π i}
    (Hf : f ≤ f') (Hg : g ≤ g') : s.piecewise f g ≤ s.piecewise f' g' :=
  s.piecewise_le_piecewise' (fun x _ => Hf x) fun x _ => Hg x
#align finset.piecewise_le_piecewise Finset.piecewise_le_piecewise

theorem piecewise_mem_Icc_of_mem_of_mem [∀ i, Preorder (π i)]
    {f f₁ g g₁ : ∀ i, π i} (hf : f ∈ Set.Icc f₁ g₁) (hg : g ∈ Set.Icc f₁ g₁) :
    s.piecewise f g ∈ Set.Icc f₁ g₁ :=
  ⟨le_piecewise_of_le_of_le _ hf.1 hg.1, piecewise_le_of_le_of_le _ hf.2 hg.2⟩
#align finset.piecewise_mem_Icc_of_mem_of_mem Finset.piecewise_mem_Icc_of_mem_of_mem

theorem piecewise_mem_Icc [∀ i, Preorder (π i)] {f g : ∀ i, π i} (h : f ≤ g) :
    s.piecewise f g ∈ Set.Icc f g :=
  piecewise_mem_Icc_of_mem_of_mem _ (Set.left_mem_Icc.2 h) (Set.right_mem_Icc.2 h)
#align finset.piecewise_mem_Icc Finset.piecewise_mem_Icc

theorem piecewise_mem_Icc' [∀ i, Preorder (π i)] {f g : ∀ i, π i} (h : g ≤ f) :
    s.piecewise f g ∈ Set.Icc g f :=
  piecewise_mem_Icc_of_mem_of_mem _ (Set.right_mem_Icc.2 h) (Set.left_mem_Icc.2 h)
#align finset.piecewise_mem_Icc' Finset.piecewise_mem_Icc'

end Finset
