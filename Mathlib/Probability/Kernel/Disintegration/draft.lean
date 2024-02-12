import Mathlib.Probability.Kernel.Disintegration
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Kernel.Disintegration.BuildKernel

open MeasureTheory Set Filter

open scoped NNReal ENNReal MeasureTheory Topology ProbabilityTheory

namespace ProbabilityTheory

variable {α Ω : Type*} {mα : MeasurableSpace α}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]

section Real

section dissection_system

def I (n : ℕ) (k : ℤ) : Set ℝ := Set.Ico (k * (2⁻¹ : ℝ) ^ n) ((k + 1) * ((2 : ℝ) ^ n)⁻¹)

lemma mem_I_iff_mul {n : ℕ} {k : ℤ} (x : ℝ) : x ∈ I n k ↔ k ≤ x * 2 ^ n ∧ x * 2 ^ n < k + 1 := by
  simp only [I, inv_pow, mem_Ico]
  rw [← div_eq_mul_inv, div_le_iff, ← div_eq_mul_inv, lt_div_iff]
  · positivity
  · positivity

lemma mem_I_iff_floor {n : ℕ} {k : ℤ} (x : ℝ) : x ∈ I n k ↔ ⌊x * 2 ^ n⌋ = k := by
  simp [mem_I_iff_mul, Int.floor_eq_iff]

lemma measurableSet_I (n : ℕ) (k : ℤ) : MeasurableSet (I n k) := measurableSet_Ico

lemma Measure.iInf_Iic_gt_prod {ρ : Measure (α × ℝ)} [IsFiniteMeasure ρ]
    {s : Set α} (hs : MeasurableSet s) (t : ℚ) :
    ⨅ r : { r' : ℚ // t < r' }, ρ (s ×ˢ Iic (r : ℝ)) = ρ (s ×ˢ Iic (t : ℝ)) := by
  have h := Measure.iInf_IicSnd_gt ρ t hs
  simp_rw [Measure.IicSnd_apply ρ _ hs] at h
  rw [← h]

lemma pairwise_disjoint_I (n : ℕ) : Pairwise (Disjoint on fun k ↦ I n k) := by
  intro i j hij
  rw [Function.onFun, Set.disjoint_iff]
  intro x
  simp only [mem_inter_iff, mem_I_iff_floor, mem_empty_iff_false, and_imp, imp_false]
  intro hi hj
  rw [hi] at hj
  exact hij hj

lemma I_succ_union (n : ℕ) (k : ℤ) : I (n+1) (2 * k) ∪ I (n+1) (2 * k + 1) = I n k := by
  ext x
  cases lt_or_le x ((2 * k + 1) * ((2 : ℝ) ^ (n+1))⁻¹) with
  | inl h =>
    simp only [I, inv_pow, mem_Ico, Int.cast_mul, Int.int_cast_ofNat, Int.cast_add,
      Int.cast_one, mem_union, h, and_true, not_le.mpr h, false_and, or_false]
    have : x < (k + 1) * (2 ^ n)⁻¹ := by
      refine h.trans_le ?_
      rw [pow_add, pow_one, mul_inv, mul_comm _ 2⁻¹, ← mul_assoc]
      gcongr
      rw [add_mul, one_mul, mul_comm, ← mul_assoc, inv_mul_cancel two_ne_zero, one_mul]
      gcongr
      norm_num
    simp only [this, and_true]
    rw [pow_add, pow_one, mul_inv, mul_comm _ 2⁻¹, ← mul_assoc, mul_comm _ 2⁻¹, ← mul_assoc,
      inv_mul_cancel two_ne_zero, one_mul]
  | inr h =>
    simp only [I, inv_pow, mem_Ico, Int.cast_mul, Int.int_cast_ofNat, Int.cast_add,
      Int.cast_one, mem_union, not_lt.mpr h, and_false, h, true_and, false_or]
    have : k * (2 ^ n)⁻¹ ≤ x := by
      refine le_trans ?_ h
      rw [pow_add, pow_one, mul_inv, mul_comm _ 2⁻¹, ← mul_assoc, mul_comm _ 2⁻¹, mul_add,
        ← mul_assoc, inv_mul_cancel two_ne_zero, mul_one, one_mul, add_mul]
      simp only [le_add_iff_nonneg_right, gt_iff_lt, inv_pos, zero_lt_two,
        mul_nonneg_iff_of_pos_left, inv_nonneg]
      positivity
    simp only [this, true_and]
    rw [pow_add, pow_one, mul_inv, mul_comm _ 2⁻¹, ← mul_assoc, mul_comm _ 2⁻¹, add_assoc]
    norm_num
    rw [one_div, mul_add, ← mul_assoc, inv_mul_cancel two_ne_zero, one_mul]

-- todo : `Filtration` should be renamed to `filtration`
def ℱ : Filtration ℕ (borel ℝ) where
  seq := fun n ↦ MeasurableSpace.generateFrom {s | ∃ k, s = I n k}
  mono' := by
    refine monotone_nat_of_le_succ ?_
    intro n
    refine MeasurableSpace.generateFrom_le fun s ⟨k, hs⟩ ↦ ?_
    rw [hs, ← I_succ_union n k]
    refine MeasurableSet.union ?_ ?_
    · exact MeasurableSpace.measurableSet_generateFrom ⟨2 * k, rfl⟩
    · exact MeasurableSpace.measurableSet_generateFrom ⟨2 * k + 1, rfl⟩
  le' := fun n ↦ by
    refine MeasurableSpace.generateFrom_le fun s ⟨k, hs⟩ ↦ ?_
    rw [hs]
    exact measurableSet_I n k

lemma measurableSet_ℱ_I (n : ℕ) (k : ℤ) : MeasurableSet[ℱ n] (I n k) :=
  MeasurableSpace.measurableSet_generateFrom ⟨k, rfl⟩

noncomputable def indexI (n : ℕ) (t : ℝ) : ℤ := Int.floor (t * 2^n)

lemma mem_I_indexI (n : ℕ) (t : ℝ) : t ∈ I n (indexI n t) := by
  rw [indexI, I]
  simp only [inv_pow, mem_Ico]
  constructor
  · rw [← div_eq_mul_inv, div_le_iff]
    · exact Int.floor_le (t * 2 ^ n)
    · positivity
  · rw [← div_eq_mul_inv, lt_div_iff]
    · exact Int.lt_floor_add_one (t * 2 ^ n)
    · positivity

lemma indexI_of_mem (n : ℕ) (k : ℤ) (t : ℝ) (ht : t ∈ I n k) : indexI n t = k := by
  rw [indexI]
  simp only [I, inv_pow, mem_Ico, ← div_eq_mul_inv] at ht
  rw [div_le_iff, lt_div_iff] at ht
  · rw [Int.floor_eq_iff]
    exact ht
  · positivity
  · positivity

lemma mem_I_iff_indexI (n : ℕ) (k : ℤ) (t : ℝ) : t ∈ I n k ↔ indexI n t = k :=
  ⟨fun h ↦ indexI_of_mem n k t h, fun h ↦ h ▸ mem_I_indexI n t⟩

lemma measurable_indexI (n : ℕ) : Measurable[ℱ n] (indexI n) := by
  unfold indexI
  refine @measurable_to_countable' ℤ ℝ _ _ (ℱ n) _ (fun k ↦ ?_)
  have : (fun t ↦ ⌊t * (2 : ℝ) ^ n⌋) ⁻¹' {k} = I n k := by
    ext t
    simp only [mem_I_iff_floor, mem_preimage, mem_singleton_iff]
  rw [this]
  exact measurableSet_ℱ_I n k

lemma iUnion_I (n : ℕ) : ⋃ k, I n k = univ := by
  ext x
  simp only [mem_iUnion, mem_univ, iff_true]
  exact ⟨indexI n x, mem_I_indexI n x⟩

lemma indexI_le_indexI_iff (n : ℕ) (t x : ℝ) :
    indexI n t ≤ indexI n x ↔ ⌊t * 2 ^ n⌋ * (2 ^ n)⁻¹ ≤ x := by
  simp only [indexI._eq_1]
  rw [← div_eq_mul_inv, div_le_iff, Int.le_floor]
  positivity

lemma iUnion_ge_I (n : ℕ) (t : ℝ) :
    ⋃ (k) (_ : indexI n t ≤ k), I n k = Ici (⌊t * 2 ^ n⌋ * (2 ^ n)⁻¹ : ℝ) := by
  ext x
  simp [mem_I_iff_indexI, indexI_le_indexI_iff]

lemma iInter_biUnion_I (x : ℝ) : ⋂ n, ⋃ (k) (_ : indexI n x ≤ k), I n k = Ici x := by
  ext t
  simp [iUnion_ge_I]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra h_lt
    push_neg at h_lt
    --have h_pos : ∀ i, 0 < (2 : ℝ) ^ i := fun i ↦ by positivity
    --simp_rw [← div_eq_mul_inv, div_le_iff (h_pos _)] at h
    sorry
  · intro n
    refine le_trans ?_ h
    rw [← div_eq_mul_inv, div_le_iff]
    · exact Int.floor_le (x * 2 ^ n)
    · positivity

lemma iSup_ℱ : ⨆ n, ℱ n = borel ℝ := by
  refine le_antisymm ?_ ?_
  · rw [iSup_le_iff]
    exact ℱ.le
  · conv_lhs => rw [borel_eq_generateFrom_Ici ℝ]
    refine MeasurableSpace.generateFrom_le (fun s ⟨x, hx⟩ ↦ ?_)
    rw [← hx, ← iInter_biUnion_I x]
    refine MeasurableSet.iInter (fun n ↦ ?_)
    refine MeasurableSet.biUnion ?_ (fun k _ ↦ ?_)
    · exact to_countable _
    · exact le_iSup ℱ n _ (measurableSet_ℱ_I n k)

end dissection_system

variable {β : Type*} [MeasurableSpace β]

-- issue with the following: joint measurability
--noncomputable
--def M' (κ : kernel α (ℝ × β)) (a : α) (s : Set β) (n : ℕ) (t : ℝ) : ℝ≥0∞ :=
--  (((κ a).restrict (univ ×ˢ s)).fst.trim (ℱ.le n)).rnDeriv (((kernel.fst κ a)).trim (ℱ.le n)) t

noncomputable
def M (κ : kernel α (ℝ × β)) (a : α) (s : Set β) (n : ℕ) (t : ℝ) : ℝ :=
  (κ a (I n (indexI n t) ×ˢ s) / kernel.fst κ a (I n (indexI n t))).toReal

lemma m_def (κ : kernel α (ℝ × β)) (a : α) (s : Set β) (n : ℕ) :
    M κ a s n = fun t ↦ (κ a (I n (indexI n t) ×ˢ s) / kernel.fst κ a (I n (indexI n t))).toReal :=
  rfl

lemma measurable_m_aux (κ : kernel α (ℝ × β)) {s : Set β} (hs : MeasurableSet s) (n : ℕ) :
    Measurable (fun (p : α × ℝ) ↦
      κ p.1 (I n (indexI n p.2) ×ˢ s) / kernel.fst κ p.1 (I n (indexI n p.2))) := by
  change Measurable ((fun (p : α × ℤ) ↦
    κ p.1 (I n p.2 ×ˢ s) / kernel.fst κ p.1 (I n p.2)) ∘ (fun (p : α × ℝ) ↦ (p.1, indexI n p.2)))
  have h1 : Measurable (fun (p : α × ℤ) ↦ κ p.1 (I n p.2 ×ˢ s) / kernel.fst κ p.1 (I n p.2)) := by
    refine Measurable.div ?_ ?_
    · have h_swap : Measurable fun (p : ℤ × α) ↦ κ p.2 (I n p.1 ×ˢ s) := by
        refine measurable_uncurry_of_continuous_of_measurable
          (u := fun k a ↦ κ a (I n k ×ˢ s)) ?_ ?_
        · exact fun _ ↦ continuous_bot
        · exact fun _ ↦ kernel.measurable_coe _ ((measurableSet_I _ _).prod hs)
      change Measurable ((fun (p : ℤ × α) ↦ κ p.2 (I n p.1 ×ˢ s)) ∘ Prod.swap)
      exact h_swap.comp measurable_swap
    · have h_swap : Measurable fun (p : ℤ × α) ↦ kernel.fst κ p.2 (I n p.1) := by
        refine measurable_uncurry_of_continuous_of_measurable
          (u := fun k a ↦ kernel.fst κ a (I n k)) ?_ ?_
        · exact fun _ ↦ continuous_bot
        · exact fun _ ↦ kernel.measurable_coe _ (measurableSet_I _ _)
      change Measurable ((fun (p : ℤ × α) ↦ kernel.fst κ p.2 (I n p.1)) ∘ Prod.swap)
      exact h_swap.comp measurable_swap
  refine h1.comp (measurable_fst.prod_mk ?_)
  exact (Measurable.mono (measurable_indexI n) (ℱ.le n) le_rfl).comp measurable_snd

lemma measurable_m (κ : kernel α (ℝ × β)) {s : Set β} (hs : MeasurableSet s) (n : ℕ) :
    Measurable (fun (p : α × ℝ) ↦ M κ p.1 s n p.2) :=
  (measurable_m_aux κ hs n).ennreal_toReal

lemma measurable_m_left (κ : kernel α (ℝ × β)) {s : Set β} (hs : MeasurableSet s) (n : ℕ) (t : ℝ) :
    Measurable (fun a ↦ M κ a s n t) :=
  (measurable_m κ hs n).comp (measurable_id.prod_mk measurable_const)

lemma measurable_m_right (κ : kernel α (ℝ × β)) {s : Set β} (a : α) (hs : MeasurableSet s) (n : ℕ) :
    Measurable (M κ a s n) :=
  (measurable_m κ hs n).comp (measurable_const.prod_mk measurable_id)

lemma measurable_ℱ_m (κ : kernel α (ℝ × β)) (a : α) (s : Set β) (n : ℕ) :
    Measurable[ℱ n] (M κ a s n) := by
  rw [m_def]
  refine @Measurable.ennreal_toReal _ (ℱ n) _ ?_
  refine Measurable.div ?_ ?_
  · change Measurable[ℱ n] ((fun k ↦ κ a (I n k ×ˢ s)) ∘ (indexI n))
    refine Measurable.comp ?_ (measurable_indexI n)
    exact measurable_of_countable _
  · change Measurable[ℱ n] ((fun k ↦ (kernel.fst κ) a (I n k)) ∘ (indexI n))
    refine Measurable.comp ?_ (measurable_indexI n)
    exact measurable_of_countable _

lemma stronglyMeasurable_ℱ_m (κ : kernel α (ℝ × β)) (a : α) (s : Set β) (n : ℕ) :
    StronglyMeasurable[ℱ n] (M κ a s n) :=
  (measurable_ℱ_m κ a s n).stronglyMeasurable

lemma adapted_m (κ : kernel α (ℝ × β)) (a : α) (s : Set β) : Adapted ℱ (M κ a s) :=
  stronglyMeasurable_ℱ_m κ a s

lemma m_nonneg (κ : kernel α (ℝ × β)) (a : α) (s : Set β) (n : ℕ) (t : ℝ) :
    0 ≤ M κ a s n t :=
  ENNReal.toReal_nonneg

lemma m_le_one (κ : kernel α (ℝ × β)) (a : α) (s : Set β) (n : ℕ) (t : ℝ) :
    M κ a s n t ≤ 1 := by
  rw [M]
  refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
  rw [ENNReal.ofReal_one]
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_mul, kernel.fst_apply' _ _ (measurableSet_I _ _)]
  refine measure_mono (fun x ↦ ?_)
  simp only [mem_prod, mem_setOf_eq, and_imp]
  exact fun h _ ↦ h

lemma snorm_m_le_one (κ : kernel α (ℝ × β)) [IsMarkovKernel (kernel.fst κ)]
    (a : α) (s : Set β) (n : ℕ) :
    snorm (M κ a s n) 1 (kernel.fst κ a) ≤ 1 := by
  refine (snorm_le_of_ae_bound (C := 1) (ae_of_all _ (fun x ↦ ?_))).trans ?_
  · simp only [Real.norm_eq_abs, abs_of_nonneg (m_nonneg κ a s n x), m_le_one κ a s n x]
  · simp

lemma integrable_m (κ : kernel α (ℝ × β)) [IsMarkovKernel (kernel.fst κ)]
    (a : α) {s : Set β} (hs : MeasurableSet s) (n : ℕ) :
    Integrable (M κ a s n) (kernel.fst κ a) := by
  rw [← memℒp_one_iff_integrable]
  refine ⟨Measurable.aestronglyMeasurable ?_, ?_⟩
  · exact measurable_m_right κ a hs n
  · exact (snorm_m_le_one κ a s n).trans_lt ENNReal.one_lt_top

lemma set_integral_m_I (κ : kernel α (ℝ × β)) [IsFiniteKernel κ]
    (a : α) {s : Set β} (hs : MeasurableSet s) (n : ℕ) (k : ℤ) :
    ∫ t in I n k, M κ a s n t ∂(kernel.fst κ a) = (κ a (I n k ×ˢ s)).toReal := by
  simp_rw [M]
  rw [integral_toReal]
  rotate_left
  · refine Measurable.aemeasurable ?_
    have h := measurable_m_aux κ hs n
    change Measurable
      ((fun (p : α × ℝ) ↦ κ p.1 (I n (indexI n p.2) ×ˢ s) / kernel.fst κ p.1 (I n (indexI n p.2)))
        ∘ (fun t ↦ (a, t)))
    exact h.comp measurable_prod_mk_left
  · refine ae_of_all _ (fun t ↦ ?_)
    by_cases h0 : kernel.fst κ a (I n (indexI n t)) = 0
    · suffices κ a (I n (indexI n t) ×ˢ s) = 0 by simp [h0, this]
      rw [kernel.fst_apply' _ _ (measurableSet_I _ _)] at h0
      refine measure_mono_null (fun x ↦ ?_) h0
      simp only [mem_prod, mem_setOf_eq, and_imp]
      exact fun h _ ↦ h
    · refine ENNReal.div_lt_top ?_ h0
      exact measure_ne_top _ _
  congr
  have : ∫⁻ t in I n k, κ a (I n (indexI n t) ×ˢ s)
                        / kernel.fst κ a (I n (indexI n t)) ∂(kernel.fst κ) a
      = ∫⁻ _ in I n k, κ a (I n k ×ˢ s) / kernel.fst κ a (I n k) ∂(kernel.fst κ) a := by
    refine set_lintegral_congr_fun (measurableSet_I _ _) (ae_of_all _ (fun t ht ↦ ?_))
    rw [indexI_of_mem _ _ _ ht]
  rw [this]
  simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter]
  by_cases h0 : kernel.fst κ a (I n k) = 0
  · simp only [h0, mul_zero]
    rw [kernel.fst_apply' _ _ (measurableSet_I _ _)] at h0
    refine (measure_mono_null ?_ h0).symm
    intro p
    simp only [mem_prod, mem_setOf_eq, and_imp]
    exact fun h _ ↦ h
  rw [div_eq_mul_inv, mul_assoc, ENNReal.inv_mul_cancel h0, mul_one]
  exact measure_ne_top _ _

lemma integral_m (κ : kernel α (ℝ × β)) [IsMarkovKernel κ]
    (a : α) {s : Set β} (hs : MeasurableSet s) (n : ℕ) :
    ∫ t, M κ a s n t ∂(kernel.fst κ a) = (κ a (univ ×ˢ s)).toReal := by
  rw [← integral_univ, ← iUnion_I n, iUnion_prod_const, measure_iUnion]
  rotate_left
  · intro i j hij
    simp only [Set.disjoint_prod, disjoint_self, bot_eq_empty]
    exact Or.inl (pairwise_disjoint_I n hij)
  · exact fun k ↦ (measurableSet_I n k).prod hs
  rw [integral_iUnion (measurableSet_I n) (pairwise_disjoint_I n)
    (integrable_m κ a hs n).integrableOn]
  rw [ENNReal.tsum_toReal_eq (fun _ ↦ measure_ne_top _ _)]
  congr with k
  rw [set_integral_m_I _ _ hs]

lemma set_integral_m (κ : kernel α (ℝ × β)) [IsMarkovKernel κ]
    (a : α) {s : Set β} (hs : MeasurableSet s) (n : ℕ) {A : Set ℝ} (hA : MeasurableSet[ℱ n] A) :
    ∫ t in A, M κ a s n t ∂(kernel.fst κ a) = (κ a (A ×ˢ s)).toReal := by
  refine MeasurableSpace.induction_on_inter (m := ℱ n) (s := {s | ∃ k, s = I n k})
    (C := fun A ↦ ∫ t in A, M κ a s n t ∂(kernel.fst κ a) = (κ a (A ×ˢ s)).toReal) rfl
    ?_ ?_ ?_ ?_ ?_ hA
  · rintro s ⟨i, rfl⟩ t ⟨j, rfl⟩ hst
    refine ⟨i, ?_⟩
    suffices i = j by rw [this, inter_self]
    by_contra h_ne
    have h_disj := pairwise_disjoint_I n h_ne
    rw [nonempty_iff_ne_empty] at hst
    refine hst ?_
    rwa [Function.onFun, disjoint_iff_inter_eq_empty] at h_disj
  · simp
  · rintro _ ⟨k, rfl⟩
    rw [set_integral_m_I _ _ hs]
  · intro A hA hA_eq
    have hA' : MeasurableSet A := ℱ.le _ _ hA
    have h := integral_add_compl hA' (integrable_m κ a hs n)
    rw [hA_eq, integral_m κ a hs] at h
    have : Aᶜ ×ˢ s = univ ×ˢ s \ A ×ˢ s := by
      rw [prod_diff_prod, compl_eq_univ_diff]
      simp
    rw [this, measure_diff (by intro x; simp) (hA'.prod hs) (measure_ne_top (κ a) _),
      ENNReal.toReal_sub_of_le (measure_mono (by intro x; simp)) (measure_ne_top _ _)]
    rw [eq_tsub_iff_add_eq_of_le, add_comm]
    · exact h
    · rw [ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)]
      exact measure_mono (by intro x; simp)
  · intro f hf_disj hf h_eq
    rw [integral_iUnion (fun i ↦ ℱ.le n _ (hf i)) hf_disj (integrable_m κ _ hs _).integrableOn]
    simp_rw [h_eq]
    rw [iUnion_prod_const, measure_iUnion _ (fun i ↦ (ℱ.le n _ (hf i)).prod hs)]
    · rw [ENNReal.tsum_toReal_eq]
      exact fun _ ↦ measure_ne_top _ _
    · intro i j hij
      rw [Function.onFun, Set.disjoint_prod]
      exact Or.inl (hf_disj hij)

lemma set_integral_m_of_le (κ : kernel α (ℝ × β)) [IsMarkovKernel κ]
    (a : α) {s : Set β} (hs : MeasurableSet s) {n m : ℕ} (hnm : n ≤ m)
    {A : Set ℝ} (hA : MeasurableSet[ℱ n] A) :
    ∫ t in A, M κ a s m t ∂(kernel.fst κ a) = (κ a (A ×ˢ s)).toReal :=
  set_integral_m κ a hs m (ℱ.mono hnm A hA)

lemma condexp_m (κ : kernel α (ℝ × β)) [IsMarkovKernel κ] (a : α) {s : Set β}
    (hs : MeasurableSet s) {i j : ℕ} (hij : i ≤ j) :
    (kernel.fst κ a)[M κ a s j | ℱ i] =ᵐ[kernel.fst κ a] M κ a s i := by
  symm
  refine ae_eq_condexp_of_forall_set_integral_eq ?_ ?_ ?_ ?_ ?_
  · exact integrable_m κ a hs j
  · refine fun t _ _ ↦ Integrable.integrableOn ?_
    exact integrable_m κ _ hs _
  · intro t ht _
    rw [set_integral_m κ a hs i ht, set_integral_m_of_le κ a hs hij ht]
  · exact StronglyMeasurable.aeStronglyMeasurable' (stronglyMeasurable_ℱ_m κ a s i)

lemma martingale_m (κ : kernel α (ℝ × β)) [IsMarkovKernel κ] (a : α) {s : Set β}
    (hs : MeasurableSet s) :
    Martingale (M κ a s) ℱ (kernel.fst κ a) :=
  ⟨adapted_m κ a s, fun _ _ ↦ condexp_m κ a hs⟩

lemma m_mono_set (κ : kernel α (ℝ × β)) (a : α) {s s' : Set β} (h : s ⊆ s') (n : ℕ) (t : ℝ) :
    M κ a s n t ≤ M κ a s' n t := by
  have h_ne_top : ∀ s, κ a (I n (indexI n t) ×ˢ s) / kernel.fst κ a (I n (indexI n t)) ≠ ⊤ := by
    intro s
    rw [ne_eq, ENNReal.div_eq_top]
    push_neg
    simp_rw [kernel.fst_apply' _ _ (measurableSet_I _ _)]
    constructor
    · refine fun h h0 ↦ h (measure_mono_null (fun x ↦ ?_) h0)
      simp only [mem_prod, mem_setOf_eq, and_imp]
      exact fun h _ ↦ h
    · refine fun h_top ↦ eq_top_mono (measure_mono (fun x ↦ ?_)) h_top
      simp only [mem_prod, mem_setOf_eq, and_imp]
      exact fun h _ ↦ h
  rw [M, M, ENNReal.toReal_le_toReal]
  · gcongr
    rw [prod_subset_prod_iff]
    simp [subset_rfl, h]
  · exact h_ne_top s
  · exact h_ne_top s'

lemma m_univ (κ : kernel α (ℝ × β)) [IsFiniteKernel κ] (a : α) (n : ℕ) (t : ℝ) :
    M κ a univ n t = if kernel.fst κ a (I n (indexI n t)) = 0 then 0 else 1 := by
  rw [M]
  by_cases h : kernel.fst κ a (I n (indexI n t)) = 0
  · simp [h]
    by_cases h' : κ a (I n (indexI n t) ×ˢ univ) = 0
    · simp [h']
    · rw [ENNReal.div_zero h']
      simp
  · simp only [h, ite_false]
    rw [kernel.fst_apply' _ _ (measurableSet_I _ _)]
    have : I n (indexI n t) ×ˢ univ = {p : ℝ × β | p.1 ∈ I n (indexI n t)} := by
      ext x
      simp
    rw [this, ENNReal.div_self]
    · simp
    · rwa [kernel.fst_apply' _ _ (measurableSet_I _ _)] at h
    · exact measure_ne_top _ _

lemma m_empty (κ : kernel α (ℝ × β)) (a : α) (n : ℕ) (t : ℝ) :
    M κ a ∅ n t = 0 := by
  rw [M]
  simp

lemma m_univ_ae (κ : kernel α (ℝ × β)) [IsFiniteKernel κ] (a : α) (n : ℕ) :
    ∀ᵐ t ∂(kernel.fst κ a), M κ a univ n t = 1 := by
  rw [ae_iff]
  have : {t | ¬ M κ a univ n t = 1} ⊆ {t | kernel.fst κ a (I n (indexI n t)) = 0} := by
    intro t ht
    simp only [mem_setOf_eq] at ht ⊢
    rw [m_univ] at ht
    simpa using ht
  refine measure_mono_null this ?_
  have : {t | kernel.fst κ a (I n (indexI n t)) = 0}
      ⊆ ⋃ (k) (_ : kernel.fst κ a (I n k) = 0), I n k := by
    intro t
    simp only [mem_setOf_eq, mem_iUnion, exists_prop]
    intro ht
    exact ⟨indexI n t, ht, mem_I_indexI _ _⟩
  refine measure_mono_null this ?_
  rw [measure_iUnion_null]
  intro i
  simp

lemma tendsto_m_atTop_univ_of_monotone (κ : kernel α (ℝ × β))
    (a : α) (s : ℕ → Set β) (hs : Monotone s) (hs_iUnion : ⋃ i, s i = univ) (n : ℕ) (t : ℝ) :
    Tendsto (fun m ↦ M κ a (s m) n t) atTop (𝓝 (M κ a univ n t)) := by
  simp_rw [M]
  refine (ENNReal.tendsto_toReal ?_).comp ?_
  · rw [ne_eq, ENNReal.div_eq_top]
    push_neg
    simp_rw [kernel.fst_apply' _ _ (measurableSet_I _ _)]
    constructor
    · refine fun h h0 ↦ h (measure_mono_null (fun x ↦ ?_) h0)
      simp only [mem_prod, mem_setOf_eq, and_imp]
      exact fun h _ ↦ h
    · refine fun h_top ↦ eq_top_mono (measure_mono (fun x ↦ ?_)) h_top
      simp only [mem_prod, mem_setOf_eq, and_imp]
      exact fun h _ ↦ h
  by_cases h0 : kernel.fst κ a (I n (indexI n t)) = 0
  · rw [kernel.fst_apply' _ _ (measurableSet_I _ _)] at h0 ⊢
    suffices ∀ m, κ a (I n (indexI n t) ×ˢ s m) = 0 by
      simp only [this, h0, ENNReal.zero_div, tendsto_const_nhds_iff]
      suffices κ a (I n (indexI n t) ×ˢ univ) = 0 by simp only [this, ENNReal.zero_div]
      convert h0
      ext x
      simp only [mem_prod, mem_univ, and_true, mem_setOf_eq]
    refine fun m ↦ measure_mono_null (fun x ↦ ?_) h0
    simp only [mem_prod, mem_setOf_eq, and_imp]
    exact fun h _ ↦ h
  refine ENNReal.Tendsto.div_const ?_ ?_
  · have h := tendsto_measure_iUnion (μ := κ a) (s := fun m ↦ I n (indexI n t) ×ˢ s m) ?_
    swap
    · intro m m' hmm'
      simp only [le_eq_subset, prod_subset_prod_iff, subset_rfl, true_and]
      exact Or.inl <| hs hmm'
    convert h
    rw [← prod_iUnion, hs_iUnion]
  · exact Or.inr h0

lemma tendsto_m_atTop_ae_of_monotone (κ : kernel α (ℝ × β)) [IsFiniteKernel κ]
    (a : α) (s : ℕ → Set β) (hs : Monotone s) (hs_iUnion : ⋃ i, s i = univ) (n : ℕ) :
    ∀ᵐ t ∂(kernel.fst κ a), Tendsto (fun m ↦ M κ a (s m) n t) atTop (𝓝 1) := by
  filter_upwards [m_univ_ae κ a n] with t ht
  rw [← ht]
  exact tendsto_m_atTop_univ_of_monotone κ a s hs hs_iUnion n t

lemma tendsto_m_atTop_empty_of_antitone (κ : kernel α (ℝ × β)) [IsFiniteKernel κ]
    (a : α) (s : ℕ → Set β) (hs : Antitone s) (hs_iInter : ⋂ i, s i = ∅)
    (hs_meas : ∀ n, MeasurableSet (s n)) (n : ℕ) (t : ℝ) :
    Tendsto (fun m ↦ M κ a (s m) n t) atTop (𝓝 (M κ a ∅ n t)) := by
  simp_rw [M]
  refine (ENNReal.tendsto_toReal ?_).comp ?_
  · rw [ne_eq, ENNReal.div_eq_top]
    push_neg
    simp
  by_cases h0 : kernel.fst κ a (I n (indexI n t)) = 0
  · simp only [h0, prod_empty, OuterMeasure.empty', ENNReal.zero_div]
    have : ∀ m, (κ a) (I n (indexI n t) ×ˢ s m) = 0 := by
      intro m
      rw [kernel.fst_apply' _ _ (measurableSet_I _ _)] at h0
      refine measure_mono_null ?_ h0
      intro x hx
      rw [mem_prod] at hx
      exact hx.1
    simp [this]
  refine ENNReal.Tendsto.div_const ?_ ?_
  · have h := tendsto_measure_iInter (μ := κ a) (s := fun m ↦ I n (indexI n t) ×ˢ s m) ?_ ?_ ?_
    · convert h
      rw [← prod_iInter, hs_iInter]
    · exact fun n ↦ MeasurableSet.prod (measurableSet_I _ _) (hs_meas n)
    · intro m m' hmm'
      simp only [le_eq_subset, prod_subset_prod_iff, subset_rfl, true_and]
      exact Or.inl <| hs hmm'
    · exact ⟨0, measure_ne_top _ _⟩
  · simp only [prod_empty, OuterMeasure.empty', ne_eq, not_true_eq_false, false_or, h0,
      not_false_iff]

lemma tendsto_m_atTop_of_antitone (κ : kernel α (ℝ × β)) [IsFiniteKernel κ]
    (a : α) (s : ℕ → Set β) (hs : Antitone s) (hs_iInter : ⋂ i, s i = ∅)
    (hs_meas : ∀ n, MeasurableSet (s n)) (n : ℕ) (t : ℝ) :
    Tendsto (fun m ↦ M κ a (s m) n t) atTop (𝓝 0) := by
  rw [← m_empty κ a n t]
  exact tendsto_m_atTop_empty_of_antitone κ a s hs hs_iInter hs_meas n t

lemma tendsto_m_limitProcess (κ : kernel α (ℝ × β)) (a : α) [IsMarkovKernel κ]
    {s : Set β} (hs : MeasurableSet s) :
    ∀ᵐ t ∂(kernel.fst κ a),
      Tendsto (fun n ↦ M κ a s n t) atTop (𝓝 (ℱ.limitProcess (M κ a s) (kernel.fst κ a) t)) := by
  refine Submartingale.ae_tendsto_limitProcess (martingale_m κ a hs).submartingale (R := 1) ?_
  intro n
  rw [ENNReal.coe_one]
  exact snorm_m_le_one κ a s n

lemma limitProcess_mem_L1 (κ : kernel α (ℝ × β)) [IsMarkovKernel κ]
    (a : α) {s : Set β} (hs : MeasurableSet s) :
    Memℒp (ℱ.limitProcess (M κ a s) (kernel.fst κ a)) 1 (kernel.fst κ a) := by
  refine Submartingale.memℒp_limitProcess (martingale_m κ a hs).submartingale (R := 1) ?_
  intro n
  rw [ENNReal.coe_one]
  exact snorm_m_le_one κ a s n

lemma tendsto_snorm_one_m_limitProcess (κ : kernel α (ℝ × β)) (a : α) [IsMarkovKernel κ]
    {s : Set β} (hs : MeasurableSet s) :
    Tendsto
      (fun n ↦ snorm (M κ a s n - ℱ.limitProcess (M κ a s) (kernel.fst κ a)) 1 (kernel.fst κ a))
      atTop (𝓝 0) := by
  refine Submartingale.tendsto_snorm_one_limitProcess ?_ ?_
  · exact (martingale_m κ a hs).submartingale
  · refine uniformIntegrable_of le_rfl ENNReal.one_ne_top ?_ ?_
    · exact fun n ↦ (measurable_m_right κ a hs n).aestronglyMeasurable
    · intro ε _
      refine ⟨2, fun n ↦ ?_⟩
      refine le_of_eq_of_le ?_ (?_ : 0 ≤ ENNReal.ofReal ε)
      · have : {x | 2 ≤ ‖M κ a s n x‖₊} = ∅ := by
          ext x
          simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
          refine (?_ : _ ≤ (1 : ℝ≥0)).trans_lt one_lt_two
          rw [Real.nnnorm_of_nonneg (m_nonneg _ _ _ _ _)]
          exact mod_cast (m_le_one _ _ _ _ _)
        rw [this]
        simp
      · simp

lemma snorm_restrict_le [NormedAddCommGroup β] {p : ℝ≥0∞} {f : α → β} {μ : Measure α} (s : Set α) :
    snorm f p (μ.restrict s) ≤ snorm f p μ :=
  snorm_mono_measure f Measure.restrict_le_self

lemma tendsto_snorm_restrict_zero {α β ι : Type*} {mα : MeasurableSpace α} [NormedAddCommGroup β]
    {p : ℝ≥0∞} {f : ι → α → β} {μ : Measure α} {l : Filter ι}
    (h : Tendsto (fun n ↦ snorm (f n) p μ) l (𝓝 0)) (s : Set α) :
    Tendsto (fun n ↦ snorm (f n) p (μ.restrict s)) l (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h ?_ ?_
  · exact fun _ ↦ zero_le _
  · exact fun _ ↦ snorm_restrict_le _

lemma tendsto_snorm_one_restrict_m_limitProcess (κ : kernel α (ℝ × β)) (a : α) [IsMarkovKernel κ]
    {s : Set β} (hs : MeasurableSet s) (A : Set ℝ) :
    Tendsto (fun n ↦ snorm (M κ a s n - ℱ.limitProcess (M κ a s) (kernel.fst κ a)) 1
        ((kernel.fst κ a).restrict A))
      atTop (𝓝 0) :=
  tendsto_snorm_restrict_zero (tendsto_snorm_one_m_limitProcess κ a hs) A

noncomputable
def MLimsup (κ : kernel α (ℝ × β)) (a : α) (s : Set β) (t : ℝ) : ℝ :=
  limsup (fun n ↦ M κ a s n t) atTop

lemma mLimsup_ae_eq_limitProcess (κ : kernel α (ℝ × β)) [IsMarkovKernel κ]
    (a : α) {s : Set β} (hs : MeasurableSet s) :
    MLimsup κ a s =ᵐ[kernel.fst κ a] ℱ.limitProcess (M κ a s) (kernel.fst κ a) := by
  filter_upwards [tendsto_m_limitProcess κ a hs] with t ht using ht.limsup_eq

lemma tendsto_m_mLimsup (κ : kernel α (ℝ × β)) (a : α) [IsMarkovKernel κ]
    {s : Set β} (hs : MeasurableSet s) :
    ∀ᵐ t ∂(kernel.fst κ a),
      Tendsto (fun n ↦ M κ a s n t) atTop (𝓝 (MLimsup κ a s t)) := by
  filter_upwards [tendsto_m_limitProcess κ a hs, mLimsup_ae_eq_limitProcess κ a hs] with t h1 h2
  rw [h2]
  exact h1

lemma measurable_mLimsup (κ : kernel α (ℝ × β)) {s : Set β} (hs : MeasurableSet s) :
    Measurable (fun (p : α × ℝ) ↦ MLimsup κ p.1 s p.2) :=
  measurable_limsup (fun n ↦ measurable_m κ hs n)

lemma measurable_mLimsup_left (κ : kernel α (ℝ × β)) {s : Set β} (hs : MeasurableSet s) (t : ℝ) :
    Measurable (fun a ↦ MLimsup κ a s t) := by
  change Measurable ((fun (p : α × ℝ) ↦ MLimsup κ p.1 s p.2) ∘ (fun a ↦ (a, t)))
  exact (measurable_mLimsup κ hs).comp (measurable_id.prod_mk measurable_const)

lemma measurable_mLimsup_right (κ : kernel α (ℝ × β)) {s : Set β} (hs : MeasurableSet s) (a : α) :
    Measurable (MLimsup κ a s) := by
  change Measurable ((fun (p : α × ℝ) ↦ MLimsup κ p.1 s p.2) ∘ (fun t ↦ (a, t)))
  exact (measurable_mLimsup κ hs).comp (measurable_const.prod_mk measurable_id)

lemma mLimsup_mono_set (κ : kernel α (ℝ × β)) (a : α) {s s' : Set β} (h : s ⊆ s') (t : ℝ) :
    MLimsup κ a s t ≤ MLimsup κ a s' t := by
  rw [MLimsup, MLimsup]
  refine limsup_le_limsup ?_ ?_ ?_
  · exact eventually_of_forall (fun n ↦ m_mono_set κ a h n t)
  · -- todo: extract lemma (of find it)
    refine ⟨0, ?_⟩
    simp only [eventually_map, eventually_atTop, ge_iff_le, forall_exists_index]
    intro x n h
    specialize h n le_rfl
    exact (m_nonneg _ _ _ _ _).trans h
  · -- todo: extract lemma (of find it)
    refine ⟨1, ?_⟩
    simp only [eventually_map, eventually_atTop, ge_iff_le]
    exact ⟨0, fun n _ ↦ m_le_one _ _ _ _ _⟩

lemma mLimsup_nonneg (κ : kernel α (ℝ × β)) (a : α) (s : Set β) (t : ℝ) :
    0 ≤ MLimsup κ a s t := by
  refine le_limsup_of_frequently_le ?_ ?_
  · exact frequently_of_forall (fun n ↦ m_nonneg _ _ _ _ _)
  · -- todo: extract lemma (of find it)
    refine ⟨1, ?_⟩
    simp only [eventually_map, eventually_atTop, ge_iff_le]
    exact ⟨0, fun n _ ↦ m_le_one _ _ _ _ _⟩

lemma mLimsup_le_one (κ : kernel α (ℝ × β)) (a : α) (s : Set β) (t : ℝ) :
    MLimsup κ a s t ≤ 1 := by
  refine limsup_le_of_le ?_ ?_
  · -- todo: extract lemma (of find it)
    refine ⟨0, ?_⟩
    simp only [eventually_map, eventually_atTop, ge_iff_le, forall_exists_index]
    intro x n h
    specialize h n le_rfl
    exact (m_nonneg _ _ _ _ _).trans h
  · exact eventually_of_forall (fun n ↦ m_le_one _ _ _ _ _)

lemma mLimsup_univ (κ : kernel α (ℝ × β)) [IsFiniteKernel κ] (a : α) :
    ∀ᵐ t ∂(kernel.fst κ a), MLimsup κ a Set.univ t = 1 := by
  have h := m_univ_ae κ a
  rw [← ae_all_iff] at h
  filter_upwards [h] with t ht
  rw [MLimsup]
  simp_rw [ht]
  rw [limsup_const] -- should be simp

lemma snorm_mLimsup_le_one (κ : kernel α (ℝ × β)) [IsMarkovKernel (kernel.fst κ)]
    (a : α) (s : Set β) :
    snorm (fun t ↦ MLimsup κ a s t) 1 (kernel.fst κ a) ≤ 1 := by
  refine (snorm_le_of_ae_bound (C := 1) (ae_of_all _ (fun t ↦ ?_))).trans ?_
  · simp only [Real.norm_eq_abs, abs_of_nonneg (mLimsup_nonneg κ a s t),
      mLimsup_le_one κ a s t]
  · simp

lemma integrable_mLimsup (κ : kernel α (ℝ × β)) [IsMarkovKernel (kernel.fst κ)]
    (a : α) {s : Set β} (hs : MeasurableSet s) :
    Integrable (fun t ↦ MLimsup κ a s t) (kernel.fst κ a) := by
  rw [← memℒp_one_iff_integrable]
  refine ⟨Measurable.aestronglyMeasurable ?_, ?_⟩
  · exact measurable_mLimsup_right κ hs a
  · exact (snorm_mLimsup_le_one κ a s).trans_lt ENNReal.one_lt_top

lemma tendsto_integral_of_L1' {ι G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {μ : Measure α}
    (f : α → G) (hfi : Integrable f μ)
    {F : ι → α → G} {l : Filter ι}
    (hFi : ∀ᶠ i in l, Integrable (F i) μ)
    (hF : Tendsto (fun i ↦ snorm (F i - f) 1 μ) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ x, F i x ∂μ) l (𝓝 (∫ x, f x ∂μ)) := by
  refine tendsto_integral_of_L1 f hfi hFi ?_
  simp_rw [snorm_one_eq_lintegral_nnnorm, Pi.sub_apply] at hF
  exact hF

lemma tendsto_set_integral_of_L1 {ι G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {μ : Measure α}
    (f : α → G) (hfi : Integrable f μ)
    {F : ι → α → G} {l : Filter ι}
    (hFi : ∀ᶠ i in l, Integrable (F i) μ)
    (hF : Tendsto (fun i ↦ ∫⁻ x, ‖F i x - f x‖₊ ∂μ) l (𝓝 0)) (s : Set α) :
    Tendsto (fun i ↦ ∫ x in s, F i x ∂μ) l (𝓝 (∫ x in s, f x ∂μ)) := by
  refine tendsto_integral_of_L1 f hfi.restrict ?_ ?_
  · filter_upwards [hFi] with i hi using hi.restrict
  · simp_rw [← snorm_one_eq_lintegral_nnnorm] at hF ⊢
    exact tendsto_snorm_restrict_zero hF s

lemma tendsto_set_integral_of_L1' {ι G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {μ : Measure α}
    (f : α → G) (hfi : Integrable f μ)
    {F : ι → α → G} {l : Filter ι}
    (hFi : ∀ᶠ i in l, Integrable (F i) μ)
    (hF : Tendsto (fun i ↦ snorm (F i - f) 1 μ) l (𝓝 0)) (s : Set α) :
    Tendsto (fun i ↦ ∫ x in s, F i x ∂μ) l (𝓝 (∫ x in s, f x ∂μ)) := by
  refine tendsto_set_integral_of_L1 f hfi hFi ?_ s
  simp_rw [snorm_one_eq_lintegral_nnnorm, Pi.sub_apply] at hF
  exact hF

lemma tendsto_set_integral_m (κ : kernel α (ℝ × β)) [IsMarkovKernel κ]
    (a : α) {s : Set β} (hs : MeasurableSet s) (A : Set ℝ) :
    Tendsto (fun i ↦ ∫ x in A, M κ a s i x ∂(kernel.fst κ) a) atTop
      (𝓝 (∫ x in A, MLimsup κ a s x ∂(kernel.fst κ) a)) := by
  refine tendsto_set_integral_of_L1' (μ := kernel.fst κ a) (MLimsup κ a s)
    (integrable_mLimsup κ a hs) (F := fun i t ↦ M κ a s i t) (l := atTop)
    (eventually_of_forall (fun n ↦ integrable_m _ _ hs _)) ?_ A
  refine (tendsto_congr fun n ↦ ?_).mp (tendsto_snorm_one_m_limitProcess κ a hs)
  refine snorm_congr_ae ?_
  refine EventuallyEq.sub EventuallyEq.rfl ?_
  exact (mLimsup_ae_eq_limitProcess κ a hs).symm

lemma set_integral_mLimsup_of_measurableSet (κ : kernel α (ℝ × β)) [IsMarkovKernel κ]
    (a : α) {s : Set β} (hs : MeasurableSet s) (n : ℕ)
    {A : Set ℝ} (hA : MeasurableSet[ℱ n] A) :
    ∫ t in A, MLimsup κ a s t ∂(kernel.fst κ a) = (κ a (A ×ˢ s)).toReal := by
  suffices ∫ t in A, MLimsup κ a s t ∂(kernel.fst κ a) = ∫ t in A, M κ a s n t ∂(kernel.fst κ a) by
    rw [this]
    exact set_integral_m _ _ hs _ hA
  suffices ∫ t in A, MLimsup κ a s t ∂(kernel.fst κ a)
      = limsup (fun i ↦ ∫ t in A, M κ a s i t ∂(kernel.fst κ a)) atTop by
    rw [this, ← limsup_const (α := ℕ) (f := atTop) (∫ t in A, M κ a s n t ∂(kernel.fst κ a)),
      limsup_congr]
    simp only [eventually_atTop, ge_iff_le]
    refine ⟨n, fun m hnm ↦ ?_⟩
    rw [set_integral_m_of_le _ _ hs hnm hA, set_integral_m _ _ hs _ hA]
  -- use L1 convergence
  have h := tendsto_set_integral_m κ a hs A
  rw [h.limsup_eq]

lemma integral_mLimsup (κ : kernel α (ℝ × β)) [IsMarkovKernel κ]
    (a : α) {s : Set β} (hs : MeasurableSet s) :
    ∫ t, MLimsup κ a s t ∂(kernel.fst κ a) = (κ a (univ ×ˢ s)).toReal := by
  rw [← integral_univ, set_integral_mLimsup_of_measurableSet κ a hs 0 MeasurableSet.univ]

lemma set_integral_mLimsup (κ : kernel α (ℝ × β)) [IsMarkovKernel κ]
    (a : α) {s : Set β} (hs : MeasurableSet s) {A : Set ℝ} (hA : MeasurableSet A) :
    ∫ t in A, MLimsup κ a s t ∂(kernel.fst κ a) = (κ a (A ×ˢ s)).toReal := by
  have hA' : MeasurableSet[⨆ n, ℱ n] A := by rwa [iSup_ℱ]
  refine MeasurableSpace.induction_on_inter (m := ⨆ n, ℱ n)
    (C := fun A ↦ ∫ t in A, MLimsup κ a s t ∂(kernel.fst κ a) = (κ a (A ×ˢ s)).toReal)
    (MeasurableSpace.measurableSpace_iSup_eq ℱ) ?_ ?_ ?_ ?_ ?_ hA'
  · rintro s ⟨n, hs⟩ t ⟨m, ht⟩ _
    exact ⟨max n m, (ℱ.mono (le_max_left n m) _ hs).inter (ℱ.mono (le_max_right n m) _ ht)⟩
  · simp
  · intro A ⟨n, hA⟩
    exact set_integral_mLimsup_of_measurableSet κ a hs n hA
  · intro A hA hA_eq
    rw [iSup_ℱ] at hA
    have h := integral_add_compl hA (integrable_mLimsup κ a hs)
    rw [hA_eq, integral_mLimsup κ a hs] at h
    have : Aᶜ ×ˢ s = univ ×ˢ s \ A ×ˢ s := by
      rw [prod_diff_prod, compl_eq_univ_diff]
      simp
    rw [this, measure_diff (by intro x; simp) (hA.prod hs) (measure_ne_top (κ a) _),
      ENNReal.toReal_sub_of_le (measure_mono (by intro x; simp)) (measure_ne_top _ _)]
    rw [eq_tsub_iff_add_eq_of_le, add_comm]
    · exact h
    · rw [ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)]
      exact measure_mono (by intro x; simp)
  · intro f hf_disj hf h_eq
    rw [integral_iUnion _ hf_disj (integrable_mLimsup _ _ hs).integrableOn]
    · simp_rw [h_eq]
      rw [← ENNReal.tsum_toReal_eq (fun _ ↦ measure_ne_top _ _)]
      congr
      rw [iUnion_prod_const, measure_iUnion]
      · intro i j hij
        rw [Function.onFun, Set.disjoint_prod]
        exact Or.inl (hf_disj hij)
      · rw [iSup_ℱ] at hf
        exact fun i ↦ (hf i).prod hs
    · rwa [iSup_ℱ] at hf

lemma tendsto_integral_mLimsup_of_monotone (κ : kernel α (ℝ × β)) [IsMarkovKernel κ]
    (a : α) (s : ℕ → Set β) (hs : Monotone s) (hs_iUnion : ⋃ i, s i = univ)
    (hs_meas : ∀ n, MeasurableSet (s n)) :
    Tendsto (fun m ↦ ∫ t, MLimsup κ a (s m) t ∂(kernel.fst κ a)) atTop (𝓝 1) := by
  simp_rw [integral_mLimsup κ a (hs_meas _)]
  rw [← ENNReal.one_toReal]
  have h_cont := ENNReal.continuousOn_toReal.continuousAt (x := 1) ?_
  swap
  · rw [mem_nhds_iff]
    refine ⟨Iio 2, fun x hx ↦ ne_top_of_lt (?_ : x < 2), isOpen_Iio, ENNReal.one_lt_two⟩
    simpa using hx
  refine h_cont.tendsto.comp ?_
  have h := tendsto_measure_iUnion (s := fun n ↦ univ ×ˢ s n) (μ := κ a) ?_
  swap; · intro n m hnm x; simp only [mem_prod, mem_univ, true_and]; exact fun h ↦ hs hnm h
  convert h
  rw [← prod_iUnion, hs_iUnion]
  simp only [univ_prod_univ, measure_univ]

lemma tendsto_integral_mLimsup_of_antitone (κ : kernel α (ℝ × β)) [IsMarkovKernel κ]
    (a : α) (s : ℕ → Set β) (hs : Antitone s) (hs_iInter : ⋂ i, s i = ∅)
    (hs_meas : ∀ n, MeasurableSet (s n)) :
    Tendsto (fun m ↦ ∫ t, MLimsup κ a (s m) t ∂(kernel.fst κ a)) atTop (𝓝 0) := by
  simp_rw [integral_mLimsup κ a (hs_meas _)]
  rw [← ENNReal.zero_toReal]
  have h_cont := ENNReal.continuousOn_toReal.continuousAt (x := 0) ?_
  swap
  · rw [mem_nhds_iff]
    refine ⟨Iio 1, fun x hx ↦ ne_top_of_lt (?_ : x < 1), isOpen_Iio, ?_⟩
    · simpa using hx
    · simp
  refine h_cont.tendsto.comp ?_
  have h := tendsto_measure_iInter (s := fun n ↦ univ ×ˢ s n) (μ := κ a)
    (fun n ↦ MeasurableSet.univ.prod (hs_meas n)) ?_ ?_
  rotate_left
  · intro n m hnm x; simp only [mem_prod, mem_univ, true_and]; exact fun h ↦ hs hnm h
  · refine ⟨0, measure_ne_top _ _⟩
  convert h
  rw [← prod_iInter, hs_iInter]
  simp only [ne_eq, prod_empty, OuterMeasure.empty', forall_exists_index]

lemma ae_eq_of_integral_eq_of_ae_le {μ : Measure α} {f g : α → ℝ} (hf : Integrable f μ)
    (hg : Integrable g μ) (h_le : f ≤ᵐ[μ] g) (h_eq : ∫ a, f a ∂μ = ∫ a, g a ∂μ) :
    f =ᵐ[μ] g := by
  suffices g - f =ᵐ[μ] 0 by
    filter_upwards [this] with a ha
    symm
    simpa only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] using ha
  have h_eq' : ∫ a, (g - f) a ∂μ = 0 := by
    simp_rw [Pi.sub_apply]
    rwa [integral_sub hg hf, sub_eq_zero, eq_comm]
  rwa [integral_eq_zero_iff_of_nonneg_ae _ (hg.sub hf)] at h_eq'
  filter_upwards [h_le] with a ha
  simpa

lemma integral_tendsto_of_tendsto_of_monotone {μ : Measure α} {f : ℕ → α → ℝ} {F : α → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hF : Integrable F μ) (h_mono : ∀ᵐ x ∂μ, Monotone fun n ↦ f n x)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n ↦ ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) := by
  let f' := fun n x ↦ f n x - f 0 x
  have hf'_nonneg : ∀ᵐ x ∂μ, ∀ n, 0 ≤ f' n x := by
    filter_upwards [h_mono] with a ha n
    simp [ha (zero_le n)]
  have hf'_meas : ∀ n, Integrable (f' n) μ := fun n ↦ (hf n).sub (hf 0)
  suffices Tendsto (fun n ↦ ∫ x, f' n x ∂μ) atTop (𝓝 (∫ x, (F - f 0) x ∂μ)) by
    rw [integral_sub' hF (hf 0)] at this
    have h_sub : ∀ n, ∫ x, f' n x ∂μ = ∫ x, f n x ∂μ - ∫ x, f 0 x ∂μ := by
      intro n
      simp only
      rw [integral_sub (hf n) (hf 0)]
    simp_rw [h_sub] at this
    have h1 : (fun n ↦ ∫ x, f n x ∂μ)
        = fun n ↦ (∫ x, f n x ∂μ - ∫ x, f 0 x ∂μ) + ∫ x, f 0 x ∂μ := by ext n; abel
    have h2 : ∫ x, F x ∂μ = (∫ x, F x ∂μ - ∫ x, f 0 x ∂μ) + ∫ x, f 0 x ∂μ := by abel
    rw [h1, h2]
    exact this.add tendsto_const_nhds
  have hF_ge : 0 ≤ᵐ[μ] fun x ↦ (F - f 0) x := by
    filter_upwards [h_tendsto, h_mono] with x hx_tendsto hx_mono
    simp only [Pi.zero_apply, Pi.sub_apply, sub_nonneg]
    exact ge_of_tendsto' hx_tendsto (fun n ↦ hx_mono (zero_le _))
  rw [ae_all_iff] at hf'_nonneg
  simp_rw [integral_eq_lintegral_of_nonneg_ae (hf'_nonneg _) (hf'_meas _).1]
  rw [integral_eq_lintegral_of_nonneg_ae hF_ge (hF.1.sub (hf 0).1)]
  have h_cont := ENNReal.continuousOn_toReal.continuousAt
    (x := ∫⁻ a, ENNReal.ofReal ((F - f 0) a) ∂μ) ?_
  swap
  · rw [mem_nhds_iff]
    refine ⟨Iio (∫⁻ a, ENNReal.ofReal ((F - f 0) a) ∂μ + 1), ?_, isOpen_Iio, ?_⟩
    · intro x
      simp only [Pi.sub_apply, mem_Iio, ne_eq, mem_setOf_eq]
      exact ne_top_of_lt
    · simp only [Pi.sub_apply, mem_Iio]
      refine ENNReal.lt_add_right ?_ one_ne_zero
      rw [← ofReal_integral_eq_lintegral_ofReal]
      · exact ENNReal.ofReal_ne_top
      · exact hF.sub (hf 0)
      · exact hF_ge
  refine h_cont.tendsto.comp ?_
  refine lintegral_tendsto_of_tendsto_of_monotone ?_ ?_ ?_
  · exact fun n ↦ ((hf n).sub (hf 0)).aemeasurable.ennreal_ofReal
  · filter_upwards [h_mono] with x hx
    intro n m hnm
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [tsub_le_iff_right, sub_add_cancel]
    exact hx hnm
  · filter_upwards [h_tendsto] with x hx
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    simp only [Pi.sub_apply]
    exact Tendsto.sub hx tendsto_const_nhds

lemma integral_tendsto_of_tendsto_of_antitone {μ : Measure α} {f : ℕ → α → ℝ} {F : α → ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hF : Integrable F μ) (h_mono : ∀ᵐ x ∂μ, Antitone fun n ↦ f n x)
    (h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n ↦ f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n ↦ ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, F x ∂μ)) := by
  suffices Tendsto (fun n ↦ ∫ x, -f n x ∂μ) atTop (𝓝 (∫ x, -F x ∂μ)) by
    suffices Tendsto (fun n ↦ ∫ x, - -f n x ∂μ) atTop (𝓝 (∫ x, - -F x ∂μ)) by
      simp_rw [neg_neg] at this
      exact this
    convert this.neg <;> rw [integral_neg]
  refine integral_tendsto_of_tendsto_of_monotone (fun n ↦ (hf n).neg) hF.neg ?_ ?_
  · filter_upwards [h_mono] with x hx
    intro n m hnm
    simp only [neg_le_neg_iff]
    exact hx hnm
  · filter_upwards [h_tendsto] with x hx
    exact hx.neg

theorem tendsto_atTop_atBot_iff_of_antitone {α β : Type*}
    [Nonempty α] [SemilatticeSup α] [Preorder β] {f : α → β}
    (hf : Antitone f) :
    Tendsto f atTop atBot ↔ ∀ b : β, ∃ a : α, f a ≤ b :=
  @tendsto_atTop_atTop_iff_of_monotone _ βᵒᵈ _ _ _ _ hf

lemma tendsto_mLimsup_atTop_ae_of_monotone (κ : kernel α (ℝ × β)) [IsMarkovKernel κ]
    (a : α) (s : ℕ → Set β) (hs : Monotone s) (hs_iUnion : ⋃ i, s i = univ)
    (hs_meas : ∀ n, MeasurableSet (s n)) :
    ∀ᵐ t ∂(kernel.fst κ a), Tendsto (fun m ↦ MLimsup κ a (s m) t) atTop (𝓝 1) := by
  have h_mono : ∀ t, Monotone (fun m ↦ MLimsup κ a (s m) t) :=
    fun t n m hnm ↦ mLimsup_mono_set κ a (hs hnm) t
  have h_le_one : ∀ m t, MLimsup κ a (s m) t ≤ 1 := fun m t ↦ mLimsup_le_one κ a (s m) t
  -- for all `t`, `fun m ↦ MLimsup κ a (s m) t` has a limit
  have h_exists : ∀ t, ∃ l, Tendsto (fun m ↦ MLimsup κ a (s m) t) atTop (𝓝 l) := by
    intro t
    have h_tendsto : Tendsto (fun m ↦ MLimsup κ a (s m) t) atTop atTop ∨
        ∃ l, Tendsto (fun m ↦ MLimsup κ a (s m) t) atTop (𝓝 l) :=
      tendsto_of_monotone (h_mono t)
    cases' h_tendsto with h_absurd h_tendsto
    · rw [tendsto_atTop_atTop_iff_of_monotone (h_mono t)] at h_absurd
      obtain ⟨r, hr⟩ := h_absurd 2
      exact absurd (hr.trans (h_le_one r t)) one_lt_two.not_le
    · exact h_tendsto
  -- let `F` be the pointwise limit of `fun m ↦ MLimsup κ a (s m) t` for all `t`
  let F : ℝ → ℝ := fun t ↦ (h_exists t).choose
  have hF_tendsto : ∀ t, Tendsto (fun m ↦ MLimsup κ a (s m) t) atTop (𝓝 (F t)) :=
    fun t ↦ (h_exists t).choose_spec
  have hF_nonneg : ∀ t, 0 ≤ F t :=
    fun t ↦ ge_of_tendsto' (hF_tendsto t) (fun m ↦ mLimsup_nonneg κ a (s m) t)
  have hF_le_one : ∀ t, F t ≤ 1 := fun t ↦ le_of_tendsto' (hF_tendsto t) (fun m ↦ h_le_one m t)
  have hF_int : Integrable F (kernel.fst κ a) := by
    rw [← memℒp_one_iff_integrable]
    refine ⟨?_, ?_⟩
    · refine aestronglyMeasurable_of_tendsto_ae atTop (fun n ↦ ?_) (ae_of_all _ hF_tendsto)
      exact (measurable_mLimsup_right κ (hs_meas _) a).aestronglyMeasurable
    · rw [snorm_one_eq_lintegral_nnnorm]
      calc ∫⁻ x, ‖F x‖₊ ∂(kernel.fst κ a) ≤ ∫⁻ _, 1 ∂(kernel.fst κ a) := by
            refine lintegral_mono (fun x ↦ ?_)
            rw [← ofReal_norm_eq_coe_nnnorm, Real.norm_eq_abs, ENNReal.ofReal_le_one,
              abs_of_nonneg (hF_nonneg _)]
            exact hF_le_one _
      _ < ⊤ := by simp only [lintegral_const, measure_univ, mul_one, ENNReal.one_lt_top]
   -- it suffices to show that the limit `F` is 1 a.e.
  suffices ∀ᵐ t ∂(kernel.fst κ a), F t = 1 by
    filter_upwards [this] with t ht_eq
    rw [← ht_eq]
    exact hF_tendsto t
  -- since `F` is at most 1, proving that its integral is the same as the integral of 1 will tell
  -- us that `F` is 1 a.e.
  refine ae_eq_of_integral_eq_of_ae_le hF_int (integrable_const _) (ae_of_all _ hF_le_one) ?_
  have h_integral :
    Tendsto (fun m : ℕ ↦ ∫ t, MLimsup κ a (s m) t ∂(kernel.fst κ a)) atTop
      (𝓝 (∫ t, F t ∂(kernel.fst κ a))) := by
    refine integral_tendsto_of_tendsto_of_monotone ?_ hF_int ?_ ?_
    · exact fun n ↦ integrable_mLimsup _ _ (hs_meas n)
    · exact ae_of_all _ h_mono
    · exact ae_of_all _ hF_tendsto
  have h_integral' :
    Tendsto (fun m : ℕ ↦ ∫ t, MLimsup κ a (s m) t ∂(kernel.fst κ a)) atTop
      (𝓝 (∫ _, 1 ∂(kernel.fst κ a))) := by
    rw [integral_const, measure_univ]
    simp only [ENNReal.one_toReal, smul_eq_mul, mul_one]
    exact tendsto_integral_mLimsup_of_monotone κ a s hs hs_iUnion hs_meas
  exact tendsto_nhds_unique h_integral h_integral'

lemma tendsto_mLimsup_atTop_ae_of_antitone (κ : kernel α (ℝ × β)) [IsMarkovKernel κ]
    (a : α) (s : ℕ → Set β) (hs : Antitone s) (hs_iInter : ⋂ i, s i = ∅)
    (hs_meas : ∀ n, MeasurableSet (s n)) :
    ∀ᵐ t ∂(kernel.fst κ a), Tendsto (fun m ↦ MLimsup κ a (s m) t) atTop (𝓝 0) := by
  have h_anti : ∀ t, Antitone (fun m ↦ MLimsup κ a (s m) t) :=
    fun t n m hnm ↦ mLimsup_mono_set κ a (hs hnm) t
  have h_le_one : ∀ m t, MLimsup κ a (s m) t ≤ 1 := fun m t ↦ mLimsup_le_one κ a (s m) t
  -- for all `t`, `fun m ↦ MLimsup κ a (s m) t` has a limit
  have h_exists : ∀ t, ∃ l, Tendsto (fun m ↦ MLimsup κ a (s m) t) atTop (𝓝 l) := by
    intro t
    have h_tendsto : Tendsto (fun m ↦ MLimsup κ a (s m) t) atTop atBot ∨
        ∃ l, Tendsto (fun m ↦ MLimsup κ a (s m) t) atTop (𝓝 l) :=
      tendsto_of_antitone (h_anti t)
    cases' h_tendsto with h_absurd h_tendsto
    · rw [tendsto_atTop_atBot_iff_of_antitone (h_anti t)] at h_absurd
      obtain ⟨r, hr⟩ := h_absurd (-1)
      have h_nonneg := mLimsup_nonneg κ a (s r) t
      linarith
    · exact h_tendsto
  -- let `F` be the pointwise limit of `fun m ↦ MLimsup κ a (s m) t` for all `t`
  let F : ℝ → ℝ := fun t ↦ (h_exists t).choose
  have hF_tendsto : ∀ t, Tendsto (fun m ↦ MLimsup κ a (s m) t) atTop (𝓝 (F t)) :=
    fun t ↦ (h_exists t).choose_spec
  have hF_nonneg : ∀ t, 0 ≤ F t :=
    fun t ↦ ge_of_tendsto' (hF_tendsto t) (fun m ↦ mLimsup_nonneg κ a (s m) t)
  have hF_le_one : ∀ t, F t ≤ 1 := fun t ↦ le_of_tendsto' (hF_tendsto t) (fun m ↦ h_le_one m t)
  have hF_int : Integrable F (kernel.fst κ a) := by
    rw [← memℒp_one_iff_integrable]
    refine ⟨?_, ?_⟩
    · refine aestronglyMeasurable_of_tendsto_ae atTop (fun n ↦ ?_) (ae_of_all _ hF_tendsto)
      exact (measurable_mLimsup_right κ (hs_meas _) a).aestronglyMeasurable
    · rw [snorm_one_eq_lintegral_nnnorm]
      calc ∫⁻ x, ‖F x‖₊ ∂(kernel.fst κ a) ≤ ∫⁻ _, 1 ∂(kernel.fst κ a) := by
            refine lintegral_mono (fun x ↦ ?_)
            rw [← ofReal_norm_eq_coe_nnnorm, Real.norm_eq_abs, ENNReal.ofReal_le_one,
              abs_of_nonneg (hF_nonneg _)]
            exact hF_le_one _
      _ < ⊤ := by simp only [lintegral_const, measure_univ, mul_one, ENNReal.one_lt_top]
   -- it suffices to show that the limit `F` is 0 a.e.
  suffices ∀ᵐ t ∂(kernel.fst κ a), F t = 0 by
    filter_upwards [this] with t ht_eq
    rw [← ht_eq]
    exact hF_tendsto t
  -- since `F` is nonnegative, proving that its integral is 0 is sufficient to get that
  -- `F` is 0 a.e.
  suffices ∀ᵐ (t : ℝ) ∂(kernel.fst κ) a, 0 = F t by filter_upwards [this] with a ha; simp [ha]
  refine ae_eq_of_integral_eq_of_ae_le (integrable_const _) hF_int  (ae_of_all _ hF_nonneg) ?_
  have h_integral :
    Tendsto (fun m : ℕ ↦ ∫ t, MLimsup κ a (s m) t ∂(kernel.fst κ a)) atTop
      (𝓝 (∫ t, F t ∂(kernel.fst κ a))) := by
    refine integral_tendsto_of_tendsto_of_antitone ?_ hF_int ?_ ?_
    · exact fun n ↦ integrable_mLimsup _ _ (hs_meas n)
    · exact ae_of_all _ h_anti
    · exact ae_of_all _ hF_tendsto
  have h_integral' :
    Tendsto (fun m : ℕ ↦ ∫ t, MLimsup κ a (s m) t ∂(kernel.fst κ a)) atTop
      (𝓝 (∫ _, 0 ∂(kernel.fst κ a))) := by
    simp only [integral_zero]
    exact tendsto_integral_mLimsup_of_antitone κ a s hs hs_iInter hs_meas
  exact (tendsto_nhds_unique h_integral h_integral').symm

section Iic_Q

noncomputable
def mLimsupIic (κ : kernel α (ℝ × ℝ)) (a : α) (t : ℝ) (q : ℚ) : ℝ := MLimsup κ a (Set.Iic q) t

lemma measurable_mLimsupIic (κ : kernel α (ℝ × ℝ)) (q : ℚ) :
    Measurable (fun p : α × ℝ ↦ mLimsupIic κ p.1 p.2 q) :=
  measurable_mLimsup κ measurableSet_Iic

lemma measurable_mLimsupIic_right (κ : kernel α (ℝ × ℝ)) (a : α) (q : ℚ) :
    Measurable (fun t ↦ mLimsupIic κ a t q) :=
  measurable_mLimsup_right _ measurableSet_Iic _

lemma monotone_mLimsupIic (κ : kernel α (ℝ × ℝ)) (a : α) (t : ℝ) : Monotone (mLimsupIic κ a t) := by
  intro q r hqr
  rw [mLimsupIic, mLimsupIic]
  refine mLimsup_mono_set κ a ?_ t
  refine Iic_subset_Iic.mpr ?_
  exact_mod_cast hqr

lemma mLimsupIic_nonneg (κ : kernel α (ℝ × ℝ)) (a : α) (t : ℝ) (q : ℚ) : 0 ≤ mLimsupIic κ a t q :=
  mLimsup_nonneg κ a _ t

lemma mLimsupIic_le_one (κ : kernel α (ℝ × ℝ)) (a : α) (t : ℝ) (q : ℚ) : mLimsupIic κ a t q ≤ 1 :=
  mLimsup_le_one κ a _ t

theorem tendsto_nat_ceil_atTop {α : Type*} [LinearOrderedSemiring α] [FloorSemiring α] :
    Tendsto (fun x : α ↦ ⌈x⌉₊) atTop atTop := by
  refine Nat.ceil_mono.tendsto_atTop_atTop (fun x ↦ ⟨x, ?_⟩)
  simp only [Nat.ceil_natCast, le_refl]

lemma tendsto_atTop_mLimsupIic (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ] (a : α) :
    ∀ᵐ t ∂(kernel.fst κ a), Tendsto (fun q ↦ mLimsupIic κ a t q) atTop (𝓝 1) := by
  suffices ∀ᵐ t ∂(kernel.fst κ a), Tendsto (fun (n : ℕ) ↦ mLimsupIic κ a t n) atTop (𝓝 1) by
    filter_upwards [this] with t ht
    let f := fun q : ℚ ↦ mLimsupIic κ a t ⌊q⌋₊
    let g := fun q : ℚ ↦ mLimsupIic κ a t ⌈q⌉₊
    have hf_le : ∀ᶠ q in atTop, f q ≤ mLimsupIic κ a t q := by
      simp only [eventually_atTop, ge_iff_le]
      exact ⟨0, fun q hq ↦ monotone_mLimsupIic κ a t (Nat.floor_le hq)⟩
    have hg_le : ∀ q, mLimsupIic κ a t q ≤ g q := fun q ↦ monotone_mLimsupIic κ a t (Nat.le_ceil _)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ ?_ hf_le (eventually_of_forall hg_le)
    · exact ht.comp tendsto_nat_floor_atTop
    · exact ht.comp tendsto_nat_ceil_atTop
  let s : ℕ → Set ℝ := fun n ↦ Iic n
  have hs : Monotone s := fun i j hij ↦ Iic_subset_Iic.mpr (by exact mod_cast hij)
  have hs_iUnion : ⋃ i, s i = univ := by
    ext x
    simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
    exact ⟨Nat.ceil x, Nat.le_ceil x⟩
  have hs_meas : ∀ n, MeasurableSet (s n) := fun _ ↦ measurableSet_Iic
  filter_upwards [tendsto_mLimsup_atTop_ae_of_monotone κ a s hs hs_iUnion hs_meas]
    with x hx using hx

lemma tendsto_atBot_mLimsupIic (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ] (a : α) :
    ∀ᵐ t ∂(kernel.fst κ a), Tendsto (fun q ↦ mLimsupIic κ a t q) atBot (𝓝 0) := by
  suffices ∀ᵐ t ∂(kernel.fst κ a), Tendsto (fun q ↦ mLimsupIic κ a t (-q)) atTop (𝓝 0) by
    filter_upwards [this] with t ht
    have h_eq_neg : (fun q ↦ mLimsupIic κ a t q) = fun q ↦ mLimsupIic κ a t (- -q) := by
      simp_rw [neg_neg]
    rw [h_eq_neg]
    exact ht.comp tendsto_neg_atBot_atTop
  suffices ∀ᵐ t ∂(kernel.fst κ a), Tendsto (fun (n : ℕ) ↦ mLimsupIic κ a t (-n)) atTop (𝓝 0) by
    filter_upwards [this] with t ht
    let f := fun q : ℚ ↦ mLimsupIic κ a t (-⌊q⌋₊)
    let g := fun q : ℚ ↦ mLimsupIic κ a t (-⌈q⌉₊)
    have hf_le : ∀ᶠ q in atTop, mLimsupIic κ a t (-q) ≤ f q := by
      simp only [eventually_atTop, ge_iff_le]
      refine ⟨0, fun q hq ↦ monotone_mLimsupIic κ a t ?_⟩
      rw [neg_le_neg_iff]
      exact Nat.floor_le hq
    have hg_le : ∀ q, g q ≤ mLimsupIic κ a t (-q) := by
      refine fun q ↦ monotone_mLimsupIic κ a t ?_
      rw [neg_le_neg_iff]
      exact Nat.le_ceil _
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ ?_ (eventually_of_forall hg_le) hf_le
    · exact ht.comp tendsto_nat_ceil_atTop
    · exact ht.comp tendsto_nat_floor_atTop
  let s : ℕ → Set ℝ := fun n ↦ Iic (-n)
  have hs : Antitone s := fun i j hij ↦ Iic_subset_Iic.mpr (neg_le_neg (by exact mod_cast hij))
  have hs_iInter : ⋂ i, s i = ∅ := by
    ext x
    simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false, not_forall, not_le, neg_lt]
    exact exists_nat_gt (-x)
  have hs_meas : ∀ n, MeasurableSet (s n) := fun _ ↦ measurableSet_Iic
  convert tendsto_mLimsup_atTop_ae_of_antitone κ a s hs hs_iInter hs_meas with x n
  rw [mLimsupIic]
  simp

lemma set_integral_mLimsupIic (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ]
    (a : α) (q : ℚ) {A : Set ℝ} (hA : MeasurableSet A) :
    ∫ t in A, mLimsupIic κ a t q ∂(kernel.fst κ a) = (κ a (A ×ˢ Iic (q : ℝ))).toReal :=
  set_integral_mLimsup κ a measurableSet_Iic hA

lemma integrable_mLimsupIic (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel (kernel.fst κ)]
    (a : α) (q : ℚ) :
    Integrable (fun t ↦ mLimsupIic κ a t q) (kernel.fst κ a) :=
  integrable_mLimsup _ _ measurableSet_Iic

lemma bddBelow_range_mLimsupIic (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel (kernel.fst κ)]
    (a : α) (t : ℝ) (q : ℚ) :
    BddBelow (range fun (r : Ioi q) ↦ mLimsupIic κ a t r) := by
  refine ⟨0, ?_⟩
  rw [mem_lowerBounds]
  rintro x ⟨y, rfl⟩
  exact mLimsupIic_nonneg _ _ _ _

lemma integrable_iInf_rat_gt_mLimsupIic (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ] (a : α) (q : ℚ) :
    Integrable (fun t ↦ ⨅ r : Ioi q, mLimsupIic κ a t r) (kernel.fst κ a) := by
  rw [← memℒp_one_iff_integrable]
  refine ⟨Measurable.aestronglyMeasurable ?_, ?_⟩
  · exact measurable_iInf fun i ↦ measurable_mLimsupIic_right κ a i
  refine (?_ : _ ≤ (1 : ℝ≥0∞)).trans_lt ENNReal.one_lt_top
  refine (snorm_le_of_ae_bound (C := 1) (ae_of_all _ (fun t ↦ ?_))).trans ?_
  · rw [Real.norm_eq_abs, abs_of_nonneg]
    · refine ciInf_le_of_le ?_ ?_ ?_
      · exact bddBelow_range_mLimsupIic κ a t _
      · exact ⟨q + 1, by simp⟩
      · exact mLimsupIic_le_one _ _ _ _
    · exact le_ciInf fun r ↦ mLimsupIic_nonneg κ a t r
  · simp

lemma set_integral_iInf_rat_gt_mLimsupIic (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ]
    (a : α) (q : ℚ) {A : Set ℝ} (hA : MeasurableSet A) :
    ∫ t in A, ⨅ r : Ioi q, mLimsupIic κ a t r ∂(kernel.fst κ a)
      = (κ a (A ×ˢ Iic (q : ℝ))).toReal := by
  refine le_antisymm ?_ ?_
  · have h : ∀ r : Ioi q, ∫ t in A, ⨅ r' : Ioi q, mLimsupIic κ a t r' ∂(kernel.fst κ a)
        ≤ (κ a (A ×ˢ Iic (r : ℝ))).toReal := by
      intro r
      rw [← set_integral_mLimsupIic κ a r hA]
      refine set_integral_mono ?_ ?_ ?_
      · exact (integrable_iInf_rat_gt_mLimsupIic _ _ _).integrableOn
      · exact (integrable_mLimsupIic _ _ _).integrableOn
      · exact fun t ↦ ciInf_le (bddBelow_range_mLimsupIic _ _ _ _) r
    calc ∫ t in A, ⨅ r : Ioi q, mLimsupIic κ a t r ∂(kernel.fst κ a)
      ≤ ⨅ r : Ioi q, (κ a (A ×ˢ Iic (r : ℝ))).toReal := le_ciInf h
    _ = (κ a (A ×ˢ Iic (q : ℝ))).toReal := by
        rw [← Measure.iInf_Iic_gt_prod hA q]
        exact (ENNReal.toReal_iInf (fun r ↦ measure_ne_top _ _)).symm
  · rw [← set_integral_mLimsupIic κ a q hA]
    refine set_integral_mono ?_ ?_ ?_
    · exact (integrable_mLimsupIic _ _ _).integrableOn
    · exact (integrable_iInf_rat_gt_mLimsupIic _ _ _).integrableOn
    · exact fun t ↦ le_ciInf (fun r ↦ monotone_mLimsupIic _ _ _ (le_of_lt r.prop))

lemma iInf_rat_gt_mLimsupIic_eq (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ] (a : α) :
    ∀ᵐ t ∂(kernel.fst κ a), ∀ q : ℚ, ⨅ r : Ioi q, mLimsupIic κ a t r = mLimsupIic κ a t q := by
  rw [ae_all_iff]
  refine fun q ↦ ae_eq_of_forall_set_integral_eq_of_sigmaFinite (μ := kernel.fst κ a) ?_ ?_ ?_
  · intro s _ _
    refine Integrable.integrableOn ?_
    exact integrable_iInf_rat_gt_mLimsupIic κ _ _
  · exact fun s _ _ ↦ (integrable_mLimsupIic κ a q).integrableOn
  · intro s hs _
    rw [set_integral_mLimsupIic _ _ _ hs, set_integral_iInf_rat_gt_mLimsupIic _ _ _ hs]

end Iic_Q

section Rat

lemma isRatStieltjesPoint_mLimsupIic_ae (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ] (a : α) :
    ∀ᵐ t ∂(kernel.fst κ a), IsRatStieltjesPoint (fun p q ↦ mLimsupIic κ p.1 p.2 q) (a, t) := by
  filter_upwards [tendsto_atTop_mLimsupIic κ a, tendsto_atBot_mLimsupIic κ a,
    iInf_rat_gt_mLimsupIic_eq κ a] with t ht_top ht_bot ht_iInf
  constructor
  · exact monotone_mLimsupIic κ a t
  · exact mLimsupIic_nonneg κ a t
  · exact mLimsupIic_le_one κ a t
  · exact ht_top
  · exact ht_bot
  · exact ht_iInf

lemma isRatKernelCDF_mLimsupIic (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ] :
    IsRatKernelCDF (fun p : α × ℝ ↦ mLimsupIic κ p.1 p.2) κ (kernel.fst κ) where
  measurable := measurable_mLimsupIic κ
  isRatStieltjesPoint_ae := isRatStieltjesPoint_mLimsupIic_ae κ
  integrable := integrable_mLimsupIic κ
  isCDF := fun _ _ hs _ ↦ set_integral_mLimsupIic _ _ _ hs

end Rat

-- todo: name?
noncomputable
def kernel.condexpReal (κ : kernel α (ℝ × ℝ)) : kernel (α × ℝ) ℝ :=
  cdfKernel _ (measurable_mLimsupIic κ)

instance (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ] : IsMarkovKernel (kernel.condexpReal κ) := by
  unfold kernel.condexpReal; infer_instance

lemma kernel.eq_compProd_condexpReal (κ : kernel α (ℝ × ℝ)) [IsMarkovKernel κ] :
    κ = kernel.fst κ ⊗ₖ kernel.condexpReal κ :=
  kernel.eq_compProd_cdfKernel (isRatKernelCDF_mLimsupIic κ)

end Real

variable {Ω' : Type*} [MeasurableSpace Ω'] [StandardBorelSpace Ω'] [Nonempty Ω']

noncomputable
def measurableEmbedding_real (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω] : Ω → ℝ :=
  (exists_measurableEmbedding_real Ω).choose

lemma measurableEmbedding_measurableEmbedding_real
    (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω] :
    MeasurableEmbedding (measurableEmbedding_real Ω) :=
  (exists_measurableEmbedding_real Ω).choose_spec

noncomputable
def condKernelAux (κ : kernel α (ℝ × Ω')) [IsMarkovKernel κ] : kernel (α × ℝ) Ω' :=
  let f := measurableEmbedding_real Ω'
  let hf := measurableEmbedding_measurableEmbedding_real Ω'
  let κ' := kernel.map κ (Prod.map (id : ℝ → ℝ) f) (measurable_id.prod_map hf.measurable)
  let x₀ := (range_nonempty f).choose
  kernel.comapRight
    (kernel.piecewise (measurableSet_eq_one (isRatKernelCDF_mLimsupIic κ') hf.measurableSet_range)
      (kernel.condexpReal κ') (kernel.deterministic (fun _ ↦ x₀) measurable_const))
    hf

instance instIsMarkovKernel_condKernelAux (κ : kernel α (ℝ × Ω')) [IsMarkovKernel κ] :
    IsMarkovKernel (condKernelAux κ) := by
  rw [condKernelAux]
  refine kernel.IsMarkovKernel.comapRight _ _ fun a ↦ ?_
  rw [kernel.piecewise_apply']
  split_ifs with h_mem
  · exact h_mem
  · classical
    rw [kernel.deterministic_apply' _ _
        (measurableEmbedding_measurableEmbedding_real Ω').measurableSet_range,
      Set.indicator_apply, if_pos]
    exact (range_nonempty (measurableEmbedding_real Ω')).choose_spec

lemma compProd_fst_condKernelAux (κ : kernel α (ℝ × Ω')) [IsMarkovKernel κ] :
    kernel.fst κ ⊗ₖ condKernelAux κ = κ := by
  let f := measurableEmbedding_real Ω'
  let hf := measurableEmbedding_measurableEmbedding_real Ω'
  let κ' := kernel.map κ (Prod.map (id : ℝ → ℝ) f) (measurable_id.prod_map hf.measurable)
  have h_prod_embed : MeasurableEmbedding (Prod.map (id : ℝ → ℝ) f) :=
    MeasurableEmbedding.id.prod_mk hf
  have h_fst : kernel.fst κ' = kernel.fst κ := by
    ext a u hu
    unfold_let κ'
    rw [kernel.fst_apply' _ _ hu, kernel.fst_apply' _ _ hu,
      kernel.map_apply' κ h_prod_embed.measurable]
    · rfl
    · exact measurable_fst hu
  have : κ = kernel.comapRight κ' h_prod_embed := by
    ext c t ht : 2
    unfold_let κ'
    rw [kernel.comapRight_apply' _ _ _ ht, kernel.map_apply' κ h_prod_embed.measurable
      _ (h_prod_embed.measurableSet_image.mpr ht)]
    congr with x : 1
    rw [← @Prod.mk.eta _ _ x]
    simp only [id.def, mem_preimage, Prod.map_mk, mem_image, Prod.mk.inj_iff, Prod.exists]
    refine' ⟨fun h => ⟨x.1, x.2, h, rfl, rfl⟩, _⟩
    rintro ⟨a, b, h_mem, rfl, hf_eq⟩
    rwa [hf.injective hf_eq] at h_mem
  conv_rhs => rw [this, kernel.eq_compProd_condexpReal κ']
  ext c t ht : 2
  rw [kernel.comapRight_apply' _ _ _ ht,
    kernel.compProd_apply _ _ _ (h_prod_embed.measurableSet_image.mpr ht),
    h_fst, kernel.compProd_apply _ _ _ ht]
  refine lintegral_congr_ae ?_
  let ρ_set := {p : α × ℝ | kernel.condexpReal κ' p (range f) = 1}
  have h_ae : ∀ a, ∀ᵐ t ∂(kernel.fst κ a), (a, t) ∈ ρ_set := by
    intro a
    rw [← h_fst]
    refine ae_cdfKernel_eq_one (isRatKernelCDF_mLimsupIic κ') a hf.measurableSet_range ?_
    simp only [mem_compl_iff, mem_range, not_exists]
    rw [kernel.map_apply']
    · have h_empty : {a : ℝ × Ω' | ∀ (x : Ω'), ¬f x = f a.2} = ∅ := by
        ext x
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_forall, not_not,
          exists_apply_eq_apply]
      simp [h_empty]
    · have : {x : ℝ × ℝ | ∀ (y : Ω'), ¬ f y = x.2} = univ ×ˢ (range f)ᶜ := by
        ext x
        simp only [mem_setOf_eq, mem_prod, mem_univ, mem_compl_iff, mem_range, not_exists, true_and]
      rw [this]
      exact MeasurableSet.univ.prod hf.measurableSet_range.compl
  filter_upwards [h_ae c] with a ha
  rw [condKernelAux, kernel.comapRight_apply']
  swap; · exact measurable_prod_mk_left ht
  have h1 : {c : ℝ | (a, c) ∈ Prod.map id f '' t} = f '' {c : Ω' | (a, c) ∈ t} := by
    ext1 x
    simp only [Prod_map, id.def, mem_image, Prod.mk.inj_iff, Prod.exists, mem_setOf_eq]
    constructor
    · rintro ⟨a', b, h_mem, rfl, hf_eq⟩
      exact ⟨b, h_mem, hf_eq⟩
    · rintro ⟨b, h_mem, hf_eq⟩
      exact ⟨a, b, h_mem, rfl, hf_eq⟩
  rw [h1, kernel.piecewise_apply, if_pos]
  exact ha

noncomputable
def condKernel (κ : kernel α (Ω × Ω')) [IsMarkovKernel κ] : kernel (α × Ω) Ω' :=
  let f := measurableEmbedding_real Ω
  let hf := measurableEmbedding_measurableEmbedding_real Ω
  let κ' := kernel.map κ (Prod.map f (id : Ω' → Ω')) (hf.measurable.prod_map measurable_id)
  kernel.comap (condKernelAux κ') (Prod.map (id : α → α) f) (measurable_id.prod_map hf.measurable)

instance instIsMarkovKernel_condKernel (κ : kernel α (Ω × Ω')) [IsMarkovKernel κ] :
    IsMarkovKernel (condKernel κ) := by rw [condKernel]; infer_instance

lemma compProd_fst_condKernel (κ : kernel α (Ω × Ω')) [IsMarkovKernel κ] :
    kernel.fst κ ⊗ₖ condKernel κ = κ := by
  let f := measurableEmbedding_real Ω
  let hf := measurableEmbedding_measurableEmbedding_real Ω
  let κ' : kernel α (ℝ × Ω') :=
    kernel.map κ (Prod.map f (id : Ω' → Ω')) (hf.measurable.prod_map measurable_id)
  have h_condKernel : condKernel κ
    = kernel.comap (condKernelAux κ') (Prod.map (id : α → α) f)
      (measurable_id.prod_map hf.measurable) := rfl
  have h_compProd := compProd_fst_condKernelAux κ'
  have h_prod_embed : MeasurableEmbedding (Prod.map f (id : Ω' → Ω')) :=
    hf.prod_mk MeasurableEmbedding.id
  have : κ = kernel.comapRight κ' h_prod_embed := by
    ext c t ht : 2
    unfold_let κ'
    rw [kernel.comapRight_apply' _ _ _ ht, kernel.map_apply' κ h_prod_embed.measurable
      _ (h_prod_embed.measurableSet_image.mpr ht)]
    congr with x : 1
    rw [← @Prod.mk.eta _ _ x]
    simp only [Prod.mk.eta, Prod_map, id_eq, mem_preimage, mem_image, Prod.mk.injEq, Prod.exists,
      exists_eq_right_right]
    refine ⟨fun h ↦ ⟨x.1, h, rfl⟩, ?_⟩
    rintro ⟨ω, h_mem, h⟩
    rwa [hf.injective h] at h_mem
  have h_fst : kernel.fst κ' = kernel.map (kernel.fst κ) f hf.measurable := by
    ext a s hs
    unfold_let κ'
    rw [kernel.map_apply' _ _ _ hs, kernel.fst_apply', kernel.fst_apply', kernel.map_apply']
    · congr
    · exact measurable_fst hs
    · exact hf.measurable hs
    · exact hs
  conv_rhs => rw [this, ← h_compProd]
  ext a s hs
  rw [h_condKernel, h_fst]
  rw [kernel.comapRight_apply' _ _ _ hs, kernel.compProd_apply _ _ _ hs, kernel.compProd_apply]
  swap; · exact h_prod_embed.measurableSet_image.mpr hs
  rw [kernel.map_apply, lintegral_map]
  congr with ω
  rw [kernel.comap_apply']
  · congr with ω'
    simp only [mem_setOf_eq, Prod_map, id_eq, mem_image, Prod.mk.injEq, Prod.exists,
      exists_eq_right_right]
    refine ⟨fun h ↦ ⟨ω, h, rfl⟩, ?_⟩
    rintro ⟨a, h_mem, h⟩
    rwa [hf.injective h] at h_mem
  · exact kernel.measurable_kernel_prod_mk_left' (h_prod_embed.measurableSet_image.mpr hs) _
  · exact hf.measurable

end ProbabilityTheory
