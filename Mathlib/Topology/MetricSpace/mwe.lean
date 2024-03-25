import Mathlib.Tactic

variable {α : Type _} [MetricSpace α]

@[mk_iff]
structure IsKatetov (f : α → ℝ) : Prop where
  abs_sub_le_dist : ∀ x y, |f x - f y| ≤ dist x y
  dist_le_add : ∀ x y, dist x y ≤ f x + f y

structure KatetovMap (α : Type*) [MetricSpace α] where
  protected toFun : α → ℝ
  protected IsKatetovtoFun : IsKatetov toFun

/-- The type of Katetov maps from `α`. -/
notation "E(" α ")" => KatetovMap α

noncomputable instance: MetricSpace E(α) := by sorry
noncomputable instance : CompleteSpace E(α) := by sorry

theorem exists_kuratwoski_embedding (α : Type*) [MetricSpace α] :
  ∃ f : α → E(α), Isometry f := by sorry


noncomputable def extend {α : Type*} (s : Set α) [MetricSpace α]
    (f : E(s)) : E(α) := by sorry

def restrict {α : Type*} (s : Set α) [MetricSpace α] (f : E(α)) : E(s) := by sorry

theorem exists_subset_embedding (α : Type*) [MetricSpace α] (s : Set α) :
  ∃ f : E(s) → E(α), Isometry f := by sorry

noncomputable def subset_embed {α : Type*} [MetricSpace α] (s : Set α)  : E(s) ↪ E(α) := by sorry

-- -- My "goal"
-- def FinSuppKatMaps : Set (E(α)) := ⋃₀ {subset_embed s '' (⊤ : Set E(s)) | (Set.Finite s) (s : Set α)}

-- I then want that to inherit the same metric space structure as E(α) to be clear, so this is
-- probably a misguided approach.

-- Alternatively, I was thinking of doing something like this:

-- s here is called the "support" of f
def HasFinSuppKatMap (f : E(α)) : Prop :=
     ∃ s : Set α, Set.Finite s ∧ f = extend s (restrict s f)

structure FinSuppKatetovMap (α : Type*) [MetricSpace α] extends KatetovMap α  where
    protected HasFinSuppKatetovtoFun : HasFinSuppKatMap toKatetovMap

/-- The type of Finitely Supported Katetov maps from `α`. -/
notation "E(" α ", ω)" => FinSuppKatetovMap α

-- which should be equivalent to the thing above, but then I found it surprisingly painful to make E(α, ω)
-- inherit the metric structure, so I was considering that other approach above

instance : MetricSpace E(α, ω) := by sorry
instance : CompleteSpace E(α, ω) := by sorry

-- For further context, I then want to prove that

theorem finsupp_kuratoswki_embedding (α : Type*) [MetricSpace α] :
  ∃ f : α → E(α, ω), Isometry f := by sorry  -- which is easy "mathematically", I just had the pain with E(α, ω)

-- Then I make a sequence α_{n+1} = E(αₙ, ω) and get the limit space with Metric.Inductive,
-- which is what I am actually interested in. I don't suppose that should be a problem with a decent
-- definition of E(α, ω)
