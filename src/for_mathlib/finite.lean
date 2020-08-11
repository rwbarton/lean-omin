import data.set.finite
import logic.function.iterate

variables {α : Type*} {β : Type*}

@[simp]
lemma finset.not_nonempty (s : finset α) :
  ¬s.nonempty ↔ s = ∅ :=
begin
  classical,
  rw [finset.nonempty_iff_ne_empty, not_not],
end

namespace set

lemma finite_of_finite_image_fibers {s : set α} {f : α → β}
  (himg : finite (f '' s))
  (hfib : ∀ b, finite {a ∈ s | f a = b}) :
  finite s :=
begin
  have : s = ⋃ (b ∈ f '' s), {a ∈ s | f a = b},
  { ext a,
    rw mem_bUnion_iff,
    split,
    { intro h, exact ⟨f a, mem_image_of_mem _ h, ⟨h, rfl⟩⟩ },
    { rintro ⟨_, _, ⟨h, _⟩⟩, exact h } },
  rw this,
  exact finite.bUnion himg (λ b _, hfib b)
end

lemma infinite_of_subset {s₁ s₂ : set α} (h : s₁ ⊆ s₂) (h₁ : s₁.infinite) :
  s₂.infinite :=
begin
  rw ← infinite_coe_iff at h₁ ⊢,
  resetI,
  apply infinite.of_injective _ (set.inclusion_injective h),
end

instance Ioo.densely_ordered [preorder α] [densely_ordered α] (a b : α) :
  densely_ordered (Ioo a b) :=
begin
  constructor,
  rintros ⟨x, hx⟩ ⟨y, hy⟩ h,
  change x < y at h,
  choose z hz using dense h,
  exact ⟨⟨z, lt_trans hx.1 hz.1, lt_trans hz.2 hy.2⟩, hz.1, hz.2⟩,
end

lemma Ioo.infinite [preorder α] [densely_ordered α] {x y : α} (h : x < y) :
  infinite (Ioo x y) :=
begin
  obtain ⟨c, hc₁, hc₂⟩ : ∃ c : α, x < c ∧ c < y := dense h,
  intro f,
  letI := f.fintype,
  have : well_founded ((<) : Ioo x y → Ioo x y → Prop) :=
    fintype.well_founded_of_trans_of_irrefl _,
  obtain ⟨m, _, hm⟩ : ∃ (m : Ioo x y) _, ∀ d ∈ univ, ¬ d < m := this.has_min univ ⟨⟨c, hc₁, hc₂⟩, trivial⟩,
  obtain ⟨z, hz₁, hz₂⟩ : ∃ (z : α), x < z ∧ z < m := dense m.2.1,
  refine hm ⟨z, hz₁, lt_trans hz₂ m.2.2⟩ trivial hz₂
end

lemma Ico.infinite [preorder α] [densely_ordered α] {a b : α} (h : a < b) :
  infinite (Ico a b) :=
set.infinite_of_subset Ioo_subset_Ico_self (Ioo.infinite h)

lemma Ioc.infinite [preorder α] [densely_ordered α] {a b : α} (h : a < b) :
  infinite (Ioc a b) :=
set.infinite_of_subset Ioo_subset_Ioc_self (Ioo.infinite h)

lemma Icc.infinite [preorder α] [densely_ordered α] {a b : α} (h : a < b) :
  infinite (Icc a b) :=
set.infinite_of_subset Ioo_subset_Icc_self (Ioo.infinite h)

end set
