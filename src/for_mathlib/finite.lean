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
  classical,
  let elems := himg.to_finset.bind (λ b, (hfib b).to_finset),
  refine ⟨⟨elems.preimage (subtype.coe_injective.inj_on _), _⟩⟩,
  intros a,
  rw [finset.mem_preimage, finset.mem_bind],
  use f a,
  split,
  { rw [finite.mem_to_finset, mem_image], exact ⟨a, a.2, rfl⟩ },
  { rw [finite.mem_to_finset], exact ⟨a.2, rfl⟩ }
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

lemma Ioo.infinite [preorder α] [densely_ordered α] (x y : α) (h : x < y) :
  infinite (Ioo x y) :=
begin
  rw ← infinite_coe_iff,
  let f : (Ioo x y) → (Ioo x y) :=
  λ z, let z' := classical.indefinite_description _ (dense z.2.2) in
    ⟨z'.1, lt_trans z.2.1 z'.2.1, z'.2.2⟩,
  have hf : ∀ z, z < f z,
  { intro z,
    let z' := classical.indefinite_description _ (dense z.2.2),
    exact z'.2.1 },
  let z := classical.indefinite_description _ (dense h),
  let g : ℕ → Ioo x y := λ n, f^[n] z,
  apply infinite.of_injective g,
  apply strict_mono.injective,
  apply strict_mono.nat,
  intro n,
  show g n < (f^[n.succ] z),
  rw function.iterate_succ_apply',
  apply hf,
end

lemma Ico.infinite [preorder α] [densely_ordered α] (a b : α) (h : a < b) :
  infinite (Ico a b) :=
set.infinite_of_subset Ioo_subset_Ico_self (Ioo.infinite a b h)

lemma Ioc.infinite [preorder α] [densely_ordered α] (a b : α) (h : a < b) :
  infinite (Ioc a b) :=
set.infinite_of_subset Ioo_subset_Ioc_self (Ioo.infinite a b h)

lemma Icc.infinite [preorder α] [densely_ordered α] (a b : α) (h : a < b) :
  infinite (Icc a b) :=
set.infinite_of_subset Ioo_subset_Icc_self (Ioo.infinite a b h)

end set
