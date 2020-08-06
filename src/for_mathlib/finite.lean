import data.set.finite

variables {α : Type*} {β : Type*}

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

end set
