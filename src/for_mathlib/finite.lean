import data.set.finite
import data.fintype.basic

variables {α : Type*} {β : Type*}

namespace set

lemma finite_of_finite_image_fibers {s : set α} {f : α → β}
  (himg : finite (f '' s))
  (hfib : ∀ b, finite {a ∈ s | f a = b}) :
  finite s :=
sorry

lemma Ioo.infinite [preorder α] [densely_ordered α] {x y : α} (h : x < y) :
  infinite (Ioo x y) :=
begin
  obtain ⟨c, hc₁, hc₂⟩ := dense h,
  intro f,
  letI := f.fintype,
  have := fintype.well_founded_of_trans_of_irrefl ((<) : Ioo x y → Ioo x y → Prop),
  obtain ⟨m, _, hm⟩ := this.has_min univ ⟨⟨c, hc₁, hc₂⟩, trivial⟩,
  obtain ⟨z, hz₁, hz₂⟩ := dense m.2.1,
  refine hm ⟨z, hz₁, lt_trans hz₂ m.2.2⟩ trivial hz₂
end

end set
