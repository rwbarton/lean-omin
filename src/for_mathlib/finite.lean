import data.set.finite

variables {α : Type*} {β : Type*}

namespace set

lemma finite_of_finite_image_fibers {s : set α} {f : α → β}
  (himg : finite (f '' s))
  (hfib : ∀ b, finite {a ∈ s | f a = b}) :
  finite s :=
sorry

lemma Ioo.infinite [preorder α] [densely_ordered α] (a b : α) :
  infinite (Ioo a b) :=
sorry

end set
