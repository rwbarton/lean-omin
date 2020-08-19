import o_minimal.definable

-- Definability of order relations on definable types.

namespace o_minimal

open set

variables {R : Type*} (S : struc R)
variables {X : Type*} [has_coordinates R X] [is_definable S X]
variables {Y : Type*} [has_coordinates R Y] [is_definable S Y]

variables (X)

class is_definable_le [has_le X] : Prop :=
(definable_le' : def_set S {p : X × X | p.1 ≤ p.2})

variables {S X}

section has_le

variables [has_le X] [is_definable_le S X]

lemma definable_le' : def_set S {p : X × X | p.1 ≤ p.2} :=
is_definable_le.definable_le'

lemma definable_le {f : Y → X} (hf : def_fun S f) {g : Y → X} (hg : def_fun S g) :
  def_set S {p : Y | f p ≤ g p} :=
(hf.prod' hg).preimage definable_le'

end has_le

section preorder

variables [preorder X] [is_definable_le S X]

-- In a definable preorder, `<` is also definable.

lemma definable_lt' : def_set S {p : X × X | p.1 < p.2} :=
begin
  simp_rw [lt_iff_le_not_le],
  exact definable_le'.inter (definable_le def_fun.snd def_fun.fst).compl,
end

lemma definable_lt {f : Y → X} (hf : def_fun S f) {g : Y → X} (hg : def_fun S g) :
  def_set S {p : Y | f p < g p} :=
(hf.prod' hg).preimage definable_lt'

-- TODO: intervals are all definable, once we have definable constants.

end preorder

/-- In a partial order, `≤` is definable if `<` is. -/
lemma is_definable_le_of_definable_lt [partial_order X] (h : def_set S {p : X × X | p.1 < p.2}) :
  is_definable_le S X :=
begin
  constructor,
  simp_rw [le_iff_lt_or_eq],
  exact h.union def_set_diag
end

end o_minimal


