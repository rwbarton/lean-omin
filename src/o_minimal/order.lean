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

/-- In a partial order, `≤` is definable if `<` is. -/
lemma is_definable_le_of_definable_lt [partial_order X] (h : def_set S {p : X × X | p.1 < p.2}) :
  is_definable_le S X :=
begin
  constructor,
  simp_rw [le_iff_lt_or_eq],
  exact h.union def_set_diag
end

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

-- Intervals are definable.
-- For now we assume S has definable constants for simplicity.

variables [definable_constants S] (a b : X)

lemma def_set.Iio : def_set S (Iio a) := definable_lt def_fun.id def_fun_const
lemma def_set.Ioi : def_set S (Ioi a) := definable_lt def_fun_const def_fun.id
lemma def_set.Iic : def_set S (Iic a) := definable_le def_fun.id def_fun_const
lemma def_set.Ici : def_set S (Ici a) := definable_le def_fun_const def_fun.id

lemma def_set.Ioo : def_set S (Ioo a b) := (def_set.Ioi a).inter (def_set.Iio b)
lemma def_set.Ioc : def_set S (Ioc a b) := (def_set.Ioi a).inter (def_set.Iic b)
lemma def_set.Ico : def_set S (Ico a b) := (def_set.Ici a).inter (def_set.Iio b)
lemma def_set.Icc : def_set S (Icc a b) := (def_set.Ici a).inter (def_set.Iic b)

end preorder

end o_minimal


