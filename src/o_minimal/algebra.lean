import o_minimal.definable

-- Definability of algebraic operations on definable types.

namespace o_minimal

variables {R : Type*} (S : struc R)
variables {X : Type*} [has_coordinates R X] [is_definable S X]
variables {Y : Type*} [has_coordinates R Y] [is_definable S Y]

variables (X)

class is_definable_add [has_add X] : Prop :=
(definable_add : def_fun S (λ p : X × X, p.1 + p.2))

@[to_additive]
class is_definable_mul [has_mul X] : Prop :=
(definable_mul : def_fun S (λ p : X × X, p.1 * p.2))

section definable_mul

variables {X S} [has_mul X] [is_definable_mul S X]

@[to_additive]
lemma definable_mul : def_fun S (λ p : X × X, p.1 * p.2) :=
is_definable_mul.definable_mul

@[to_additive]
lemma definable.mul {f : Y → X} (hf : def_fun S f) {g : Y → X} (hg : def_fun S g) :
  def_fun S (λ y, f y * g y) :=
definable_mul.comp (hf.prod' hg)

-- TODO: theorem: in a monoid,
-- the identity element is definable even if we don't assume definable_constants.
-- TODO: theorem: in a group OR group_with_zero,
-- the inverse is definable if multiplication is.

end definable_mul

end o_minimal

