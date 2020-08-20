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

variables {X S}

section has_mul

variables [has_mul X] [is_definable_mul S X]

@[to_additive]
lemma definable_mul : def_fun S (λ p : X × X, p.1 * p.2) :=
is_definable_mul.definable_mul

@[to_additive]
lemma definable.mul {f : Y → X} (hf : def_fun S f) {g : Y → X} (hg : def_fun S g) :
  def_fun S (λ y, f y * g y) :=
definable_mul.comp (hf.prod' hg)

end has_mul

section monoid

variables [monoid X] [is_definable_mul S X]

@[to_additive]
lemma definable_one : def_val S (1 : X) :=
begin
  suffices : {(1 : X)} = {x | ∀ y, x * y = y},
  { unfold def_val,
    rw this,
    refine def_set.forall _,
    apply_instance,             -- TODO: Huh?
    exact def_set_eq definable_mul def_fun.snd },
  ext x,
  split; intro h,
  { cases h,
    intro y,
    apply one_mul },
  { simpa using h 1 }
end

end monoid

-- TODO: theorem: in a group OR group_with_zero,
-- the inverse is definable if multiplication is.

end o_minimal

