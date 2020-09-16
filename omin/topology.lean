import topology.algebra.ordered
import o_minimal.order

namespace omin

open o_minimal

universe u

variables (R : Type u) [decidable_linear_order R] (S : struc R)

variables {X : Type*} [has_coordinates R X]
variables {Y : Type*} [has_coordinates R Y]
variables {Z : Type*} [has_coordinates R Z]
variables {W : Type*} [has_coordinates R W]

section

local attribute [instance] preorder.topology

variables (X)
def coordinate_topology : topological_space X :=
topological_space.induced (@coords R X _) (show topological_space (fin _ → R), by apply_instance)

end

variables {X}
def is_open (s : set X) : Prop :=
@_root_.is_open X (coordinate_topology R X) s

def interior (s : set X) : set X :=
@_root_.interior X (coordinate_topology R X) s

def continuous (f : X → Y) : Prop :=
@_root_.continuous X Y (coordinate_topology R X) (coordinate_topology R Y) f

section

-- This seems like it shouldn't work, because we need to guess `R`,
-- but it does work here (but not above for some reason).
local attribute [instance] coordinate_topology

lemma is_open_univ : is_open R (set.univ : set X) :=
_root_.is_open_univ

-- etc.

lemma is_open_iff_subset_interior {s : set X} : is_open R s ↔ s ⊆ interior R s :=
subset_interior_iff_open.symm

lemma mem_interior_iff {s : set X} {x : X} :
  x ∈ interior R s ↔
  ∃ (l u : fin _ → R), (∀ i, l i < coords R x i ∧ coords R x i < u i)
    ∧ ∀ y, (∀ i, l i < coords R y i ∧ coords R y i < u i) → y ∈ s :=
sorry

end

-- Definability.

variables [is_definable_le S R]
variables [is_definable S X] [is_definable S Y] [is_definable S Z] [is_definable S W]

lemma def_interior {s : set X} (hs : def_set S s) : def_set S (interior R s) :=
begin
  -- TODO: would it make more sense to use `fin _ → R` for the types of `l`, `u`?
  -- bring back instance for `fin n → R` (or `fin n → X`)?
  suffices : def_set S
    {x | ∃ (l u : finvec _ R), (∀ i, l i < coords R x i ∧ coords R x i < u i)
         ∧ ∀ y, (∀ i, l i < coords R y i ∧ coords R y i < u i) → y ∈ s},
  { convert this,
    ext x,
    rw mem_interior_iff, refl },
  apply def_set.exists,
  apply def_set.exists,
  apply def_set.and,
  { apply def_set.forall_fintype, intro i,
    apply def_set.and,
    { apply definable_lt,
      exact (def_fun.coord_rn i).comp (def_fun.snd.comp def_fun.fst),
      exact (def_fun.coord i).comp (def_fun.fst.comp def_fun.fst) },
    { apply definable_lt,
      exact (def_fun.coord i).comp (def_fun.fst.comp def_fun.fst),
      exact (def_fun.coord_rn i).comp def_fun.snd } },
  { apply def_set.forall,
    apply def_set.imp,
    { apply def_set.forall_fintype, intro i,
      apply def_set.and,
      { apply definable_lt,
        exact (def_fun.coord_rn i).comp (def_fun.snd.comp (def_fun.fst.comp def_fun.fst)),
        exact (def_fun.coord i).comp def_fun.snd },
      { apply definable_lt,
        exact (def_fun.coord i).comp def_fun.snd,
        exact (def_fun.coord_rn i).comp (def_fun.snd.comp def_fun.fst) } },
    exact def_fun.preimage def_fun.snd hs }
end

end omin
