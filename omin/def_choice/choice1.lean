import ..oqm

-- Definable choice in 1 dimension.

open o_minimal

variables {R : Type*} [OQM R] {S : struc R} [o_minimal_add S]
variables {Y : Type*} [has_coordinates R Y] [is_definable S Y]

axiom definable_choice_1 {s : set (Y × R)} (hs : def_set S s) (h : prod.fst '' s = set.univ) :
  ∃ g : Y → R, def_fun S g ∧ ∀ y, (y, g y) ∈ s
-- or use function.left_inverse?
-- TODO: actually prove it!
