import algebra.ordered_group

section
variables {G : Type*} [ordered_add_comm_group G] (a b c d : G)

lemma sub_lt_sub_iff_add_lt_add : a - b < c - d ↔ a + d < c + b :=
calc a - b < c - d ↔ a - b + b + d < c - d + b + d : by rw [← add_lt_add_iff_right b, ← add_lt_add_iff_right d]
               ... ↔ a + d < c + b                 : by rw [sub_add_cancel, add_right_comm, sub_add_cancel]

end