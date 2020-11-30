import order.basic
import data.finset.lattice
import data.rat

namespace o_minimal

set_option old_structure_cmd true

/-- A DUNLO is a dense unbounded nonempty linear order.
This is the setting in which we can talk about o-minimal structures.
See [vdD], §1.3, first italicized paragraph.
-/
class DUNLO (R : Type*) extends linear_order R :=
[dense : densely_ordered R]
[unbounded_below : no_bot_order R]
[unbounded_above : no_top_order R]
[nonempty : nonempty R]

-- These classes are all `Prop`s so these instances should be harmless.
attribute [instance] DUNLO.dense DUNLO.unbounded_below DUNLO.unbounded_above DUNLO.nonempty

instance : DUNLO ℚ :=
{ .. show linear_order ℚ, by apply_instance }

-- TODO: for_mathlib
/-- In a DUNLO, a system of constraints Lᵢ < x, x < Uⱼ is solvable
if and only if Lᵢ < Uⱼ for every i and j. Here i and j range over
possibly empty finite sets I and J respectively.
(In fact, this property characterizes DUNLOs.) -/
lemma order_constraints_feasible_iff {R : Type*} [DUNLO R] (lower upper : finset R) :
  (∃ x, (∀ g ∈ lower, g < x) ∧ (∀ h ∈ upper, x < h)) ↔
  ∀ (g ∈ lower) (h ∈ upper), g < h :=
begin
  split,
  { rintro ⟨x, hx₁, hx₂⟩ g Hg h Hh,
    exact lt_trans (hx₁ g Hg) (hx₂ h Hh) },
  { -- TODO: maybe reformulate all this into a useful lemma:
    -- (s : finset R) : s = ∅ ∨ ∃ max ∈ s, ∀ i ∈ s, i ≤ max
    -- Pretty similar to `exists_max_image`.
    cases hlower : lower.max with lmax;
      [{ rw finset.max_eq_none at hlower, subst lower },
       { have le_lmax : ∀ g ∈ lower, g ≤ lmax,
         { intros g H, apply finset.le_max_of_mem H hlower } }],
    all_goals {                 -- TODO: can't we write it using `;`?
    cases hupper : upper.min with umin;
      [{ rw finset.min_eq_none at hupper, subst upper },
       { have umin_le : ∀ h ∈ upper, umin ≤ h,
         { intros h H, apply finset.min_le_of_mem H hupper } }] },
    { simp },
    { suffices : ∃ (x : R), ∀ (h : R), h ∈ upper → x < h, { simpa },
      obtain ⟨x, hx⟩ := no_bot umin,
      exact ⟨x, λ h H, lt_of_lt_of_le hx (umin_le h H)⟩ },
    { suffices : ∃ (x : R), ∀ (g : R), g ∈ lower → g < x, { simpa },
      obtain ⟨x, hx⟩ := no_top lmax,
      exact ⟨x, λ g H, lt_of_le_of_lt (le_lmax g H) hx⟩ },
    { intro Hgh,
      specialize Hgh lmax (finset.mem_of_max hlower) umin (finset.mem_of_min hupper),
      obtain ⟨x, hx₁, hx₂⟩ := exists_between Hgh,
      exact ⟨x,
        λ g H, lt_of_le_of_lt (le_lmax g H) hx₁,
        λ h H, lt_of_lt_of_le hx₂ (umin_le h H)⟩ } }
end

end o_minimal
