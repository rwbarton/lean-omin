import topology.algebra.ordered
import .tame

-- Ultrafilters on the boolean algebra of tame sets.
-- Since mathlib doesn't have filters on general Boolean algebras
-- we just use ordinary filters and only evaluate them on tame sets.

instance preorder.topology.order_topology (α : Type*) [preorder α] :
  @order_topology α (preorder.topology α) _ :=
by letI := preorder.topology α; exact ⟨rfl⟩

open o_minimal
open filter

variables {R : Type*} [DUNLO R]

def tame_ultra (F : filter R) : Prop :=
∀ ⦃s : set R⦄ (ts : tame s), s ∈ F ∨ sᶜ ∈ F

lemma tame_ultra_iff_eventually {F : filter R} :
  tame_ultra F ↔ ∀ ⦃s : set R⦄ (ts : tame s), (∀ᶠ x in F, x ∈ s) ∨ (∀ᶠ x in F, x ∉ s) :=
iff.rfl

lemma tame_bot {s : set R} (ts : tame s) :
  tame_ultra (at_bot : filter R) :=
sorry

local attribute [instance] preorder.topology

def above (a : R) : filter R := nhds_within a (set.Ioi a)

lemma mem_above_iff {s : set R} (a : R) :
  s ∈ above a ↔ ∃ b > a, set.Ioo a b ⊆ s :=
mem_nhds_within_Ioi_iff_exists_Ioo_subset

lemma tame_above (a : R) : tame_ultra (above a) :=
sorry

/-
lemma o_minimal.tame.compl {s : set R} (ts : tame s) : tame sᶜ :=
sorry                           -- can get this from o-minimality of simple functions
-/

-- If a tame set doesn't contain its inf `a`, then it must contain some interval above `a`.
lemma above_inf {s : set R} (ts : tame s) {a : R} (ha : is_glb s a) (has : a ∉ s) :
  s ∈ above a :=
(tame_above a ts).resolve_right $ λ h, begin
  rw mem_above_iff at h,
  rcases h with ⟨b, hab, hb⟩,
  have : b ∈ lower_bounds s,
  { intros x hx,
    apply le_of_not_lt,
    intro hxb,
    rcases lt_trichotomy a x with hax|rfl|hxa,
    { exact hb ⟨hax, hxb⟩ hx },
    { exact has hx },
    { revert hxa,
      exact not_lt_of_le (ha.1 hx) } },
  revert hab,
  exact not_lt_of_le (ha.2 this)
end
