import topology.algebra.ordered
import for_mathlib.filter_decides
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

/-- We can check that a filter is `tame_ultra` by testing it
on half-infinite intervals. -/
lemma tame_ultra_of_half_infinite {F : filter R}
  (hio : ∀ (b : R), F.decides (set.Iio b))
  (hoi : ∀ (a : R), F.decides (set.Ioi a)) :
  tame_ultra F :=
begin
  unfold tame_ultra,
  rw tame_eq_gen_half_infinite_interval,
  apply filter.decides_gen,
  rintros _ (b|a); apply_assumption
end

lemma tame_bot : tame_ultra (at_bot : filter R) :=
begin
  apply tame_ultra_of_half_infinite,
  { intro b,
    left,
    apply Iio_mem_at_bot },
  { intro a,
    right,
    rw set.compl_Ioi,
    apply mem_at_bot }
end

lemma contains_Iio_or_bdd_below {s : set R} (ts : tame s) :
  (∃ a, set.Iio a ⊆ s) ∨ bdd_below s :=
begin
  cases tame_bot ts with h h;
    obtain ⟨a, ha⟩ := mem_at_bot_sets.mp h,
  { -- TODO: for_mathlib: mem_at_bot_sets' using strict inequality
    exact or.inl ⟨a, λ b hab, ha b (le_of_lt hab)⟩ },
  { right,
    -- TODO: for_mathlib?
    use a,
    intros b hb,
    apply le_of_lt,
    rw lt_iff_not_ge,
    intro H,
    exact ha b H hb }
end

-- similarly, tame_top

local attribute [instance] preorder.topology

def above (a : R) : filter R := nhds_within a (set.Ioi a)

lemma mem_above_iff {s : set R} (a : R) :
  s ∈ above a ↔ ∃ b > a, set.Ioo a b ⊆ s :=
mem_nhds_within_Ioi_iff_exists_Ioo_subset

lemma tame_above (a : R) : tame_ultra (above a) :=
begin
  apply tame_ultra_of_half_infinite,
  { intro b,
    -- TODO: float the cases/push_neg?
    by_cases h : a < b,
    { left,
      -- TODO: for_mathlib: Iio_mem_nhds_within_Ioi
      have H : a ∈ set.Ico a b := ⟨le_refl a, h⟩,
      exact mem_sets_of_superset (Ioo_mem_nhds_within_Ioi H) set.Ioo_subset_Iio_self },
    { right,
      rw set.compl_Iio,
      push_neg at h,
      unfold above,
      -- TODO: for_mathlib: Ici_mem_nhds_within_Ioi
      rw mem_nhds_within,
      exact ⟨set.univ, is_open_univ, trivial, λ x ⟨_, hx⟩, le_trans h (le_of_lt hx)⟩ } },
  { intro b,
    by_cases h : a < b,
    { right,
      rw set.compl_Ioi,
      -- TODO: for_mathlib: Iic_mem_nhds_within_Ioi
      refine mem_sets_of_superset _ set.Icc_subset_Iic_self, { exact a },
      exact Icc_mem_nhds_within_Ioi ⟨le_refl a, h⟩ },
    { left,
      push_neg at h,
      unfold above,
      -- TODO: for_mathlib: Ici_mem_nhds_within_Ioi
      rw mem_nhds_within,
      exact ⟨set.univ, is_open_univ, trivial, λ x ⟨_, hx⟩, lt_of_le_of_lt h hx⟩ } }
end

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

-- similarly, below
