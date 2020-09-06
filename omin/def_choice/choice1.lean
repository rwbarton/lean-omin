import algebra.module.ordered
import order.conditionally_complete_lattice
import ..oqm
import ..ultra

-- Definable choice in 1 dimension.
-- See `choice3.lean` for a better attempt.

open o_minimal

variables {R : Type*} [OQM R]

local notation `½` := (1/2 : ℚ)

lemma lt_of_self_add_lt {a b : R} (h : a + a < b + b) : a < b :=
begin
  contrapose! h,
  exact add_le_add h h
end

lemma half_add_half {a : R} : ½ • a + ½ • a = a :=
by { rw ←add_smul, norm_num }

variables {S : struc R} [o_minimal_add S]
variables {Y : Type*} [has_coordinates R Y] [is_definable S Y]

noncomputable def one : has_one R :=
⟨classical.some (no_top 0)⟩

local attribute [instance] one

lemma one_pos : (0 : R) < 1 :=
classical.some_spec _

/-
axiom definable_choice_1 {s : set (Y × R)} (hs : def_set S s) (h : prod.fst '' s = set.univ) :
  ∃ g : Y → R, def_fun S g ∧ ∀ y, (y, g y) ∈ s
-- or use function.left_inverse?
-/

-- TODO: actually prove it! let's try:

def is_chosen (e : R) (X : set R) : Prop :=
  (e ∈ X ∧ ∀ x ∈ X, e ≤ x)
∨ (e = 0 ∧ ∀ x, x ∈ X)
∨ (∃ b, e = b - 1 ∧ (∀ x < b, x ∈ X) ∧ (∀ b' > b, ¬ ∀ x < b', x ∈ X))
∨ (∃ a, e = a + 1 ∧ (∀ x ≤ a, x ∉ X) ∧ (∀ x > a, x ∈ X))
∨ (∃ a b, e = ½ • (a + b) ∧ a < b ∧
   (∀ x ≤ a, x ∉ X) ∧ (∀ x, a < x → x < b → x ∈ X) ∧ (∀ b' > b, ¬ ∀ x, a < x → x < b' → x ∈ X))

lemma mem_of_is_chosen {e : R} {X : set R} (h : is_chosen e X) : e ∈ X :=
begin
  rcases h with ⟨m, -⟩ | ⟨-, m⟩ | ⟨b, rfl, m, -⟩ | ⟨a, rfl, -, m⟩ | ⟨a, b, rfl, hab, -, m, -⟩; apply m; clear m,
  { exact sub_lt_self _ one_pos },
  { exact lt_add_of_pos_right _ one_pos },
  { apply lt_of_self_add_lt,
    rw half_add_half,
    apply add_lt_add_left hab },
  { apply lt_of_self_add_lt,
    rw half_add_half,
    apply add_lt_add_right hab }
end

lemma unique_chosen_of_is_least {X : set R} {m : R} (hm : is_least X m) {e : R} :
  is_chosen e X → e = m :=
sorry

lemma exists_unique_chosen {X : set R} (tX : tame X) (hX : X ≠ ∅) : ∃! e, is_chosen e X :=
begin
  rw set.ne_empty_iff_nonempty at hX,
  by_cases bdd : bdd_below X,
  { obtain ⟨a, ha : is_glb X a⟩ := exists_tInf tX hX bdd,
    by_cases mem : a ∈ X,
    { -- m is the smallest element of X, so it is the chosen one.
      have : is_least X a := ⟨mem, ha.1⟩,      -- TODO: lemma
      refine ⟨a, or.inl this, λ e, unique_chosen_of_is_least this⟩ },
    { -- m is the inf of X, but doesn't belong to X.
      let Y := {b | a < b ∧ set.Ioo a b ⊆ X}, -- do we need the `a < b` part?
      -- Use simple o-minimal structure to show that Y is also tame.
      have tY : tame Y := sorry,
      -- It's nonempty by tameness of X (this requires `a⁺` ultrafilter!)
      have nY : Y.nonempty,
      { simpa using (mem_above_iff a).mp (above_inf tX ha mem) },
      -- If it has a sup, say `b`, then we're in the "(a+b)/2" case,
      -- otherwise X must equal (a, ∞) (this requires `∞` ultrafilter!)
      -- and we're in the "a+1" case.
      by_cases bY : bdd_above Y,
      { obtain ⟨b, hb : is_lub Y b⟩ := exists_tSup tY nY bY,
        refine ⟨½ • (a + b), or.inr $ or.inr $ or.inr $ or.inr ⟨a, b, rfl, _⟩, _⟩,
        { sorry },
        { sorry } },
      { sorry } } },
  { let Y := {b | set.Iio b ⊆ X},
    -- Y is nonempty, by `-∞` ultrafilter
    -- If it has a sup `b`, we're in the "b-1" case,
    -- otherwise X = univ and we're in the "0" case.
    sorry }
end

lemma def_chosen {s : set (Y × R)} (ds : def_set S s) :
  def_set S {p : Y × R | is_chosen p.2 {x | (p.1, x) ∈ s}} :=
begin
  unfold is_chosen,
  apply def_set.or,
  { apply def_set.and,
    { refine def_fun.preimage _ ds,
      exact def_fun.prod' def_fun.fst def_fun.snd },
    { apply def_set.forall,
      apply def_set.imp,
      { refine def_fun.preimage _ ds,
        exact (def_fun.fst.comp def_fun.fst).prod' def_fun.snd },
      { exact definable_le (def_fun.snd.comp def_fun.fst) def_fun.snd } } },
  -- This proof continued for some time.
  -- TODO: definable_sub, definable_smul by ℚ
  sorry
end

lemma definable_choice_1 {s : set (Y × R)} (ds : def_set S s) (h : prod.fst '' s = set.univ) :
  ∃ g : Y → R, def_fun S g ∧ ∀ y, (y, g y) ∈ s :=
begin
  have : ∀ y, ∃! (r : R), is_chosen r {x | (y, x) ∈ s},
  { intro y,
    apply exists_unique_chosen,
    { apply tame_of_def S,
      refine def_fun.preimage _ ds,
      refine def_fun.prod' def_fun_const def_fun.id },
    { have : y ∈ prod.fst '' s := by { rw h, trivial },
      obtain ⟨⟨y', x⟩, h, rfl⟩ := this,
      rw set.ne_empty_iff_nonempty,
      exact ⟨x, h⟩ } },
  -- TODO: Is there a lemma here? ("definable function comprehension"?)
  choose g hg₁ hg₂ using this,
  refine ⟨g, _, λ y, show g y ∈ {x | (y, x) ∈ s}, from mem_of_is_chosen (hg₁ y)⟩,
  { unfold def_fun,
    convert def_chosen ds,
    ext ⟨y, r⟩,
    split,
    { rintro (rfl : g y = r),
      exact hg₁ y },
    { intro h,
      exact (hg₂ _ _ h).symm } }
end
