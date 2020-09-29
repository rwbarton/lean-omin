import algebra.module.ordered
import order.conditionally_complete_lattice
import o_minimal.sheaf.pfun
import o_minimal.sheaf.quantifiers
import ..oqm
-- import ..tame

-- Definable choice in 1 dimension.

section

-- TODO: for_mathlib order.bounds
-- also add mem_lower_bounds/is_least_def/etc.

lemma is_lub_def {α : Type*} [preorder α] (s : set α) (x : α) :
  is_lub s x ↔ (∀ a ∈ s, a ≤ x) ∧ (∀ y, (∀ a ∈ s, a ≤ y) → x ≤ y) :=
iff.rfl

lemma is_glb_def {α : Type*} [preorder α] (s : set α) (x : α) :
  is_glb s x ↔ (∀ a ∈ s, x ≤ a) ∧ (∀ y, (∀ a ∈ s, y ≤ a) → y ≤ x) :=
iff.rfl

end

local infixr ` <|| `:2 := roption.orelse_pure
local notation x ` >>* `:55 f:55 := f <$> x

open o_minimal

universe u

instance {R : Type u} {S : struc R} : is_definable S punit :=
begin
  constructor,
  convert S.definable_univ 0,
  apply set.eq_univ_of_forall,
  intro x,
  use ⟨⟩,
  ext i,
  fin_cases i
end

variables {R : Type u} [OQM R]

local notation `½` := (1/2 : ℚ)

variables {S : struc R} [o_minimal_add S]
variables {Y : Type u} [has_coordinates R Y] [definable_rep S Y]

/-
lemma def_fun.rat_smul (q : ℚ) : def_fun S (λ (r : R), q • r) :=
begin
  unfold def_fun,
  induction q using rat.num_denom_cases_on' with n d hd,
  -- need to clear denominators to get {p : R × R | n • p.fst = d • p.snd},
  -- prove definability of nsmul by constant
  sorry
end
-/

lemma half_add_half {a : R} : ½ • a + ½ • a = a :=
by { rw ←add_smul, norm_num }

lemma def_fun.half : def_fun S (λ (r : R), ½ • r) :=
begin
  unfold def_fun,
  have : def_set S {p : R × R | p.1 = p.2 + p.2} :=
    def_set_eq def_fun.fst (definable.add def_fun.snd def_fun.snd),
  convert this,
  ext ⟨x, y⟩,
  dsimp,
  split; intro h,
  { subst y,
    rw half_add_half },
  { subst x,
    rw [smul_add, half_add_half] }
end

noncomputable def one : has_one R :=
⟨classical.some (no_top 0)⟩

local attribute [instance] one

/-
let's try to prove:
axiom definable_choice_1 {s : set (Y × R)} (hs : def_set S s) (h : prod.fst '' s = set.univ) :
  ∃ g : Y → R, def_fun S g ∧ ∀ y, (y, g y) ∈ s
-/

variables (S)

-- Goal: Prove the following type is inhabited.
def definable_choice_function : Type u :=
{choice : set R →. R //
 definable S choice ∧ choice.dom = set.nonempty ∧ ∀ X H, tame X → (choice X).get H ∈ X}

variables {S}

/-- Construct a definable partial function on sets from a definable relation.
This is sensible when the relation is single-valued:
`r` s.t. `rel X r` is unique if it exists.
We ask for the proof of uniqueness now to avoid having to write it later. -/
noncomputable def pfun_of_rel (rel : set R → R → Prop)
  (uni : ∀ X r r', rel X r → rel X r' → r = r') : set R →. R := λ X,
{ dom := ∃ r, rel X r,
  get := λ h, classical.some h }

lemma mem_pfun_of_rel_iff {rel : set R → R → Prop} (uni : ∀ X r r', rel X r → rel X r' → r = r')
  (X : set R) (r : R) : r ∈ pfun_of_rel rel uni X ↔ rel X r :=
begin
  split; intro H,
  { rcases H with ⟨H, rfl⟩,
    apply classical.some_spec },
  { exact ⟨⟨r, H⟩, uni _ _ _ (classical.some_spec _) H⟩ }
end

lemma get_pfun_of_rel_eq_of_rel {rel : set R → R → Prop} {uni}
  {X : set R} {r : R} (h : rel X r) {H} : (pfun_of_rel rel uni X).get H = r :=
uni X _ _ (classical.some_spec _) h

lemma def_pfun_of_rel {rel : set R → R → Prop} {uni}
  (drel : definable S rel) : definable S (pfun_of_rel rel uni) :=
begin
  apply definable_pfun_of_graph,
  rw definable_iff_uncurry at drel,
  convert drel,
  ext ⟨x, y⟩,
  apply mem_pfun_of_rel_iff uni
end

noncomputable def the_least : set R →. R :=
pfun_of_rel is_least (λ _ _ _, is_least.unique)

@[simp] lemma the_least_dom {X : set R} : (the_least X).dom = ∃ e, is_least X e := rfl

lemma def_is_least : definable S (is_least : set R → R → Prop) :=
show definable S (λ X (r : R), r ∈ X ∧ ∀ x ∈ X, r ≤ x),
begin [defin]
  intro X,
  intro r,
  app, app, exact definable.and.definable _,
  app, app, exact definable.mem.definable _, var, var,
  all x,
  imp,
  app, app, exact definable.mem.definable _, var, var,
  app, app, exact (definable_iff_def_rel₂.mpr definable_le').definable _, var, var
end

lemma def_the_least : definable S (the_least : set R →. R) :=
def_pfun_of_rel def_is_least

-- Now repeat for inf, sup.

noncomputable def the_inf : set R →. R :=
pfun_of_rel is_glb (λ _ _ _, is_glb.unique)

noncomputable def the_sup : set R →. R :=
pfun_of_rel is_lub (λ _ _ _, is_lub.unique)

@[simp] lemma the_inf_dom {X : set R} : (the_inf X).dom = ∃ a, is_glb X a := rfl
@[simp] lemma the_sup_dom {X : set R} : (the_sup X).dom = ∃ b, is_lub X b := rfl

lemma def_the_inf : definable S (the_inf : set R →. R) :=
begin
  refine def_pfun_of_rel _,
  begin [defin]
    intro X,
    intro r,
    app, app, exact definable.and.definable _,
    { all x,
      imp,
      app, app, exact definable.mem.definable _, var, var,
      app, app, exact (definable_iff_def_rel₂.mpr definable_le').definable _, var, var },
    { all y,
      imp,
      { all x,
        imp,
        app, app, exact definable.mem.definable _, var, var,
        app, app, exact (definable_iff_def_rel₂.mpr definable_le').definable _, var, var },
      { app, app, exact (definable_iff_def_rel₂.mpr definable_le').definable _, var, var } }
  end
end

lemma def_the_sup : definable S (the_sup : set R →. R) :=
begin
  refine def_pfun_of_rel _,
  begin [defin]
    intro X,
    intro r,
    app, app, exact definable.and.definable _,
    { all x,
      imp,
      app, app, exact definable.mem.definable _, var, var,
      app, app, exact (definable_iff_def_rel₂.mpr definable_le').definable _, var, var },
    { all y,
      imp,
      { all x,
        imp,
        app, app, exact definable.mem.definable _, var, var,
        app, app, exact (definable_iff_def_rel₂.mpr definable_le').definable _, var, var },
      { app, app, exact (definable_iff_def_rel₂.mpr definable_le').definable _, var, var } }
  end
end

lemma definable_Ioo : definable S (set.Ioo : R → R → set R) :=
begin [defin]
  intro a,
  intro b,
  intro x,
  app, app, exact definable.and.definable _,
  { app, app, exact (definable_iff_def_rel₂.mpr definable_lt').definable _,
    var, var },
  { app, app, exact (definable_iff_def_rel₂.mpr definable_lt').definable _,
    var, var }
end

lemma definable_Iio : definable S (set.Iio : R → set R) :=
begin [defin]
  intro b,
  intro x,
  app, app, exact (definable_iff_def_rel₂.mpr definable_lt').definable _,
  var, var
end

-- TODO: "generalize" core library's `guard` to return `punit`?
-- TODO: super hack: we return 0 (ignored) instead of `punit`
-- just to be able to use `def_pfun_set.bind` in its current form;
-- but we could generalize the types involved in `def_pfun_set` to
-- arbitrary definable types to avoid this
-- TODO: We might have already generalized it enough.
def zero_when_nonempty : set R →. R :=
λ X, { dom := X.nonempty, get := λ _, (0 : R) }

noncomputable def chosen_one : set R →. R := λ X,
zero_when_nonempty X >>* λ _,
the_least X <||
(the_inf X >>* λ a,
  (the_sup {b | a < b ∧ set.Ioo a b ⊆ X} >>* λ b, ½ • (a + b)) <||
  a + 1) <||
(the_sup {b | set.Iio b ⊆ X} >>* λ b, b - 1) <||
0

lemma dom_chosen_one : (chosen_one : set R →. R).dom = set.nonempty :=
rfl

lemma def_zero_when_nonempty : definable S (zero_when_nonempty : set R →. R) :=
begin
  apply definable_pfun_of_graph,
  change definable S {p : set R × R | ∃ (H : p.1.nonempty), 0 = p.2},
  simp_rw exists_prop,
  have z : definable S (λ (r : R), 0 = r) :=
    definable_iff_def_set.mpr (def_set_eq def_fun_const def_fun.id),
  begin [defin]
    intro p,
    app, app, exact definable.and.definable _,
    { app, exact definable_nonempty.definable _,
      app, exact definable.fst.definable _, var },
    { app, exact z.definable _,
      app, exact definable.snd.definable _, var }
  end
end

lemma def_chosen_one : definable S (chosen_one : set R →. R) :=
begin
  unfold chosen_one,
  simp only [sub_eq_add_neg],
  begin [defin]
    intro X,
    app, app, exact definable_roption_map.definable _, swap,
    app, exact def_zero_when_nonempty.definable _, var,
    intro r,
    app, app, exact definable_orelse_pure.definable _,
    { app, exact def_the_least.definable _, var },
    app, app, exact definable_orelse_pure.definable _,
    { app, app, exact definable_roption_map.definable _, swap,
      { app, exact def_the_inf.definable _, var },
      intro a,
      app, app, exact definable_orelse_pure.definable _,
      { app, app, exact definable_roption_map.definable _, swap,
        app, exact def_the_sup.definable _,
        { intro b,
          app, app, exact definable.and.definable _,
          -- TODO: sheafy order classes
          app, app, exact (definable_iff_def_rel₂.mpr definable_lt').definable _,
          var, var,
          app, app, exact definable_subset.definable _,
          app, app, exact definable_Ioo.definable _, var, var,
          var },
        { intro b,
          app,
          exact (definable_iff_def_fun.mpr def_fun.half).definable _,
          -- TODO: sheafy algebra classes
          app, app, exact (definable_iff_def_fun₂.mpr definable_add).definable _,
          var, var } },
      { app, app, exact (definable_iff_def_fun₂.mpr definable_add).definable _,
        var,
        -- TODO: this is abstraction-breaking
        exact def_fun_const } },
    app, app, exact definable_orelse_pure.definable _,
    { app, app, exact definable_roption_map.definable _, swap,
      app, exact def_the_sup.definable _,
      { intro b,
        app, app, exact definable_subset.definable _,
        app, exact definable_Iio.definable _, var,
        var },
      { intro b,
        app, app, exact (definable_iff_def_fun₂.mpr definable_add).definable _,
        var,
        exact def_fun_const } },
    exact def_fun_const
  end
end

-- STILL TO DO (done in other files):
-- * Prove that, when `X` is tame and nonempty, `chosen_one X` is an element of `X`.
-- Hopefully it's not too hard to reason about what `chosen_one` will produce;
-- but it still requires understanding the local behavior of tame sets.
