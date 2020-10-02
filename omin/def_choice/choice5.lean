import o_minimal.sheaf.yoneda
import .choice3
import .choice4

open o_minimal

universe u

variables {R : Type u} [OQM R]
variables {S : struc R} [o_minimal_add S]

-- We need Y and R to live in the same universe to apply `def_graph`.
-- Is this really necessary?

-- jmc: ↑ is now obsolete

variables {Y : Type*} [has_coordinates R Y] [is_definable S Y]

local notation `½` := (1/2 : ℚ)

lemma definable_choice_1 {s : set (Y × R)} (ds : def_set S s) (h : prod.fst '' s = set.univ) :
  ∃ g : Y → R, def_fun S g ∧ ∀ y, (y, g y) ∈ s :=
begin
  have ne : ∀ y, set.nonempty {r | (y, r) ∈ s},
  { intro y,
    change ∃ r, (y, r) ∈ s,
    { have : y ∈ prod.fst '' s := by { rw h, trivial },
      obtain ⟨⟨y', x⟩, h, rfl⟩ := this,
      exact ⟨x, h⟩ } },
  refine ⟨λ y, (chosen_one {r | (y, r) ∈ s}), _, _⟩,
  { unfold def_fun,
    letI : definable_sheaf S Y := definable_sheaf.rep,
    letI : definable_rep S Y := ⟨λ _ _, iff.rfl⟩,
    rw ←definable_iff_def_set,
    begin [defin]
      intro p,
      app, app, exact definable_sheaf.eq,
      swap,
      { app, exact definable.snd.definable _, var },
      { app, exact definable_chosen_one.definable _,
        intro r,
        app, app, exact definable.mem.definable _,
        app, app, exact definable.prod_mk.definable _,
        app, exact definable.fst.definable _, var, var,
        exact (definable_iff_def_set.mpr ds).definable _ }
    end },
  { intro y,
    let X := {r | (y, r) ∈ s},
    have nX : X.nonempty := ne y,
    have tX : tame X,
    { apply tame_of_def S,
      refine def_fun.preimage _ ds,
      exact def_fun.prod' def_fun_const def_fun.id },
    apply chosen_one_mem nX tX }
end
.

variables {X X₁ X₂ : Type*} [definable_sheaf S X] [definable_sheaf S X₁] [definable_sheaf S X₂]

def fibre_1 (s : set (X × R)) : X → set R := λ x, {r | (x, r) ∈ s}

lemma definable_fibre_1 {s : set (X × R)} (ds : definable S s) : definable S (fibre_1 s) :=
begin [defin]
  intro x,
  intro r,
  app, app, exact definable.mem.definable _,
  app, app, exact definable.prod_mk.definable _,
  var, var, exact ds.definable _
end

lemma definable_choice_1' {s : set (X × R)} (ds : definable S s) (h : prod.fst '' s = set.univ) :
  ∃ g : X → R, definable S g ∧ ∀ x, (x, g x) ∈ s :=
begin
  refine ⟨chosen_one ∘ (fibre_1 s), _, _⟩,
  begin [defin]
    intro x,
    app, exact definable_chosen_one.definable _,
    app, exact (definable_fibre_1 ds).definable _,
    var
  end,
  have ne : ∀ y, set.nonempty {r | (y, r) ∈ s},
  { intro y,
    change ∃ r, (y, r) ∈ s,
    { have : y ∈ prod.fst '' s := by { rw h, trivial },
      obtain ⟨⟨y', x⟩, h, rfl⟩ := this,
      exact ⟨x, h⟩ } },
  begin [defin]
    -- intro x,
  -- apply chosen_one_mem (ne x),
  -- apply tame_of_def S,
  -- rw ← definable_iff_def_set,
  -- begin [defin]
    -- intro r,
    -- app, app, exact definable.mem.definable _,
    -- app, app, exact definable.prod_mk.definable _,
    -- var, var, exact ds.definable _
  end
end