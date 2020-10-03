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

lemma definable_of_forall_definable_eq (f g : X₁ → X₂) (hf : definable S f) (H : ∀ x : X₁, definable S x → f x = g x) :
  definable S g :=
begin
  constructor,
  intros K L φ hφ,
  convert hf.definable K L φ hφ using 1,
  ext1,
  dsimp [function.uncurry],
  rw [H],
  rw ← definable_yoneda at hφ,
  begin [defin]
    app, exact definable.snd.definable _,
    app, exact hφ.definable _,
    exact def_fun_const
  end
end

lemma definable_chosen_one' : definable S (chosen_one' : set R → R) :=
begin
  refine definable_of_forall_definable_eq chosen_one _ definable_chosen_one _,
  intros s hs,
  unfold chosen_one chosen_one',
  rw dif_pos,
  apply tame_of_def S,
  rwa definable_iff_def_set at hs
end

noncomputable
def chosen_n' : Π {n : ℕ}, set (finvec n R) → finvec n R
| 0     s := fin_zero_elim
| (n+1) s :=
let t : set (finvec n R) := finvec.init '' s,
    a : finvec n R       := chosen_n' t,
    X : set R            := {r | a.snoc r ∈ s}
in a.snoc (chosen_one' X)

lemma chosen_n'_mem : ∀ {n : ℕ} {s : set (finvec n R)} (hs : s.nonempty), chosen_n' s ∈ s
| 0     s hs := by { obtain ⟨x, hx⟩ := hs, convert hx }
| (n+1) s hs :=
let t : set (finvec n R) := finvec.init '' s,
    a : finvec n R       := chosen_n' t,
    X : set R            := {r | a.snoc r ∈ s}
in
begin
  have ht : t.nonempty, by { rwa set.nonempty_image_iff },
  have hat : a ∈ t := chosen_n'_mem ht,
  have hX : X.nonempty,
  { obtain ⟨v, hv, H⟩ := hat, rw [← finvec.init_snoc_last v, H] at hv, exact ⟨v.last, hv⟩ },
  have := chosen_one'_mem hX,
  rwa [chosen_n']
end

instance (n : ℕ) : definable_sheaf S (finvec n R) :=
definable_sheaf.rep

instance (n : ℕ) : definable_rep S (finvec n R) :=
⟨λ _ _, iff.rfl⟩

lemma definable_chosen_n' : ∀ (n : ℕ), definable S (chosen_n' : set (finvec n R) → finvec n R)
| 0     :=
begin [defin]
  intro s,
  exact (show definable_sheaf.definable (λ (i : ↥Γ), fin_zero_elim), by exact def_fun_const)
end
| (n+1) :=
begin
  show (definable S (λ s, chosen_n' s)),
  conv { congr, funext, rw [chosen_n'] },
  dsimp [set_of],
begin [defin]
  intro s,
  app, app, exact sorry,
  app, exact (definable_chosen_n' n).definable _,
  app, app, exact sorry, exact sorry,
  var,
  app, exact definable_chosen_one'.definable _,
  intro r,
  app, app, exact definable.mem.definable _,
  app, app, exact sorry,
  app, exact (definable_chosen_n' n).definable _,
  app, app, exact sorry, exact sorry,
  var, var, var,
  end
end

noncomputable
def chosen_1 (s : set (X × R)) : X → R := chosen_one' ∘ (fibre_1 s)

lemma chosen_1_mem (s : set (X × R)) (h : prod.fst '' s = set.univ) (x : X) : (x, chosen_1 s x) ∈ s :=
begin
  suffices ne : ∀ x, set.nonempty {r | (x, r) ∈ s},
  by exact chosen_one'_mem (ne x),
  intro x,
  change ∃ r, (x, r) ∈ s,
  obtain ⟨⟨x', x⟩, h, rfl⟩ : x ∈ prod.fst '' s := by { rw h, trivial },
  exact ⟨x, h⟩
end

lemma definable_chosen_1 {s : set (X × R)} (ds : definable S s) : definable S (chosen_1 s) :=
begin [defin]
  intro x,
  app, exact definable_chosen_one'.definable _,
  app, exact (definable_fibre_1 ds).definable _,
  var
end

lemma definable_choice_1' {s : set (X × R)} (ds : definable S s) (h : prod.fst '' s = set.univ) :
  ∃ g : X → R, definable S g ∧ ∀ x, (x, g x) ∈ s :=
⟨chosen_1 s, definable_chosen_1 ds, chosen_1_mem s h⟩

-- new proof of `definable_choice_1` using `definable_rep` instead of `is_definable`
example {Y : Type*} [has_coordinates R Y] [definable_rep S Y]
  {s : set (Y × R)} (ds : def_set S s) (h : prod.fst '' s = set.univ) :
  ∃ g : Y → R, def_fun S g ∧ ∀ y, (y, g y) ∈ s :=
begin
  refine ⟨chosen_1 s, _, chosen_1_mem s h⟩,
  rw ← definable_iff_def_set at ds,
  rw ← definable_iff_def_fun,
  exact definable_chosen_1 ds
end