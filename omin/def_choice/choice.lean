import .choice1

-- Prove general definable choice from the 1D version.

open o_minimal

variables {R : Type*} [OQM R] {S : struc R} [o_minimal_add S]

variables {X : Type*} [has_coordinates R X] [is_definable S X]
variables {Y : Type*} [has_coordinates R Y] [is_definable S Y]

-- Inductive argument: definable choice for projections s ⊆ Y × Rⁿ → Y.
lemma definable_choice_n {n : ℕ} {s : set (Y × (fin n → R))} (hs : def_set S s)
  (h : prod.fst '' s = set.univ) :
  ∃ g : Y → (fin n → R), def_fun S g ∧ ∀ y, (y, g y) ∈ s :=
begin
  induction n with n IH,
  { refine ⟨λ y, fin_zero_elim, def_fun_const, λ y, _⟩,
    have : y ∈ prod.fst '' s := by { rw h, trivial },
    obtain ⟨⟨y', z⟩, h, rfl⟩ := this,
    convert h },
  { let π : Y × (fin (n+1) → R) → Y × (fin n → R) := λ p, (p.1, fin.init p.2),
    have dπ : def_fun S π,
    { have : def_fun S (fin.init : (fin (n+1) → R) → (fin n → R)) := sorry,
      refine def_fun.prod def_fun.id this },
    let t : set (Y × (fin n → R)) := π '' s,
    have dt : def_set S t := def_fun.image dπ hs,
    have : prod.fst '' t = set.univ,
    { have : (prod.fst : Y × (fin (n+1) → R) → Y) = (prod.fst : Y × (fin n → R) → Y) ∘ π,
      { ext ⟨_, _⟩, refl },
      rwa [this, set.image_comp] at h },
    obtain ⟨g' : Y → (fin n → R), hg'₁, hg'₂⟩ := IH dt this,
    -- Now, we need to massage the data into the form to apply `definable_choice_1`.
    letI : is_definable S t := is_definable.subtype dt,
    let i : t × R → Y × (fin (n+1) → R) := λ p, (p.fst.val.fst, fin.snoc p.fst.val.snd p.snd),
    have di : def_fun S i := sorry,
    let s' := i ⁻¹' s,
    have ds' : def_set S s' := di.preimage hs,
    have : prod.fst '' s' = set.univ := sorry,
    obtain ⟨g'' : t → R, hg''₁, hg''₂⟩ := definable_choice_1 ds' this,
    -- Finally combine all the stuff.
    refine ⟨λ y, fin.snoc (g' y) (g'' ⟨⟨y, g' y⟩, hg'₂ y⟩), _, λ y, hg''₂ ⟨⟨y, g' y⟩, hg'₂ y⟩⟩,
    -- ⊢ def_fun S (λ (y : Y), fin.snoc (g' y) (g'' ⟨(y, g' y), _⟩))
    -- need to prove `fin.init`, `fin.snoc` definable (⇐ they are reindexings).
    sorry }
end

-- General form of definable choice.
theorem definable_choice {f : X → Y} (hf : def_fun S f) (h : function.surjective f) :
  ∃ g : Y → X, def_fun S g ∧ f ∘ g = id :=
begin
  let j : X → (Y × (fin _ → R)) := λ x, (f x, coords R x),
  have dj : def_fun S j := def_fun.prod' hf def_fun.coords,
  let Γ := set.range j,
  have dΓ : def_set S Γ := dj.range,
  have : prod.fst '' Γ = set.univ,
  { apply set.eq_univ_of_forall, intro y,
    obtain ⟨x, rfl⟩ := h y,
    refine ⟨j x, set.mem_range_self _, rfl⟩ },
  obtain ⟨g', hg'₁, hg'₂⟩ := definable_choice_n dΓ this,
  simp only [Γ, set.mem_range] at hg'₂,
  choose g hg₂ using hg'₂,
  refine ⟨g, _, _⟩,
  { -- we should show that `coords R : X → (fin _ → R)` is a "definable embedding"
    -- & therefore `coords R ∘ g = g'`, `def_fun S g'` implies `def_fun S g`.
    -- this doesn't mean anything special, just definable & injective.
    have : coords R ∘ g = g',
    { ext y, have := hg₂ y, dsimp only [j] at this, dsimp only [(∘)], cc },
    sorry },
  { ext y, have := hg₂ y, dsimp only [j] at this, dsimp only [(∘), id], cc }
end
