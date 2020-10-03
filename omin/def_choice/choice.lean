import .choice5

-- Prove general definable choice from the 1D version.

open o_minimal

universe u

variables {R : Type u} [OQM R] {S : struc R} [o_minimal_add S]

section

variables {X Y : Type*} [definable_sheaf S X] [definable_sheaf S Y]

noncomputable
def chosen_n_aux : Π {n : ℕ} (s : set (Y × finvec n R)) (h : prod.fst '' s = set.univ) (y : Y),
  {v : finvec n R // (y, v) ∈ s}
| 0     s h y := ⟨fin_zero_elim, by { obtain ⟨⟨y', z⟩, h, rfl⟩ : y ∈ prod.fst '' s, by { rw h, trivial }, convert h }⟩
| (n+1) s h y :=
let π : Y × finvec (n+1) R → Y × finvec n R := λ p, (p.1, finvec.init p.2),
    t : set (Y × finvec n R)                := π '' s,
    i : t × R → Y × finvec (n+1) R          := λ p, (p.fst.val.fst, p.fst.val.snd.snoc p.snd),
    s' : set (t × R)                        := i ⁻¹' s
in  have prod.fst '' t = set.univ,
    { have : (prod.fst : Y × finvec (n+1) R → Y) = (prod.fst : Y × finvec n R → Y) ∘ π,
      { ext ⟨_, _⟩, refl },
      rwa [this, set.image_comp] at h },
let v : {v // (y, v) ∈ t} := (chosen_n_aux t this y),
    x : ↥t := ⟨(y, v), v.2⟩ in
⟨finvec.snoc v.1 (chosen_1 s' x),
begin
  apply chosen_1_mem s' _ x,
  { -- TODO: is this right? probably an easier way
    apply set.eq_univ_of_forall,
    rintro ⟨_, ⟨⟨y, r⟩, h, rfl⟩⟩,
    refine ⟨(⟨(y, fin.init r), ⟨(y, r), h, rfl⟩⟩, r (fin.last n)), _, rfl⟩,
    { change (y, _) ∈ s,
      convert h,
      rw finvec.snoc_eq_append,
      convert finvec.left_append_right r,
      ext j,
      fin_cases j,
      simp [finvec.right],
      refl } },
end⟩

end

section

variables {X : Type u} [has_coordinates R X] [is_definable S X]
variables {Y : Type u} [has_coordinates R Y] [is_definable S Y]


-- Inductive argument: definable choice for projections s ⊆ Y × Rⁿ → Y.
lemma definable_choice_n {n : ℕ} {s : set (Y × finvec n R)} (hs : def_set S s)
  (h : prod.fst '' s = set.univ) :
  ∃ g : Y → finvec n R, def_fun S g ∧ ∀ y, (y, g y) ∈ s :=
begin
  induction n with n IH,
  { refine ⟨λ y, fin_zero_elim, def_fun_const, λ y, _⟩,
    have : y ∈ prod.fst '' s := by { rw h, trivial },
    obtain ⟨⟨y', z⟩, h, rfl⟩ := this,
    convert h },
  { let π : Y × finvec (n+1) R → Y × finvec n R := λ p, (p.1, finvec.init p.2),
    have dπ : def_fun S π := def_fun.prod def_fun.id (by exact def_fun.finvec.init),
    let t : set (Y × finvec n R) := π '' s,
    have dt : def_set S t := def_fun.image dπ hs,
    have : prod.fst '' t = set.univ,
    { have : (prod.fst : Y × finvec (n+1) R → Y) = (prod.fst : Y × finvec n R → Y) ∘ π,
      { ext ⟨_, _⟩, refl },
      rwa [this, set.image_comp] at h },
    obtain ⟨g' : Y → finvec n R, hg'₁, hg'₂⟩ := IH dt this,
    -- Now, we need to massage the data into the form to apply `definable_choice_1`.
    letI : is_definable S t := is_definable.subtype dt,
    let i : t × R → Y × finvec (n+1) R := λ p, (p.fst.val.fst, p.fst.val.snd.snoc p.snd),
    have di : def_fun S i,
    { apply def_fun.prod',
      { exact def_fun.fst.comp (def_fun_subtype_val.comp def_fun.fst) },
      { apply def_fun.finvec.snoc,
        { exact def_fun.snd.comp (def_fun_subtype_val.comp def_fun.fst) },
        { exact def_fun.snd } } },
    let s' := i ⁻¹' s,
    have ds' : def_set S s' := di.preimage hs,
    have : prod.fst '' s' = set.univ,
    { -- TODO: is this right? probably an easier way
      apply set.eq_univ_of_forall,
      rintro ⟨_, ⟨⟨y, r⟩, h, rfl⟩⟩,
      refine ⟨(⟨(y, fin.init r), ⟨(y, r), h, rfl⟩⟩, r (fin.last n)), _, rfl⟩,
      { change (y, _) ∈ s,
        convert h,
        rw finvec.snoc_eq_append,
        convert finvec.left_append_right r,
        ext j,
        fin_cases j,
        simp [finvec.right],
        refl } },
    obtain ⟨g'' : t → R, hg''₁, hg''₂⟩ := definable_choice_1 ds' this,
    -- Finally combine all the stuff.
    refine ⟨λ y, finvec.snoc (g' y) (g'' ⟨⟨y, g' y⟩, hg'₂ y⟩), _, λ y, hg''₂ ⟨⟨y, g' y⟩, hg'₂ y⟩⟩,
    apply def_fun.finvec.snoc hg'₁,
    apply hg''₁.comp,
    apply def_fun_subtype_mk,
    exact def_fun.id.prod' hg'₁ }
end

-- General form of definable choice.
theorem definable_choice {f : X → Y} (hf : def_fun S f) (h : function.surjective f) :
  ∃ g : Y → X, def_fun S g ∧ f ∘ g = id :=
begin
  let j : X → Y × finvec _ R := λ x, (f x, coords R x),
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
    apply def_fun.cancel def_fun.coords (injective_coords _),
    convert hg'₁ },
  { ext y, have := hg₂ y, dsimp only [j] at this, dsimp only [(∘), id], cc }
end

end