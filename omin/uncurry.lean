import o_minimal.sheaf.yoneda

namespace o_minimal

variables {R : Type*} (S : struc R)

class is_good_uncurry' (α β γ : Type*) [function.has_uncurry α β γ]
  [definable_sheaf S α] [definable_sheaf S β] [definable_sheaf S γ] :=
(definable_iff : ∀ (K : Def S) (f : K → α),
   definable S f ↔ definable S (λ k, ↿(f k)))

instance base.is_good_uncurry' {α β : Type*}
  [definable_sheaf S α] [definable_sheaf S β] : is_good_uncurry' S (α → β) α β :=
⟨λ K f, iff.rfl⟩

instance induction.is_good_uncurry' {α β γ δ : Type*} [function.has_uncurry β γ δ]
  [definable_sheaf S α] [definable_sheaf S β] [definable_sheaf S γ] [definable_sheaf S δ] :
  is_good_uncurry' S (α → β) (α × γ) δ :=
begin
  refine ⟨λ K f, _⟩,
  change _ ↔ definable S (λ k, function.uncurry (λ a c, ↿(f k a) c)),
  split; intro H,
  { begin [defin]
      intro k,
      app, exact definable.uncurry.definable _,
      intro a,
      intro c,
      app,
      exact sorry,
      var,
    end
},
  { let g := λ k, function.uncurry (λ a c, ↿(f k a) c),
    change definable S g at H,
    sorry }
end

class is_good_uncurry (α β γ : Type*) [function.has_uncurry α β γ]
  [definable_sheaf S α]
  [has_coordinates R β] [is_definable S β]
  [has_coordinates R γ] [is_definable S γ] :=
(x : @is_good_uncurry' R S α β γ _ _ definable_sheaf.rep definable_sheaf.rep)

variables {S}

lemma definable_iff_uncurry' {α β γ : Type*} [function.has_uncurry α β γ]
  [definable_sheaf S α]
  [has_coordinates R β] [is_definable S β]
  [has_coordinates R γ] [is_definable S γ]
  [i : is_good_uncurry S α β γ]
  {f : α} :
  definable S f ↔ def_fun S ↿f :=
begin
  letI : definable_sheaf S β := definable_sheaf.rep,
  letI : definable_sheaf S γ := definable_sheaf.rep,
  letI : definable_rep S β := ⟨λ _ _, iff.rfl⟩,
  letI : definable_rep S γ := ⟨λ _ _, iff.rfl⟩,
  letI := i.x,
  sorry -- exact (is_good_uncurry'.definable_iff f).trans definable_iff_def_fun
end

end o_minimal
