import for_mathlib.finite
import .ominimal

open set

variables {R : Type*} [nonempty R] [decidable_linear_order R] [densely_ordered R] [no_bot_order R] [no_top_order R]
variables (S : struc R) [definable_constants S] [definable_lt S] [o_minimal S]

lemma mono1 {a b : R} (hab : a < b) {f : Ioo a b → R} (hf : S.definable_fun f) :
  ∃ (c d : R) (hcd : c < d) (hcd' : Ioo c d ⊆ Ioo a b),
  function.injective (f ∘ subtype.map id hcd') ∨
  ∃ (z : R), ∀ (x : R) (hx : x ∈ Ioo c d), f ⟨x, hcd' hx⟩ = z := -- TODO: Ugh
begin
  classical,
  by_cases H :
    ∃ (c d : R) (hcd : c < d) (hcd' : Ioo c d ⊆ Ioo a b),
    ∃ z, ∀ (x : R) (hx : x ∈ Ioo c d), f ⟨x, by exact hcd' hx⟩ = z,
  { obtain ⟨c, d, hcd, hcd', z, hf⟩ := H,
    refine ⟨c, d, hcd, hcd', or.inr ⟨z, hf⟩⟩ },
  -- Otherwise, the preimage of any {z} under f is finite
  have finite_fibers : ∀ z, finite (f ⁻¹' {z}),
  { intro z,
    have : S.definable_set (subtype.val '' (f ⁻¹' {z})),
    { apply struc.definable.image,
      apply struc.definable.val,
      apply struc.definable.preimage _ hf,
      apply definable_constants.definable_singleton },
    replace := o_minimal.tame_of_definable _ this,
    replace := this.finite_or_contains_interval,
    cases this with h h,
    { exact finite_of_finite_image (subtype.val_injective.inj_on _) h },
    { exfalso,
      apply H,
      obtain ⟨c, d, hcd, h'⟩ := h,
      have : Ioo c d ⊆ Ioo a b := subset.trans h' (subtype.coe_image_subset _ _),
      refine ⟨c, d, hcd, this, z, λ x hx, _⟩,
      obtain ⟨⟨_, _⟩, hh, rfl⟩ := h' hx,
      exact hh } },
  -- Since the fibers of f are finite, each fiber has a smallest member
  have minocc : ∀ x, ∃ x', f x' = f x ∧ ∀ x'', f x'' = f x → x' ≤ x'',
  { intro x,
    let X := {x' | f x' = f x},
    have : finite X := finite_fibers _,
    let X' := this.to_finset,
    have X'_def : ∀ {x'}, x' ∈ X' ↔ f x' = f x := by apply finite.mem_to_finset,
    have : X'.nonempty := ⟨x, X'_def.mpr rfl⟩,
    let x' := X'.min' this,
    refine ⟨x', X'_def.mp (X'.min'_mem _), λ x'' hx'', _⟩,
    rw ←X'_def at hx'',
    apply X'.min'_le,
    exact hx'' },
  -- Let K be the set of all these smallest members
  let K := {x' | ∀ x'', f x' = f x'' → x' ≤ x''},
  have : f '' K = range f,
  { refine subset.antisymm (image_subset_range _ _) _,
    rintros _ ⟨x, rfl⟩,
    obtain ⟨x', hx'₁, hx'₂⟩ := minocc x,
    refine ⟨x', _, hx'₁⟩,
    intros x'' hx'',
    apply hx'₂,
    cc },
  replace : K.infinite,
  { intro kfin,
    replace kfin : (f '' K).finite := kfin.image _,
    rw this at kfin,
    rw ←image_univ at kfin,
    have : (univ : set (Ioo a b)).finite,
    { apply finite_of_finite_image_fibers kfin,
      intro z,
      convert finite_fibers z,
      ext, simp },
    have := Ioo.infinite hab,
    rw [←infinite_coe_iff, ←infinite_univ_iff] at this,
    contradiction },
  have : S.definable_set K := definable_K S a b f hf,
  have : S.definable_set (subtype.val '' K) := struc.definable.image S (struc.definable.val S _) this,
  replace := o_minimal.tame_of_definable _ this,
  replace := this.finite_or_contains_interval,
  cases this with hK hK,
  { exfalso,
    apply ‹K.infinite›,
    exact finite_of_finite_image (subtype.val_injective.inj_on _) hK },
  { obtain ⟨c, d, hcd, hf⟩ := hK,
    have : Ioo c d ⊆ Ioo a b := subset.trans hf (subtype.coe_image_subset _ _),
    refine ⟨c, d, hcd, this, or.inl _⟩,
    rintros ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩ hx₁₂,
    let x₁' : ↥(Ioo a b) := ⟨x₁, this hx₁⟩, -- ??
    let x₂' : ↥(Ioo a b) := ⟨x₂, this hx₂⟩,
    have x₁K : K x₁', { rcases hf hx₁ with ⟨⟨_,_⟩, h₁, rfl⟩, exact h₁ },
    have x₂K : K x₂', { rcases hf hx₂ with ⟨⟨_,_⟩, h₂, rfl⟩, exact h₂ },
    have l₁ : x₁' ≤ x₂' := x₁K _ hx₁₂,
    have l₂ : x₂' ≤ x₁' := x₂K _ hx₁₂.symm,
    exact le_antisymm l₁ l₂ }
end
