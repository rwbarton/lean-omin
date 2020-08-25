import for_mathlib.finite
import o_minimal.o_minimal

namespace o_minimal

open set

instance {R : Type*} [preorder R] (S : struc R) [is_definable_le S R] [definable_constants S]
  (a b : R) : is_definable S (Ioo a b) :=
is_definable.subtype (def_set.Ioo a b)

variables {R : Type*} [DUNLO R]
variables (S : struc R) [o_minimal S]

/-- [vdD:3.1.3 Lemma 1]:
A definable function on an interval is injective or constant on some subinterval. -/
lemma mono1 {a b : R} (hab : a < b) {f : Ioo a b → R} (hf : def_fun S f) :
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
    have : def_set S (subtype.val '' (f ⁻¹' {z})),
    { apply def_fun.image,
      exact def_fun_subtype_val,
      exact def_fun.preimage hf def_val_const },
    replace := o_minimal.tame_of_def this,
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
  have : def_set S (subtype.val '' K) := begin
    apply def_fun.image def_fun_subtype_val,
    -- TODO: automate this proof
    apply def_set.forall,
    apply def_set.imp,
    apply def_set_eq,
    exact hf.comp def_fun.fst,
    exact hf.comp def_fun.snd,
    -- TODO: definable_le instance for Ioo
    change def_set S {p : Ioo a b × Ioo a b | p.1.val ≤ p.2.val},
    apply definable_le,
    exact def_fun_subtype_val.comp def_fun.fst,
    exact def_fun_subtype_val.comp def_fun.snd
  end,
  replace := (o_minimal.tame_of_def this).finite_or_contains_interval,
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

end o_minimal
