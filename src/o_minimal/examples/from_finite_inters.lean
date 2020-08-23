import o_minimal.examples.from_finite_unions

/-
Construction of the "basic" sets of a structure
as finite intersections of "primitive" sets.

For example, in the semialgebraic structure, the basic sets are
finite intersections of "primitive sets" of the two forms
  {x ∈ Rⁿ | f(x) = 0},  {x ∈ Rⁿ | g(x) > 0}.
The semilinear and "minimal" structures also have this form.

Suppose D ("definable"), B ("basic") and P ("primitive")
are classes of subsets of Rⁿ for each n
and the following conditions are satisfied.

* A set is definable if and only if it is a finite union of basic sets.
* A set is basic if and only if it is a finite intersection of primitive sets.
* The complement of a primitive set is definable.
* If A is a primitive set then R × A and A × R are basic.
  TODO: We can weaken this condition to "... are definable" at the cost of a refactor
  (need to construct the boolean subalgebra first,
  then show it is compatible with projections).
  In practice it will even be primitive anyways.
* {x ∈ Rⁿ | x₁ = xₙ} is definable.
* The projection of a basic (not primitive!) set is definable.

Then D forms a structure on R.
Furthermore, TODO (condition to be o-minimal).

-/

namespace o_minimal

open set
open_locale finvec

variables {R : Type*} (D B P : Π ⦃n : ℕ⦄, set (set (fin n → R)))

/-- Standing hypotheses for this module. -/
structure finite_inter_struc_hypotheses : Prop :=
(definable_iff_finite_union_basic :
  ∀ {n} {s : set (fin n → R)}, D s ↔ s ∈ finite_union_closure (@B n))
(basic_iff_finite_inter_primitive :
  ∀ {n} {s : set (fin n → R)}, B s ↔ s ∈ finite_inter_closure (@P n))
(definable_compl_primitive :
  ∀ {n} {s : set (fin n → R)}, P s → D sᶜ)
(basic_r_prod_primitive :
  ∀ {n} {s : set (fin n → R)}, P s → B (U 1 ⊠ s))
(basic_primitive_prod_r :
  ∀ {n} {s : set (fin n → R)}, P s → B (s ⊠ U 1))
(definable_eq_outer :
  ∀ {n}, D ({x | x 0 = x (fin.last _)} : set (R^(n+1))))
(definable_proj1_basic :
  ∀ {n} {s : set (fin (n+1) → R)}, B s → D (finvec.left '' s))

variables {D B P}

-- Strategy: Conclude `finite_union_struc_hypotheses D B`.
-- First we work under the assumption that `B` actually is `finite_inter_closure P`.

local notation `B₀` := (λ {n : ℕ}, finite_inter_closure (@P n))

private lemma key
  (H : finite_inter_struc_hypotheses D B₀ P) :
  finite_union_struc_hypotheses D B₀ :=
have definable_of_basic : ∀ {n} {s : set (fin n → R)}, B₀ s → D s,
from λ n s hs, -- TODO: Lean bug? `H.definable_iff_finite_union_basic.mpr` should work
  (finite_inter_struc_hypotheses.definable_iff_finite_union_basic H).mpr
    (finite_union_closure.basic hs),
have promote_hypothesis : ∀ {n m : ℕ} (Φ : set (fin n → R) → set (fin m → R))
  (hΦ₀ : Φ univ = univ) (hΦ₂ : ∀ {s t}, Φ (s ∩ t) = Φ s ∩ Φ t),
  (∀ ⦃s⦄, P s → B₀ (Φ s)) → (∀ ⦃s⦄, B₀ s → B₀ (Φ s)),
from λ n m Φ hΦ₀ hΦ₂, preserves_finite_inters.bind { map_univ := @hΦ₀, map_inter := @hΦ₂ },
{ definable_iff_finite_union_basic := H.definable_iff_finite_union_basic,
  definable_univ := λ n, definable_of_basic finite_inter_closure.univ,
  definable_basic_inter_basic := λ n s t hs ht, definable_of_basic (hs.inter ht),
  definable_compl_basic := begin
    -- A basic set is a finite intersection of primitive sets,
    -- so its complement is a finite union of definable sets, hence definable.
    intros n s hs,
    rw H.definable_iff_finite_union_basic,
    obtain ⟨t, ht, hst⟩ := finite_inter_closure_iff_bInter.mp hs,
    classical,
    let t' := finset.image set.compl t,
    have : sᶜ = ⋃ (i ∈ t'), i,
    { rw hst,
      rw [←finset.bInter_coe, ←finset.bUnion_coe],
      rw compl_bInter,
      simp, refl },
    rw this,
    apply closed_under_finite_unions_finite_union_closure.mem_bUnion,
    intros i hi,
    rw ←H.definable_iff_finite_union_basic,
    rw finset.mem_image at hi,
    rcases hi with ⟨j, hj, rfl⟩,
    apply H.definable_compl_primitive,
    exact ht j hj,
  end,
  definable_r_prod_basic := begin
    intros n s hs,
    apply definable_of_basic,
    refine promote_hypothesis (λ s, U 1 ⊠ s) _ _ (λ s h, H.basic_r_prod_primitive h) hs;
    intros; ext; simp [finvec.external_prod_def]
  end,
  definable_basic_prod_r := begin
    intros n s hs,
    apply definable_of_basic,
    refine promote_hypothesis (λ s, s ⊠ U 1) _ _ (λ s h, H.basic_primitive_prod_r h) hs;
    intros; ext; simp [finvec.external_prod_def]
  end,
  definable_eq_outer := H.definable_eq_outer,
  definable_proj1_basic := H.definable_proj1_basic }

variables (H : finite_inter_struc_hypotheses D B P)
include H

lemma finite_inter_struc_hypotheses.B_eq_finite_inter_closure_P :
  B = λ n, finite_inter_closure (@P n) :=
by { ext, apply H.basic_iff_finite_inter_primitive }

lemma finite_inter_struc_hypotheses.finite_union_struc_hypotheses :
  finite_union_struc_hypotheses D B :=
by { cases H.B_eq_finite_inter_closure_P, exact key H }

def struc_of_finite_inter : struc R :=
struc_of_finite_union H.finite_union_struc_hypotheses

end o_minimal
