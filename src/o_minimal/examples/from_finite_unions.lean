import for_mathlib.closure
import o_minimal.o_minimal

/-
Construction of (o-minimal) structures of the type:
a subset of Rⁿ is definable if it is a finite union of sets of the form [...].

For example, the semialgebraic sets are the finite unions of sets of the form
{x ∈ Rⁿ | f(x) = 0, g₁(x) > 0, ..., gₖ(x) > 0}.
Semilinear sets and the "minimal" structure of sets definable in (R, <)
are also structures of this type.

Suppose D ("definable") and B ("basic") are classes of subsets of Rⁿ for each n
and the following conditions are satisfied.

* A set is definable if and only if it is a finite union of basic sets.
* Finite intersections of basic sets are definable.
* The complement of a basic set is definable.
* If A is a basic set then R × A and A × R are definable.
* {x ∈ Rⁿ | x₁ = xₙ} is definable.
* The projection of a basic set is definable.

Then D forms a structure on R.
Furthermore, if every basic subset of R¹ is tame,
then so is every definable subset.
(TODO: Last sentence above.)

-/

namespace o_minimal

open set
open_locale finvec

variables {R : Type*} (D B : Π ⦃n : ℕ⦄, set (set (fin n → R)))

/-- Standing hypotheses for this module. -/
structure finite_union_struc_hypotheses : Prop :=
(definable_iff_finite_union_basic :
  ∀ {n} {s : set (fin n → R)}, D s ↔ s ∈ finite_union_closure (@B n))
(definable_univ :
  ∀ {n}, D (U n))
(definable_basic_inter_basic :
  ∀ {n} {s t : set (fin n → R)}, B s → B t → D (s ∩ t))
(definable_compl_basic :
  ∀ {n} {s : set (fin n → R)}, B s → D sᶜ)
(definable_r_prod_basic :
  ∀ {n} {s : set (fin n → R)}, B s → D (U 1 ⊠ s))
(definable_basic_prod_r :
  ∀ {n} {s : set (fin n → R)}, B s → D (s ⊠ U 1))
(definable_eq_outer :
  ∀ {n}, D ({x | x 0 = x (fin.last _)} : set (R^(n+1))))
(definable_proj1_basic :
  ∀ {n} {s : set (fin (n+1) → R)}, B s → D (finvec.left '' s))

variables {D B}

section struc

variables (H : finite_union_struc_hypotheses D B)
include H

lemma finite_union_struc_hypotheses.D_eq_finite_union_closure_B :
  D = λ n, finite_union_closure (@B n) :=
by { ext, apply H.definable_iff_finite_union_basic }

/--
Suppose Φ : set (fin n → R) → set (fin m → R) is an operation
which commutes with finite unions.
Then if (s ∈ B → Φ s ∈ D) then (s ∈ D → Φ s ∈ D).
Examples of Φ: product with R¹ on either side; projection.

Only uses the assumption `D = finite_union_closure B`.
TODO: Generalize this to the setting of for_mathlib.closure.
-/
lemma finite_union_struc_hypotheses.promote_hypothesis {n m : ℕ}
  (Φ : set (fin n → R) → set (fin m → R)) (hΦ₀ : Φ ∅ = ∅)
  (hΦ₂ : ∀ {s t}, Φ (s ∪ t) = Φ s ∪ Φ t) :
  (∀ ⦃s : set (fin n → R)⦄, B s → D (Φ s)) →
  (∀ ⦃s : set (fin n → R)⦄, D s → D (Φ s)) :=
begin
  cases H.D_eq_finite_union_closure_B,
  intros h,
  apply finite_union_closure.rec,
  { exact @h },
  { rw hΦ₀, apply finite_union_closure.empty },
  { rintros s t - - hs ht,
    rw hΦ₂,
    apply hs.union ht }
end

/-- The structure obtained from the hypotheses `finite_union_struc_hypotheses D B`.
By definition, the definable sets are given by `D`. -/
def struc_of_finite_union : struc R :=
{ definable := D,
  definable_empty := begin
    cases H.D_eq_finite_union_closure_B,
    intro n,
    exact finite_union_closure.empty
  end,
  definable_union := begin
    cases H.D_eq_finite_union_closure_B,
    intros _ _ _ hs ht,
    exact hs.union ht
  end,
  definable_compl := begin
    cases H.D_eq_finite_union_closure_B,
    intros n s hs,
    apply closed_under_complements_finite_union_closure,
    { apply H.definable_univ },
    { apply H.definable_basic_inter_basic },
    { apply H.definable_compl_basic },
    { exact hs }
  end,
  definable_r_prod := begin
    intro n,
    refine H.promote_hypothesis (λ s, U 1 ⊠ s) _ _ (λ s h, H.definable_r_prod_basic h);
    intros; ext; simp [finvec.external_prod_def],
  end,
  definable_prod_r := begin
    intro n,
    refine H.promote_hypothesis (λ s, s ⊠ U 1) _ _ (λ s h, H.definable_basic_prod_r h);
    intros; ext; simp [finvec.external_prod_def],
  end,
  definable_eq_outer := H.definable_eq_outer,
  definable_proj1 := begin
    intro n,
    refine H.promote_hypothesis (λ s, finvec.left '' s) _ _ (λ s h, H.definable_proj1_basic h);
    intros; ext; simp [image_union]
  end }

end struc

section o_minimal

variables (D B) [DUNLO R]

structure finite_union_o_minimal_hypotheses extends finite_union_struc_hypotheses D B : Prop :=
(definable_lt : D {x : fin 2 → R | x 0 < x 1})
(definable_const : ∀ {r}, D {x : fin 1 → R | x 0 = r})
(tame_of_basic : ∀ {s : set (fin 1 → R)}, B s → tame {r | (λ _, r : fin 1 → R) ∈ s})

variables {D B} (H : finite_union_o_minimal_hypotheses D B)

lemma o_minimal_of_finite_union :
  o_minimal (struc_of_finite_union H.to_finite_union_struc_hypotheses : struc R) :=
o_minimal.mk' _ H.definable_lt H.definable_const $
begin
  change ∀ s, D s → _,
  cases H.to_finite_union_struc_hypotheses.D_eq_finite_union_closure_B,
  refine preserves_finite_unions.bind' _ closed_under_finite_unions_finite_union_closure _,
  { split; intros; simp; refl },
  exact H.tame_of_basic
end

end o_minimal

end o_minimal
