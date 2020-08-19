import tactic.omega
import data.fin
import data.fintype.basic
import data.set.finite
import data.set.lattice
import for_mathlib.equiv
import for_mathlib.finvec

open set
open_locale finvec

namespace o_minimal

variables {R : Type*}

-- Lean doesn't seem to want to display this notation in goals
-- local notation `U` n:max := (univ : set (R^n))
abbreviation U (n : ℕ) : set (R^n) := univ

variables (R)

/-- [vdD:1.2.1] A *structure* on a type R consists of
a class 𝑆ₙ of *definable* subsets of Rⁿ for each n ≥ 0
such that:
  (S1) 𝑆ₙ is a boolean subalgebra of subsets of Rⁿ;
  (S2) If A belongs to 𝑆ₙ then R × A and A × R belong to 𝑆ₙ₊₁;
  (S3) For n ≥ 1, {(x₁, ..., xₙ) | x₁ = xₙ} belongs to 𝑆ₙ;
  (S4) If A belongs to 𝑆ₙ₊₁ then π(A) belongs to Sₙ, where
       π : Rⁿ⁺¹ → Rⁿ denotes the projection onto the first n coordinates. -/
structure struc :=
-- TODO: "generalize" to Type instead of Prop here?
-- TODO: Try this idea: (definable : (Σ {n : ℕ}, set (R^n)) → Prop)?
(definable : Π {n : ℕ} (A : set (R^n)), Prop)
(definable_empty (n : ℕ) :
  definable (∅ : set (R^n)))
(definable_union {n : ℕ} {A B : set (R^n)} :
  definable A → definable B → definable (A ∪ B))
(definable_compl {n : ℕ} {A : set (R^n)} :
  definable A → definable Aᶜ)
(definable_r_prod {n : ℕ} {A : set (R^n)} :
  definable A → definable (U 1 ⊠ A))
(definable_prod_r {n : ℕ} {A : set (R^n)} :
  definable A → definable (A ⊠ U 1))
(definable_eq_outer {n : ℕ} :
  definable ({x | x 0 = x (fin.last _)} : set (R^(n+1))))
(definable_proj1 {n : ℕ} {A : set (R^(n+1))} :
  definable A → definable (finvec.left '' A))

variables {R} (S : struc R)

lemma struc.convert_definable {n n' : ℕ}
  {A : set (R^n)} {A' : set (R^n')} (hA' : S.definable A')
  (h : n = n') (e : ∀ x, x ∈ A ↔ finvec.cast h x ∈ A') :
  S.definable A :=
begin
  cases h,
  convert hA',
  ext x,
  convert e x,
  rw finvec.cast_id
end

lemma struc.definable_univ (n : ℕ) : S.definable (univ : set (R^n)) :=
begin
  rw ←compl_empty,
  exact S.definable_compl (S.definable_empty n)
end

lemma struc.definable_inter {n : ℕ} {A B : set (R^n)}
  (hA : S.definable A) (hB : S.definable B) : S.definable (A ∩ B) :=
begin
  rw inter_eq_compl_compl_union_compl,
  exact S.definable_compl (S.definable_union (S.definable_compl hA) (S.definable_compl hB))
end

lemma struc.definable_diff {n : ℕ} {A B : set (R^n)}
  (hA : S.definable A) (hB : S.definable B) : S.definable (A \ B) :=
begin
  rw diff_eq,
  exact S.definable_inter hA (S.definable_compl hB)
end

lemma struc.definable_Inter {ι : Type*} [fintype ι] {n : ℕ} {A : ι → set (R^n)}
  (hA : ∀ i, S.definable (A i)) : S.definable (⋂ i, A i) :=
suffices ∀ {s : set ι}, set.finite s → S.definable (⋂ i ∈ s, A i),
by { convert this finite_univ, simp },
λ s hs, finite.induction_on hs
  (by { convert S.definable_univ _, simp })
  (λ i s _ _ IH, by { convert S.definable_inter (hA i) IH, simp })

lemma struc.definable_rn_prod {m n : ℕ} {A : set (R^n)}
  (hA : S.definable A) : S.definable (U m ⊠ A) :=
begin
  -- TODO: induction principle for `nat` which uses `m + 1` rather than `nat.succ m`
  induction m with m ih,
  { refine S.convert_definable hA (by apply zero_add) _,
    intro x,
    simp [finvec.external_prod_def, finvec.right_zero], },
  { refine S.convert_definable (S.definable_r_prod ih) (by omega) _,
    intro x,
    -- Big yikes
    repeat { rw finvec.external_prod_def },
    dsimp only [nat.succ_eq_add_one],
    simp only [true_and, mem_univ],
    convert iff.rfl using 2,
    ext i,
    change x _ = x _,
    congr' 1,
    ext,
    change 1 + (m + i) = (m + 1) + i,
    ring }
end

lemma struc.definable_prod_rn {n m : ℕ} {A : set (R^n)}
  (hA : S.definable A) : S.definable (A ⊠ U m) :=
begin
  induction m with m ih,
  -- This one goes more smoothly, because of the handedness of `+`
  { refine S.convert_definable hA rfl _,
    intro x,
    simp [finvec.external_prod_def],
    refl },
  { refine S.convert_definable (S.definable_prod_r ih) rfl _,
    intro x,
    simp [finvec.external_prod_def],
    refl }
end

--- [vdD:1.2.2(i)]
lemma struc.definable_external_prod {n m : ℕ}
  {A : set (R^n)} (hA : S.definable A)
  {B : set (R^m)} (hB : S.definable B) : S.definable (A ⊠ B) :=
begin
  replace hA : S.definable (A ⊠ U m) := S.definable_prod_rn hA,
  replace hB : S.definable (U n ⊠ B) := S.definable_rn_prod hB,
  convert S.definable_inter hA hB,
  ext x,
  simp [finvec.external_prod_def]
end

private lemma obvious_nat_lemma {n : ℕ} {i j : fin n} (h : i ≤ j) :
  n = ↑i + (↑j - ↑i + 1 + (n - 1 - ↑j)) :=
begin
  cases i with i,
  cases j with j,
  change i ≤ j at h,
  dsimp,
  omega
end

--- [vdD:1.2.2(ii)]
lemma struc.definable_eq {n : ℕ} (i j : fin n) :
  S.definable {x | x i = x j} :=
begin
  wlog h : i ≤ j using i j,
  swap, { convert this, ext x, apply eq_comm },
  have : S.definable (U i ⊠ {x : R^((j - i) + 1) | x 0 = x (fin.last _)} ⊠ U (n - 1 - j)),
  { apply S.definable_rn_prod,
    apply S.definable_prod_rn,
    apply S.definable_eq_outer },
  apply S.convert_definable this (obvious_nat_lemma h),
  intro x,
  simp only
    [finvec.external_prod_def, true_and, and_true, mem_univ, mem_set_of_eq, function.comp_app],
  rw iff_iff_eq,
  congr; ext,
  { simp, refl },
  { simpa using (nat.add_sub_cancel' h).symm }
end

lemma struc.definable_diag_rn {n : ℕ} :
  S.definable {x : R^(n+n) | finvec.left x = finvec.right x} :=
begin
  have : S.definable {x : R^(n+n) | ∀ (i : fin n), finvec.left x i = finvec.right x i},
  { convert_to S.definable (⋂ (i : fin n), {x : R^(n+n) | finvec.left x i = finvec.right x i}),
    { ext, simp },
    exact S.definable_Inter (λ i, S.definable_eq _ _) },
  convert this,
  ext x,
  apply function.funext_iff
end

lemma struc.definable_proj (S : struc R) {n m : ℕ} {A : set (R^(n+m))}
  (hA : S.definable A) : S.definable (finvec.left '' A) :=
begin
  induction m with m IH,
  -- Defeqs are in our favor, so just use `convert`.
  { convert hA,
    convert set.image_id _,
    ext x ⟨i,_⟩,
    refl },
  { convert IH (S.definable_proj1 hA) using 1,
    rw ←set.image_comp,
    refl }
end

lemma struc.definable_reindex_aux {n m : ℕ} (σ : fin n → fin m)
  {B : set (R^n)} (hB : S.definable B) :
  S.definable {x : fin (m + n) → R | finvec.left x ∘ σ = finvec.right x ∧ finvec.right x ∈ B} :=
begin
  let Z : set (R^(m+n)) :=
    (⋂ (i : fin n), {z | z ((σ i).cast_add _) = z (i.nat_add _)}) ∩ (U m ⊠ B),
  have Zdef : ∀ (x : R^m) (y : R^n), x ++ y ∈ Z ↔ x ∘ σ = y ∧ y ∈ B,
  { intros x y,
    simp only [set.mem_inter_iff, set.mem_Inter, set.mem_univ,
      finvec.append_mem_external_prod, ←and_assoc, and_true],
    congr',
    rw [eq_iff_iff, function.funext_iff],
    apply forall_congr,
    intro j,
    change finvec.left (x ++ y) (σ j) = finvec.right (x ++ y) j ↔ _,
    simp },
  have : S.definable Z :=
    S.definable_inter (S.definable_Inter $ λ i, S.definable_eq _ _) (S.definable_rn_prod hB),
  convert this,
  ext z,
  dsimp,
  specialize Zdef (finvec.left z) (finvec.right z),
  rw finvec.append_left_right at Zdef,
  simp at Zdef,
  simp [Zdef],
  exact iff.rfl,
end

--- [vdD:1.2.2(iii)]
lemma struc.definable_reindex {n m : ℕ} (σ : fin n → fin m)
  {B : set (R^n)} (hB : S.definable B) : S.definable {x | x ∘ σ ∈ B} :=
begin
  convert (S.definable_proj (S.definable_reindex_aux σ hB)),
  ext x,
  rw ←finvec.append_equiv.exists_congr_left,
  rw prod.exists,
  simp only [finvec.append_equiv_apply, finvec.append_left],
  finish []
end

end o_minimal
