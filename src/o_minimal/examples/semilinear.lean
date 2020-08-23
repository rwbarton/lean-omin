import o_minimal.examples.isolating
import algebra.module.ordered
import data.fintype.card

namespace o_minimal

universe variable u

/-
Let R be an ordered vector space over an ordered field K (most commonly, R = K).
Then the functions of the form x ↦ k₀ x₀ + ... + kₙ₋₁ xₙ₋₁ + r (with kᵢ ∈ K, r ∈ R)
form an isolating family, which defines the o-minimal structure of semilinear sets.
-/

variables (K R : Type u)
variables [linear_ordered_field K] [ordered_add_comm_group R] [ordered_semimodule K R]

section semilinear

/-- Codes for semilinear functions:
constants and coordinate projections. -/
inductive semilinear_function_type (n : ℕ) : Type u
| semilinear : Π (k : fin n → K) (r : R), semilinear_function_type

namespace semilinear_function_type

open_locale big_operators

variables {K R}

/-- The interpretation of a code for a semilinear function. -/
protected def to_fun {n : ℕ} : semilinear_function_type K R n → (fin n → R) → R
| (semilinear k r) := λ x, (∑ i, k i • x i) + r

/-- (The code for) the extension of a semilinear function by an argument on the left. -/
def extend_left {n : ℕ} :
  semilinear_function_type K R n → semilinear_function_type K R (n+1)
-- | (semilinear k r) := semilinear (λ i, if h : ↑i < n then k (i.cast_lt h) else 0) r
| (semilinear k r) := semilinear (fin.cons 0 k) r

lemma to_fun_extend_left {n : ℕ} (f : semilinear_function_type K R n) :
  f.extend_left.to_fun = f.to_fun ∘ fin.tail :=
begin
  cases f with k r,
  ext,
  simp only [semilinear_function_type.to_fun, extend_left, fin.tail, add_left_inj, function.comp_app],
  rw fin.sum_univ_succ,
  simp only [fin.cons_zero, fin.cons_succ, zero_smul, zero_add],
end

def extend_right {n : ℕ} :
  semilinear_function_type K R n → semilinear_function_type K R (n+1)
| (semilinear k r) := semilinear (fin.snoc k 0) r

lemma to_fun_extend_right {n : ℕ} (f : semilinear_function_type K R n) :
  f.extend_right.to_fun = f.to_fun ∘ fin.init :=
begin
  cases f with k r,
  ext,
  simp only [semilinear_function_type.to_fun, extend_right, fin.init, add_left_inj, function.comp_app],
  rw fin.sum_univ_cast_succ,
  simp only [fin.snoc_last, add_zero, zero_smul, fin.snoc_cast_succ],
end

end semilinear_function_type

open semilinear_function_type

/-- The family of semilinear functions, consisting of just constants and coordinate projections. -/
def semilinear_function_family : function_family R :=
{ carrier := semilinear_function_type K R,
  to_fun := @semilinear_function_type.to_fun K R _ _ _,
  const := λ n r, semilinear (λ x, 0) r,
  to_fun_const := λ n r, by { ext x, simp [semilinear_function_type.to_fun], },
  coord := λ n i, semilinear (λ j, if j = i then 1 else 0) 0,
  to_fun_coord := λ n i,
  begin
    ext x,
    simp only [semilinear_function_type.to_fun, add_zero],
    rw finset.sum_eq_single i,
    { simp only [if_true, eq_self_iff_true, one_smul], },
    { simp only [eq_self_iff_true, zero_smul, if_false, forall_true_iff] {contextual := tt}, },
    { simp only [finset.mem_univ, forall_prop_of_false, not_true, not_false_iff], }
  end,
  extend_left := @extend_left K R _ _ _,
  to_fun_extend_left := @to_fun_extend_left K R _ _ _,
  extend_right := @extend_right K R _ _ _,
  to_fun_extend_right := @to_fun_extend_right K R _ _ _ }

-- TODO: Add some simp lemmas, phrased in terms of coercions

lemma semilinear_function_family_is_isolating :
  (semilinear_function_family K K).is_isolating :=
begin
  rintros n _ (⟨f,g⟩|⟨f,g⟩); clear a, -- what is `a`??
  { sorry },
  { sorry }
end

end semilinear

end o_minimal
