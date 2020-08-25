import o_minimal.examples.isolating
import algebra.module.ordered
import data.fintype.card
import algebra.module.pi
import algebra.module.submodule

import for_mathlib.ordered_group

namespace o_minimal

universe variable u

open_locale big_operators

/-
Let R be an ordered vector space over an ordered field K (most commonly, R = K).
Then the functions of the form x ↦ k₀ x₀ + ... + kₙ₋₁ xₙ₋₁ + r (with kᵢ ∈ K, r ∈ R)
form an isolating family, which defines the o-minimal structure of semilinear sets.
-/

variables (K R : Type u)
variables [linear_ordered_field K] [ordered_add_comm_group R] [ordered_semimodule K R]

section semilinear

-- some thing is wrong here
instance foo (α : Type*) : semimodule K (α → R) :=
@pi.semimodule α (λ i, R) K _ _
(λ i, by { dsimp, apply @ordered_semimodule.to_semimodule K R _, })

def semilinear_function_type (n : ℕ) : submodule K ((fin n → R) → R) :=
{ carrier := {f | ∃ (k : fin n → K) (r : R), f = λ x, ∑ i, k i • x i + r},
  zero_mem' := by { use [0, 0], ext, simp, },
  add_mem' :=
  begin
    rintro - - ⟨kf, rf, rfl⟩ ⟨kg, rg, rfl⟩,
    use [kf + kg, rf + rg],
    ext,
    simp only [finset.sum_add_distrib, add_smul, pi.add_apply],
    abel,
  end,
  smul_mem' :=
  begin
    rintro c - ⟨k, r, rfl⟩,
    use [c • k, c • r],
    ext,
    simp only [smul_add, finset.smul_sum, smul_smul, smul_eq_mul, pi.smul_apply],
  end }

namespace semilinear_function_type
variables {K R} {n : ℕ}

instance : has_coe_to_fun (semilinear_function_type K R n) :=
{ F := λ f, (fin n → R) → R,
  coe := λ f, f.1 }

@[simp] lemma coe_eq_coe_fn (f : semilinear_function_type K R n) :
  (coe f : (fin n → R) → R) = f := rfl

@[simp] lemma coe_anon (f) (hf : f ∈ semilinear_function_type K R n) :
  ⇑(⟨f, hf⟩ : semilinear_function_type K R n) = f := rfl

/-- `mk k r` is the semilinear function `x ↦ ∑ i, k i • x i + r`. -/
def mk (k : fin n → K) (r : R) :
  semilinear_function_type K R n :=
⟨_, k, r, rfl⟩

@[simp] lemma coe_mk (k : fin n → K) (r : R) :
  (mk k r : (fin n → R) → R) = λ x, ∑ i, k i • x i + r := rfl

end semilinear_function_type

open semilinear_function_type

/-- The family of semilinear functions. -/
def semilinear_function_family : function_family R :=
{ carrier := λ n, semilinear_function_type K R n,
  to_fun := λ n, coe_fn,
  const := λ n r, mk 0 r,
  to_fun_const := λ n r, by simp,
  coord := λ n i, mk (λ j, if j = i then 1 else 0) 0,
  to_fun_coord := λ n i,
  begin
    ext x,
    simp only [add_zero, coe_mk],
    rw finset.sum_eq_single i,
    { simp only [if_true, eq_self_iff_true, one_smul], },
    { simp only [eq_self_iff_true, zero_smul, if_false, forall_true_iff] {contextual := tt}, },
    { simp only [finset.mem_univ, forall_prop_of_false, not_true, not_false_iff], }
  end,
  extend_left := λ n f, ⟨f ∘ fin.tail,
  begin
    rcases f with ⟨_, k, r, rfl⟩,
    refine ⟨(fin.cons 0 k), r, _⟩,
    ext,
    simp only [fin.sum_univ_succ, fin.tail, fin.cons_zero, fin.cons_succ, zero_smul, zero_add, coe_anon, function.comp_app],
  end⟩,
  to_fun_extend_left := λ n f, rfl,
  extend_right := λ n f, ⟨f ∘ fin.init,
  begin
    rcases f with ⟨_, k, r, rfl⟩,
    refine ⟨(fin.snoc k 0), r, _⟩,
    ext,
    simp only [fin.sum_univ_cast_succ, fin.init, fin.snoc_last, add_zero, function.comp_app, zero_smul, fin.snoc_cast_succ, coe_anon],
  end⟩,
  to_fun_extend_right := λ n f, rfl }

namespace semilinear_function_family

instance {n : ℕ} : add_comm_group (semilinear_function_family K R n) :=
show add_comm_group (semilinear_function_type K R n),
by apply_instance

instance {n : ℕ} : module K (semilinear_function_family K R n) :=
show module K (semilinear_function_type K R n),
by apply_instance

end semilinear_function_family

/-
NOTE
From now on we assume R = K, since Lean doesn't seem to have linear_ordered_add_comm_group yet.
Without it, we can't get a linear_order on R without diamonds.
-/

variable {K}

lemma semilinear_function_family_eq_constraint ⦃n : ℕ⦄
  (f : (semilinear_function_family K K) (n + 1)) :
  ∃ (ic : isolated_constraint (semilinear_function_family K K) n),
    ic.to_set = {x | f x = 0} :=
begin
  rcases f with ⟨-, k, r, rfl⟩,
  by_cases h : k (fin.last n) = 0,
  { refine ⟨isolated_constraint.push_eq (mk (k ∘ fin.cast_succ) r) 0, _⟩,
    simp only [h, isolated_constraint.to_set, fin.sum_univ_cast_succ, fin.init, function.comp_app,
      function_family.extend_right_app, smul_eq_mul, coe_anon, add_zero, coe_mk, zero_mul],
    ext x,
    exact iff.rfl },
  { let c := k (fin.last n),
    refine ⟨isolated_constraint.eq (mk (-c⁻¹ • k ∘ fin.cast_succ) (-c⁻¹ * r)), _⟩,
    simp only [h, isolated_constraint.to_set, fin.sum_univ_cast_succ, fin.init, coe_mk, function.comp_app,
      function_family.extend_right_app, smul_eq_mul, pi.smul_apply, coe_anon],
    ext x,
    show _ = _ ↔ _ = _,
    simp only [neg_mul_eq_neg_mul_symm, finset.sum_neg_distrib, mul_assoc, ← finset.mul_sum],
    rw [← neg_add, ← mul_add, eq_neg_iff_add_eq_zero, ← mul_right_inj' h],
    simp only [h, mul_add, ne.def, not_false_iff, mul_zero, mul_inv_cancel_left'],
    rw [add_left_comm, add_assoc], }
end

lemma semilinear_function_family_lt_constraint ⦃n : ℕ⦄
  (f : (semilinear_function_family K K) (n + 1)) :
  ∃ (ic : isolated_constraint (semilinear_function_family K K) n),
    ic.to_set = {x | f x < 0} :=
begin
  rcases f with ⟨-, k, r, rfl⟩,
  by_cases h : k (fin.last n) = 0,
  { refine ⟨isolated_constraint.push_lt (mk (k ∘ fin.cast_succ) r) 0, _⟩,
    simp only [h, isolated_constraint.to_set, fin.sum_univ_cast_succ, fin.init, function.comp_app,
      function_family.extend_right_app, smul_eq_mul, coe_anon, add_zero, coe_mk, zero_mul],
    ext x,
    exact iff.rfl },
  { let c := k (fin.last n),
    obtain hc|hc : c < 0 ∨ 0 < c := lt_or_gt_of_ne h,
    { refine ⟨isolated_constraint.gt (mk (-c⁻¹ • k ∘ fin.cast_succ) (-c⁻¹ * r)), _⟩,
      rw [isolated_constraint.to_set],
      simp only [neg_mul_eq_neg_mul_symm, coe_mk, pi.neg_apply, function.comp_app,
        function_family.extend_right_app, finset.sum_neg_distrib, smul_eq_mul, neg_smul, pi.smul_apply,
        fin.sum_univ_cast_succ, fin.init, coe_anon],
      ext x,
      show _ < _ ↔ _ < _,
      simp only [neg_mul_eq_neg_mul_symm, finset.sum_neg_distrib, mul_assoc, ← finset.mul_sum],
      rw [← neg_add, ← mul_add, ← sub_lt_zero, sub_eq_add_neg, ← mul_lt_mul_left_of_neg hc],
      rw [mul_zero, ← neg_add, ← neg_mul_eq_mul_neg, mul_add, mul_inv_cancel_left' (ne_of_lt hc)],
      rw [neg_pos, add_right_comm], },
    { refine ⟨isolated_constraint.lt (mk (-c⁻¹ • k ∘ fin.cast_succ) (-c⁻¹ * r)), _⟩,
      rw [isolated_constraint.to_set],
      simp only [neg_mul_eq_neg_mul_symm, coe_mk, pi.neg_apply, function.comp_app,
        function_family.extend_right_app, finset.sum_neg_distrib, smul_eq_mul, neg_smul, pi.smul_apply,
        fin.sum_univ_cast_succ, fin.init, coe_anon],
      ext x,
      show _ < _ ↔ _ < _,
      simp only [neg_mul_eq_neg_mul_symm, finset.sum_neg_distrib, mul_assoc, ← finset.mul_sum],
      rw [← neg_add, ← mul_add, ← sub_lt_zero, sub_eq_add_neg, neg_neg, ← mul_lt_mul_left hc],
      simp only [mul_add, mul_inv_cancel_left', ne_of_gt hc, ne.def, not_false_iff, mul_zero],
      rw [add_left_comm, add_assoc], }, }
end

variables (K)

lemma semilinear_function_family_is_isolating :
  (semilinear_function_family K K).is_isolating :=
begin
  rintros n s h,
  cases h with f g f g,
  { obtain ⟨ic, H⟩ := semilinear_function_family_eq_constraint (f - g),
    use ic, rw H, ext, rw ← sub_eq_zero, exact iff.rfl },
  { obtain ⟨ic, H⟩ := semilinear_function_family_lt_constraint (f - g),
    use ic, rw H, ext, rw ← sub_lt_zero, exact iff.rfl }
end

end semilinear

variables (K' : Type u) [discrete_linear_ordered_field K']

instance discrete_linear_ordered_field.DUNLO : DUNLO K' :=
{ .. ‹discrete_linear_ordered_field K'› }

def semilinear : struc K' :=
struc_of_isolating' (semilinear_function_family_is_isolating K')

lemma semilinear_o_minimal : o_minimal (semilinear K') :=
by apply o_minimal_of_isolating

end o_minimal
