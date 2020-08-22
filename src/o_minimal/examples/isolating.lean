import o_minimal.examples.from_function_family

/-
A function family on a linear order R is *isolating*
if any constraint f(x) = g(x) or f(x) < g(x) in n+1 variables x = (x₀, ..., xₙ)
is equivalent to one of the below:
- true;
- false;
- a constraint of one of the forms
  xₙ = h(x₀, ..., xₙ₋₁) or
  xₙ < h(x₀, ..., xₙ₋₁) or
  xₙ > h(x₀, ..., xₙ₋₁);
- a constraint f'(x) = g'(x) or f'(x) < g'(x)
  where f' and g' are functions (belonging to the family)
  of only the first n variables (x₀, ..., xₙ₋₁).
We refer to the last case as "pushing" the constraint down to
a constraint in only n variables.

We show that if a function family is isolating
then the associated definable sets form an o-minimal structure.

Examples:
* The family of simple functions (just constant functions and coordinate projections)
  is isolating, and defines the smallest o-minimal structure.
* Let R be an ordered vector space over an ordered field K (most commonly, R = K).
  Then the functions of the form x ↦ k₀ x₀ + ... + kₙ₋₁ xₙ₋₁ + r (with kᵢ ∈ K, r ∈ R)
  form an isolating family, which defines the o-minimal structure of semilinear sets.
-/

namespace o_minimal

open set

universe u

variables {R : Type u} [linear_order R]
variables (F : function_family R)

/-- An isolated form for a constraint in n+1 variables:
either the last variable stands alone on one side of the constraint
or does not appear at all. -/
-- TODO: it quite looks as though we ought to have a data form of `constrained`
inductive isolated_constraint (n : ℕ) : Type u
| tt : isolated_constraint                   -- true
| ff : isolated_constraint                   -- false
| eq (h : F n) : isolated_constraint         -- xₙ = h(x')
| lt (h : F n) : isolated_constraint         -- xₙ < h(x')
| gt (h : F n) : isolated_constraint         -- xₙ > h(x')
| push_eq (f g : F n) : isolated_constraint  -- f(x') = g(x')
| push_lt (f g : F n) : isolated_constraint  -- f(x') < g(x')

namespace isolated_constraint

variables {F}

def to_set {n : ℕ} :
  isolated_constraint F n → set (fin (n+1) → R)
| tt := univ
| ff := ∅
| (eq h) := {x | x (fin.last n) = F.extend_right h x}
| (lt h) := {x | x (fin.last n) < F.extend_right h x}
| (gt h) := {x | x (fin.last n) > F.extend_right h x}
| (push_eq f g) := {x | F.extend_right f x = F.extend_right g x}
| (push_lt f g) := {x | F.extend_right f x < F.extend_right g x}

end isolated_constraint

/-- A function family is *isolating* if any constraint in n+1 variables
is equivalent to an isolated constraint. -/
-- TODO: Should `isolate` be data?
-- Currently `constrained` only exists as a `Prop`, should it be data?
-- TODO: Should isolating_family be a mix-in?
def function_family.is_isolating : Prop :=
∀ {n : ℕ} {s : set (fin (n+1) → R)}, constrained F s →
∃ (ic : isolated_constraint F n), ic.to_set = s

section simple
-- TODO: Move all contents on simple functions to their own module
-- once we've shown they generate an o-minimal structure.

/-- A simple function in n+1 variables is either the last coordinate
or can be pushed down to a simple function in n variables. -/
lemma simple.last_coord_or_push {n : ℕ} : 
  ∀ (f : simple_function_family R (n+1)),
  f = (simple_function_family R).coord (fin.last n) ∨
  ∃ f', f = (simple_function_family R).extend_right f'
| (simple_function_type.const r) := or.inr ⟨simple_function_type.const r, rfl⟩
| (simple_function_type.coord i) :=
begin
  -- TODO: simplify & share logic with `fin.snoc`?
  by_cases h : i < fin.last n,
  { refine or.inr ⟨simple_function_type.coord (fin.cast_lt i h), _⟩,
    change _ = simple_function_type.coord _,
    rw fin.cast_succ_cast_lt i h },
  { replace h := fin.eq_last_of_not_lt h,
    subst i,
    refine or.inl rfl }
end

-- TODO: for_mathlib
@[simp] lemma lt_self_iff_false {α : Type*} [preorder α] (x : α) : (x < x) ↔ false :=
by { rw iff_false, exact lt_irrefl x }

lemma simple_function_family_is_isolating : (simple_function_family R).is_isolating :=
begin
  -- Analyze the given constraint and push down the functions if possible: 8 cases
  rintros n _ (⟨f,g⟩|⟨f,g⟩); clear a; -- what is `a`??
    rcases simple.last_coord_or_push f with rfl|⟨f', rfl⟩;
    rcases simple.last_coord_or_push g with rfl|⟨g', rfl⟩,
  { refine ⟨isolated_constraint.tt, _⟩,
    simp [isolated_constraint.to_set], refl },
  { exact ⟨isolated_constraint.eq g', rfl⟩ },
  { refine ⟨isolated_constraint.eq f', _⟩,
    conv_rhs { funext, rw eq_comm },
    refl },
  { exact ⟨isolated_constraint.push_eq f' g', rfl⟩ },
  { refine ⟨isolated_constraint.ff, _⟩,
    simp [isolated_constraint.to_set], refl },
  { refine ⟨isolated_constraint.lt g', rfl⟩ },
  { refine ⟨isolated_constraint.gt f', _⟩,
    conv_rhs { funext, rw ←gt_iff_lt },
    refl },
  { refine ⟨isolated_constraint.push_lt f' g', rfl⟩ }
end

end simple

end o_minimal
