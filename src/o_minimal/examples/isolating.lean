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

-- TODO: should we use `fin.init x` instead of `F.extend_right`?
-- (They're equal by hypothesis, but not definitionally.)
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

-- Henceforth, we assume the family F is isolating.
variables (hF : F.is_isolating)

-- Next, we show how to put a collection of constraints into "triangular form".

/-- The constraints on the last variable xₙ in a triangular form:
either a single constraint of the form xₙ = f(x'),
or two finite sets of constraints of the forms {gᵢ(x') < xₙ} and {xₙ < hⱼ(x')}.
(Here as usual x' denotes the remaining variables.)

No constraint (i.e. `true`) is represented by the second case, with empty sets.
`false` is not represented here; instead it gets pushed down to the base case
of the triangular form.
-/
inductive last_variable_constraints (n : ℕ) : Type u
| eq (f : F n) : last_variable_constraints
| between (L R : finset (F n)) : last_variable_constraints

namespace last_variable_constraints

variables {F}

/-- The set defined by some last variable constraints. -/
def to_set {n : ℕ} :
  Π (c : last_variable_constraints F n), set (fin (n+1) → R)
| (eq f) := {x | x (fin.last n) = f (fin.init x)}
| (between L R) :=
  {x | (∀ (g : F n), g ∈ L → g (fin.init x) < x (fin.last n)) ∧
       (∀ (h : F n), h ∈ R → x (fin.last n) < h (fin.init x))}

end last_variable_constraints

/-- A conjunction of constraints in n variables in "triangular form".
In the base case (n = 0) we have the logical constants true and false.
In the inductive case of n+1 variables we have
a conjunction of constraints on the last variable
and a triangular system of constraints on the first n variables.
-/
inductive triangular_constraints : Π (n : ℕ), Type u
| tt : triangular_constraints 0
| ff : triangular_constraints 0
| step {n : ℕ} :
    last_variable_constraints F n → triangular_constraints n → triangular_constraints (n+1)

namespace triangular_constraints

variables {F}

/-- The set defined by a triangular system of constraints. -/
def to_set :
  Π {n : ℕ} (t : triangular_constraints F n), set (fin n → R)
| 0 tt := univ
| 0 ff := ∅
| (n+1) (step c t') := c.to_set ∩ {x | fin.init x ∈ t'.to_set}

end triangular_constraints

-- Now we prove that triangular systems of constraints
-- have the same expressive power as arbitrary conjunctions of constraints.

-- First we show that any set defined by a triangular system of constraints
-- is also defined by a conjunction of constraints.

/-
lemma finite_inter_constrained_of_triangular {n : ℕ} (t : triangular_constraints F n) :
  finite_inter_closure (constrained F) t.to_set :=
-- TODO: Hang on, isn't this false? What do we plan to do with `ff : triangular_constraints 0`?
-- well, here is a goofy way out:
-- * if R is nonempty, then we can use `r < r` for some choice of `r : R`;
-- * if R is empty, then we can use `univ` because then `univ = ∅`!
-- Maybe the correct way to do this though would be to include `∅` as a "constrained" set.
sorry
-/

-- To prove the reverse implication, it suffices to show that
-- * a single constraint can be expressed as a triangular system [TODO];
-- * the sets defined by triangular systems of constraints are closed under finite intersections.

-- The idea is to combine the last variable constraints and handle the rest by induction.
-- When combining two last variable constraints, we might face two equality constraints on xₙ.
-- In this case, we keep one of them and push the equation between the two right hand sides
-- to a constraint on the previous variables.

end o_minimal
