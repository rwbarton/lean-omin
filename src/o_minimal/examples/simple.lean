import o_minimal.examples.isolating

-- Simple functions: just constants and coordinates.
-- We prove they determine an o-minimal structure on any DUNLO.

namespace o_minimal

universe u

variables (R : Type u)

/-- Codes for simple functions: constants and coordinate projections. -/
inductive simple_function_type (n : ℕ) : Type u
| const : Π (r : R),     simple_function_type
| coord : Π (i : fin n), simple_function_type

namespace simple_function_type

variables {R}

/-- The interpretation of a code for a simple function. -/
protected def to_fun {n : ℕ} : simple_function_type R n → (fin n → R) → R
| (const r) := λ x, r
| (coord i) := λ x, x i

/-- (The code for) the extension of a simple function by an argument on the left. -/
def extend_left {n : ℕ} :
  simple_function_type R n → simple_function_type R (n+1)
| (const r) := const r
| (coord i) := coord i.succ

lemma to_fun_extend_left {n : ℕ} (f : simple_function_type R n) :
  f.extend_left.to_fun = f.to_fun ∘ fin.tail :=
by cases f; ext; simp [simple_function_type.to_fun, extend_left, fin.tail]

def extend_right {n : ℕ} :
  simple_function_type R n → simple_function_type R (n+1)
| (const r) := const r
| (coord i) := coord i.cast_succ

lemma to_fun_extend_right {n : ℕ} (f : simple_function_type R n) :
  f.extend_right.to_fun = f.to_fun ∘ fin.init :=
by cases f; ext; simp [simple_function_type.to_fun, extend_right, fin.init]

end simple_function_type

open simple_function_type

/-- The family of simple functions, consisting of just constants and coordinate projections. -/
def simple_function_family : function_family R :=
{ carrier := simple_function_type R,
  to_fun := @simple_function_type.to_fun R,
  const := λ n r, const r,
  to_fun_const := λ n r, rfl,
  coord := λ n i, coord i,
  to_fun_coord := λ n i, rfl,
  extend_left := @extend_left R,
  to_fun_extend_left := @to_fun_extend_left R,
  extend_right := @extend_right R,
  to_fun_extend_right := @to_fun_extend_right R }

-- TODO: Add some simp lemmas, phrased in terms of coercions

variables {R}

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

variables [DUNLO R]

lemma simple_function_family_is_isolating : (simple_function_family R).is_isolating :=
begin
  -- Analyze the given constraint and push down the functions if possible: 8 cases
  rintros n _ hs,
  rcases hs with (⟨f,g⟩|⟨f,g⟩); clear hs;
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

/-- The structure defined by (R, <). -/
def simple_struc : struc R := struc_of_isolating' simple_function_family_is_isolating

/-- The structure defined by (R, <) is o-minimal. -/
instance : o_minimal (simple_struc : struc R) := by apply o_minimal_of_isolating

end o_minimal
