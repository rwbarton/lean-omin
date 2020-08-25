import for_mathlib.tmp
import o_minimal.examples.from_finite_inters

namespace o_minimal

open_locale finvec

universe u

variables (R : Type u)

/-
Let R be any type. A *function family* on R consists of,
for each n, a family of functions Rⁿ → R, such that:

* All constant functions belong to the family.
* All coordinate functions belong to the family.
[TODO: We could reduce the above to constants R⁰ → R and the identity R¹ → R
 by using the extension property we require below.]
* Functions can be "extended" by adding irrelevant arguments on the left or right.
  That is, if f : Rⁿ → R belongs to the family, then the functions gₗ and gᵣ defined by
    gₗ(y, x₁, ..., xₙ) = f(x₁, ..., xₙ)
    gᵣ(x₁, ..., xₙ, y) = f(x₁, ..., xₙ)
  also belong to the family.

We do not require any other properties (like closure under composition),
even though in practice they would always be satisfied.

Examples:
- only constants and coordinate functions;
- all K-linear functions (where R is a K-module);
- all polynomial functions (where R is a ring).

We use a separate indexing type `carrier` to represent the functions
(rather than something like `Π (n : ℕ), set ((fin n → R) → R)`)
to make it easier to operate on the functions in a specific context
(for example, to simplify constraints).

TODO: Probably make argument `n` of `to_fun` implicit.
TODO: These {n : ℕ} binders are really annoying.
-/
structure function_family : Type (u+1) :=
(carrier : Π (n : ℕ), Type u)
(to_fun : Π (n : ℕ), carrier n → (fin n → R) → R)
(const : Π {n : ℕ} (r : R), carrier n)
(to_fun_const :
  ∀ {n : ℕ} {r : R}, to_fun n (const r) = λ _, r)
(coord : Π {n : ℕ} (i : fin n), carrier n)
(to_fun_coord :
  ∀ {n : ℕ} {i : fin n}, to_fun n (coord i) = λ x, x i)
(extend_left : Π {n : ℕ}, carrier n → carrier (n+1))
(to_fun_extend_left :
  ∀ {n : ℕ} (f : carrier n), to_fun (n+1) (extend_left f) = to_fun n f ∘ fin.tail)
(extend_right : Π {n : ℕ}, carrier n → carrier (n+1))
(to_fun_extend_right :
  ∀ {n : ℕ} (f : carrier n), to_fun (n+1) (extend_right f) = to_fun n f ∘ fin.init)

instance has_coe_to_fun.function_family : has_coe_to_fun (function_family R) :=
⟨_, function_family.carrier⟩

instance has_coe_to_fun.F (F : function_family R) (n : ℕ) : has_coe_to_fun (F n) :=
⟨_, F.to_fun n⟩

-- TODO: Make judicious use of these lemmas
@[simp] lemma function_family.const_app (F : function_family R) {n : ℕ} {r : R} {x : fin n → R} :
  F.const r x = r :=
congr_fun (function_family.to_fun_const F) x

@[simp] lemma function_family.coord_app (F : function_family R) {n : ℕ} {i : fin n} {x} :
  F.coord i x = x i :=
congr_fun (function_family.to_fun_coord F) x

@[simp] lemma function_family.extend_left_app (F : function_family R) {n : ℕ} {f : F n} {x} :
  F.extend_left f x = f (fin.tail x) :=
congr_fun (F.to_fun_extend_left f) x

@[simp] lemma function_family.extend_right_app (F : function_family R) {n : ℕ} {f : F n} {x} :
  F.extend_right f x = f (fin.init x) :=
congr_fun (F.to_fun_extend_right f) x

@[simp] lemma function_family.to_fun_eq_coe (F : function_family R) {n : ℕ} {f : F n} :
  F.to_fun n f = f := rfl

section simple

-- Simple functions: just constants and coordinates.

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

end simple

section linear_order

/-
Now suppose that the type R has an ordering.
Relative to a fixed function family F, we define a *primitive set*
to be a set of one of the forms
  {x | f(x) = g(x)},  {x | f(x) < g(x)}
where f and g are functions belonging to F.
We assume that R is linearly ordered,
so that the complement of such a set is a finite union of sets of the same form.

We'll define a basic set to be a finite intersection of primitive sets
and a definable set to be a finite union of basic sets.
Our aim in this module is to describe conditions
under which the definable sets formed in this way make up an o-minimal structure.
-/

variables {R} [linear_order R] (F : function_family R)

inductive constrained {n : ℕ} : set (fin n → R) → Prop
| EQ (f g : F n) : constrained {x | f x = g x}
| LT (f g : F n) : constrained {x | f x < g x}

variables {F}

lemma constrained.r_prod {n : ℕ} {s : set (fin n → R)} (hs : constrained F s) :
  constrained F (U 1 ⊠ s) :=
begin
  rcases hs with ⟨f,g⟩|⟨f,g⟩,
  { convert constrained.EQ (F.extend_left f) (F.extend_left g) using 1,
    { exact add_comm _ _ },
    { convert finvec.r_prod_eq,
      ext x,
      -- TODO: add lemma for extend_left stated in terms of coercions
      change F.to_fun _ (F.extend_left f) x = F.to_fun _ (F.extend_left g) x ↔ _,
      rw [F.to_fun_extend_left, F.to_fun_extend_left],
      refl } },
  { convert constrained.LT (F.extend_left f) (F.extend_left g) using 1,
    { exact add_comm _ _ },
    { convert finvec.r_prod_eq,
      ext x,
      change F.to_fun _ (F.extend_left f) x < F.to_fun _ (F.extend_left g) x ↔ _,
      rw [F.to_fun_extend_left, F.to_fun_extend_left],
      refl } },
end

lemma constrained.prod_r {n : ℕ} {s : set (fin n → R)} (hs : constrained F s) :
  constrained F (s ⊠ U 1) :=
begin
  rcases hs with ⟨f,g⟩|⟨f,g⟩,
  { convert constrained.EQ (F.extend_right f) (F.extend_right g),
    convert finvec.prod_r_eq,
    ext x,
    -- TODO: add lemma for extend_right stated in terms of coercions
    change F.to_fun _ (F.extend_right f) x = F.to_fun _ (F.extend_right g) x ↔ _,
    rw [F.to_fun_extend_right, F.to_fun_extend_right],
    refl },
  { convert constrained.LT (F.extend_right f) (F.extend_right g) using 1,
    convert finvec.prod_r_eq,
    ext x,
    change F.to_fun _ (F.extend_right f) x < F.to_fun _ (F.extend_right g) x ↔ _,
    rw [F.to_fun_extend_right, F.to_fun_extend_right],
    refl },
end

-- TODO: for_mathlib
@[simp] lemma lt_self_iff_false {α : Type*} [preorder α] (x : α) : (x < x) ↔ false :=
by { rw iff_false, exact lt_irrefl x }

section empty

/-
The assumption that R is nonempty is annoying, mainly because it shouldn't really be needed.
The problem is that it's *almost* true that the projection of a basic set is basic,
if we define a basic set to be a finite intersection of constrained ones,
and in the structure defined by just (R, <), for example.
The issue is that ∅ = {x | x < x} ⊆ R¹ is basic, but its projection to R⁰ is not basic,
because there are no simple functions at all on R⁰ when R is empty!
It is still definable though, as the empty union.

Options for dealing with this include:
0. [the current choice] Just assume R is nonempty here, because it eventually will be anyways.
1. Work with "basic or empty" sets in the context of isolating families.
2. Include `empty` as another constructor of `constrained`,
   and let it affect the definition of the eventual definable sets.
3. Include `empty` as another constructor of `constrained`,
   but then prove we get the same definable sets in the end as if it didn't exist.
   (Especially if we only add `constrained.empty` for `n = 0`, this doesn't seem too taxing.)
-/
lemma constrained.empty [h : nonempty R] {n : ℕ} : constrained F (∅ : set (fin n → R)) :=
begin
  casesI h with r,
  convert constrained.LT (F.const r) (F.const r),
  simp
end

end empty

variables (F) (D B P : Π ⦃n : ℕ⦄, set (set (fin n → R)))

/-- Hypotheses for a structure. -/
structure function_family_struc_hypotheses : Prop :=
(definable_iff_finite_union_basic :
  ∀ {n} {s : set (fin n → R)}, D s ↔ s ∈ finite_union_closure (@B n))
(basic_iff_finite_inter_primitive :
  ∀ {n} {s : set (fin n → R)}, B s ↔ s ∈ finite_inter_closure (@P n))
(primitive_iff_constrained :
  ∀ {n} {s : set (fin n → R)}, P s ↔ constrained F s)
(definable_proj1_basic :
  ∀ {n} {s : set (fin (n+1) → R)}, B s → D (finvec.left '' s))

variables {F D B P}

-- Strategy: Conclude `finite_inter_struc_hypotheses D B P`.
-- First we work under the assumption that `P` is `constrained F`.

local notation `P₀` := (λ {n : ℕ}, constrained F)
-- local notation `B₀` := (λ {n : ℕ}, finite_inter_closure (@P n))
-- local notation `D₀` := (λ {n : ℕ}, finite_union_closure (finite_inter_closure (@P n)))

private lemma key
  (H : function_family_struc_hypotheses F D B P₀) :
  finite_inter_struc_hypotheses D B P₀ :=
have basic_of_constrained : ∀ {n} {s : set (fin n → R)}, constrained F s → B s,
from λ n s hs,
  (function_family_struc_hypotheses.basic_iff_finite_inter_primitive H).mpr
    (finite_inter_closure.basic hs),
{ definable_iff_finite_union_basic := H.definable_iff_finite_union_basic,
  basic_iff_finite_inter_primitive := H.basic_iff_finite_inter_primitive,
  definable_compl_primitive := begin
    rintros n s (⟨f,g⟩|⟨f,g⟩); rw H.definable_iff_finite_union_basic,
    { convert_to ({x | f x < g x} ∪ {x | g x < f x}) ∈ _,
      { ext x, exact ne_iff_lt_or_gt },
      apply finite_union_closure.union; apply finite_union_closure.basic; apply basic_of_constrained,
      { exact constrained.LT f g },
      { exact constrained.LT g f } },
    { convert_to ({x | f x = g x} ∪ {x | g x < f x}) ∈ _,
      { ext x, exact not_lt_iff_eq_or_lt }, -- library_search failed?
      apply finite_union_closure.union; apply finite_union_closure.basic; apply basic_of_constrained,
      { exact constrained.EQ f g },
      { exact constrained.LT g f } }
  end,
  basic_r_prod_primitive := λ n s hs, basic_of_constrained hs.r_prod,
  basic_primitive_prod_r := λ n s hs, basic_of_constrained hs.prod_r,
  definable_eq_outer := λ n,
    (function_family_struc_hypotheses.definable_iff_finite_union_basic H).mpr $
    finite_union_closure.basic $
    basic_of_constrained $
    begin
      convert constrained.EQ (F.coord 0) (F.coord (fin.last n)),
      ext x,
      -- TODO: Another lemma
      change _ ↔ F.to_fun _ (F.coord 0) x = F.to_fun _ (F.coord (fin.last n)) x,
      rw [F.to_fun_coord, F.to_fun_coord]
    end,
  definable_proj1_basic := H.definable_proj1_basic }

variables (H : function_family_struc_hypotheses F D B P)
include H

lemma function_family_struc_hypotheses.finite_inter_struc_hypotheses :
  finite_inter_struc_hypotheses D B P :=
begin
  have : @P = @constrained _ _ F,
  { ext, apply H.primitive_iff_constrained },
  subst P,
  exact key H
end

def struc_of_function_family : struc R :=
struc_of_finite_inter H.finite_inter_struc_hypotheses

end linear_order

section o_minimal

variables {R} [DUNLO R] (F : function_family R) (D B P : Π ⦃n : ℕ⦄, set (set (fin n → R)))

structure function_family_o_minimal_hypotheses extends function_family_struc_hypotheses F D B P : Prop :=
(tame_of_constrained : ∀ {s : set (fin 1 → R)}, constrained F s → tame {r | (λ _, r : fin 1 → R) ∈ s})

variables {F D B P} (H : function_family_o_minimal_hypotheses F D B P)

lemma o_minimal_of_function_family :
  o_minimal (struc_of_function_family H.to_function_family_struc_hypotheses) :=
have definable_of_constrained : ∀ {n} {s : set (fin n → R)}, constrained F s → D s := λ n s hs,
  -- TODO: This is terrible
  (function_family_struc_hypotheses.definable_iff_finite_union_basic H.to_function_family_struc_hypotheses).mpr $
  finite_union_closure.basic $
  (function_family_struc_hypotheses.basic_iff_finite_inter_primitive H.to_function_family_struc_hypotheses).mpr $
  finite_inter_closure.basic $
  (function_family_struc_hypotheses.primitive_iff_constrained H.to_function_family_struc_hypotheses).mpr hs,
o_minimal_of_finite_inter
{ definable_lt := by simpa using definable_of_constrained (constrained.LT (F.coord 0) (F.coord 1)),
  definable_const := λ r, by simpa using definable_of_constrained (constrained.EQ (F.coord 0) (F.const r)),
  tame_of_primitive := λ s hs, by { rw H.primitive_iff_constrained at hs, exact H.tame_of_constrained hs },
  .. H.to_function_family_struc_hypotheses.finite_inter_struc_hypotheses }

end o_minimal

end o_minimal
