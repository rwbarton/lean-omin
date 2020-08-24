import o_minimal.examples.from_function_family
import o_minimal.o_minimal

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
open_locale finvec

universe u

variables {R : Type u}
variables (F : function_family R)

section linear_order

variables [linear_order R]

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
∀ ⦃n : ℕ⦄ ⦃s : set (fin (n+1) → R)⦄, constrained F s →
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
| between (lower upper : finset (F n)) : last_variable_constraints
-- Remark. We'll have to use classical to form the union of `finset`s.
-- A constructive treatment could use lists instead.

namespace last_variable_constraints

variables {F}

/-- The set defined by some last variable constraints. -/
def to_set {n : ℕ} :
  Π (c : last_variable_constraints F n), set (fin (n+1) → R)
| (eq f) := {x | x (fin.last n) = f (fin.init x)}
| (between lower upper) :=
    (⋂ (g : F n) (H : g ∈ lower), {x | g (fin.init x) < x (fin.last n)}) ∩
    (⋂ (h : F n) (H : h ∈ upper), {x | x (fin.last n) < h (fin.init x)})

@[simp]
lemma to_set_empty_empty {n : ℕ} : (between ∅ ∅ : last_variable_constraints F n).to_set = univ :=
by simp [to_set]

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

section triangularize

-- Now we prove that triangular systems of constraints
-- have the same expressive power as arbitrary conjunctions of constraints.
-- For technical reasons we now assume `R` is nonempty (see `constrained.empty`).
variables [nonempty R]

-- First we show that any set defined by a triangular system of constraints
-- is also defined by a conjunction of constraints ("basic").

variables {F}

lemma last_variable_constraints.to_set_basic {n : ℕ} :
  ∀ (c : last_variable_constraints F n),
  finite_inter_closure (constrained F) c.to_set
| (last_variable_constraints.eq f) :=
begin
  apply finite_inter_closure.basic,
  convert constrained.EQ (F.coord (fin.last n)) (F.extend_right f),
  ext x,
  -- TODO: simplify this proof
  change x (fin.last n) = f (fin.init x) ↔ F.to_fun _ (F.coord (fin.last n)) x = F.to_fun _ (F.extend_right f) x,
  rw [F.to_fun_coord, F.to_fun_extend_right],
  refl
end
| (last_variable_constraints.between lower upper) :=
begin
  apply finite_inter_closure.inter;
    refine closed_under_finite_inters_finite_inter_closure.mem_fInter _ _;
    intros i _;
    apply finite_inter_closure.basic,                 -- TODO: use rintros -
  { change constrained F _,
    convert constrained.LT (F.extend_right i) (F.coord (fin.last n)),
    ext x,
    -- TODO: simplify this proof
    change _ ↔ F.to_fun _ (F.extend_right i) x < F.to_fun _ (F.coord (fin.last n)) x,
    rw [F.to_fun_coord, F.to_fun_extend_right],
    refl },
  { change constrained F _,
    convert constrained.LT (F.coord (fin.last n)) (F.extend_right i),
    ext x,
    -- TODO: simplify this proof
    change _ ↔ F.to_fun _ (F.coord (fin.last n)) x < F.to_fun _ (F.extend_right i) x,
    rw [F.to_fun_coord, F.to_fun_extend_right],
    refl },
end

lemma triangular_constraints.to_set_basic :
  ∀ {n : ℕ} (t : triangular_constraints F n),
  finite_inter_closure (constrained F) t.to_set
| 0 triangular_constraints.tt := finite_inter_closure.univ
| 0 triangular_constraints.ff := finite_inter_closure.basic constrained.empty
| (n+1) (triangular_constraints.step c t') := begin
  refine finite_inter_closure.inter c.to_set_basic _,
  have IH : finite_inter_closure (constrained F) t'.to_set := t'.to_set_basic,
  -- TODO: move this somewhere sensible
  have rw_me : {x : fin (n+1) → R | fin.init x ∈ t'.to_set} = t'.to_set ⊠ U 1,
  { ext x,
    simp [finvec.external_prod_def], refl },
  change finite_inter_closure (constrained F) {x : fin (n + 1) → R | fin.init x ∈ t'.to_set},
  rw rw_me,
  -- TODO: move this somewhere sensible. Copied from `from_finite_inters`.
  have : preserves_finite_inters (λ s : set (fin n → R), s ⊠ U 1) := begin
    split; intros; ext; simp [finvec.external_prod_def]
  end,
  refine this.bind _ t'.to_set IH,
  { intros s hs,
    apply finite_inter_closure.basic,
    exact hs.prod_r }
end

-- To prove the reverse implication, it suffices to show that
-- * a single constraint can be expressed as a triangular system;
-- * the sets defined by triangular systems of constraints are closed under finite intersections.

-- Preliminary constructions.

def triangular_constraints.extend_right {n : ℕ} (t : triangular_constraints F n) :
  triangular_constraints F (n+1) :=
triangular_constraints.step (last_variable_constraints.between ∅ ∅) t

@[simp]
lemma triangular_constraints.to_set_extend_right {n : ℕ} {t : triangular_constraints F n} :
  t.extend_right.to_set = {x | fin.init x ∈ t.to_set} :=
by simp [triangular_constraints.extend_right, triangular_constraints.to_set]

variables (F)

def triangular_constraints.ff_n : Π (n : ℕ), triangular_constraints F n
| 0 := triangular_constraints.ff
| (n+1) := (triangular_constraints.ff_n n).extend_right

def triangular_constraints.tt_n : Π (n : ℕ), triangular_constraints F n
| 0 := triangular_constraints.tt
| (n+1) := (triangular_constraints.tt_n n).extend_right

variables {F}

@[simp]
lemma triangular_constraints.to_set_ff_n {n : ℕ} : (triangular_constraints.ff_n F n).to_set = ∅ :=
begin
  induction n with n ih,
  { refl },
  { simp [triangular_constraints.ff_n, ih] }
end

@[simp]
lemma triangular_constraints.to_set_tt_n {n : ℕ} : (triangular_constraints.tt_n F n).to_set = univ :=
begin
  induction n with n ih,
  { refl },
  { simp [triangular_constraints.tt_n, ih] }
end

def triangular_constraints.last_variable_constraint {n : ℕ} (c : last_variable_constraints F n) :
  triangular_constraints F (n+1) :=
triangular_constraints.step c (triangular_constraints.tt_n F _)

@[simp]
lemma triangular_constraints.to_set_last_variable_constraint
  {n : ℕ} {c : last_variable_constraints F n} :
  (triangular_constraints.last_variable_constraint c).to_set = c.to_set :=
by simp [triangular_constraints.to_set, triangular_constraints.last_variable_constraint]

-- TODO: for_mathlib. Write a better proof.
lemma eq_empty_or_univ {α : Type*} [subsingleton α] (s : set α) : s = ∅ ∨ s = univ :=
begin
  classical,
  by_cases h : s = univ,
  { exact or.inr h },
  { left,
    rw eq_empty_iff_forall_not_mem,
    intro x,
    contrapose! h,
    ext y,
    have : x = y, by cc,
    subst y,
    simp [h] }
end

/-- Any subset of R⁰ = * can be described by a triangular system of constraints. -/
lemma triangular_constraints.zero {s : set (fin 0 → R)} :
  ∃ t : triangular_constraints F 0, t.to_set = s :=
begin
  -- We use classical here.
  -- If we carried a `constrained F s` hypothesis around,
  -- we'd see it really just needs the decidability of = and < on R.
  rcases eq_empty_or_univ s with rfl|rfl,
  { exact ⟨triangular_constraints.ff, rfl⟩ },
  { exact ⟨triangular_constraints.tt, rfl⟩ }
end

include hF

-- For the first part, we use the isolating property of F
-- to describe s by an isolated constraint, working by induction.
lemma triangular_constraints_of_constraint {n : ℕ} {s : set (fin n → R)} (hs : constrained F s) :
  ∃ t : triangular_constraints F n, t.to_set = s :=
begin
  induction n with n IH,
  { exact triangular_constraints.zero },
  { obtain ⟨i, rfl⟩ := hF hs, clear hs,
    rcases i with _|_|h|h|h|⟨f,g⟩|⟨f,g⟩,
    -- true or false; we built these earlier.
    { exact ⟨triangular_constraints.tt_n F _, triangular_constraints.to_set_tt_n⟩ },
    { exact ⟨triangular_constraints.ff_n F _, triangular_constraints.to_set_ff_n⟩ },
    -- an isolated constraint involving the last variable.
    { refine ⟨triangular_constraints.last_variable_constraint (last_variable_constraints.eq h), _⟩,
      simp [last_variable_constraints.to_set, isolated_constraint.to_set] },
    { refine ⟨triangular_constraints.last_variable_constraint (last_variable_constraints.between ∅ {h}), _⟩,
      simp [last_variable_constraints.to_set, isolated_constraint.to_set] },
    { refine ⟨triangular_constraints.last_variable_constraint (last_variable_constraints.between {h} ∅), _⟩,
      simp [last_variable_constraints.to_set, isolated_constraint.to_set] },
    -- a constraint that can be pushed down to the previous level, using the inductive hypothesis.
    { obtain ⟨t, ht⟩ := IH (constrained.EQ f g),
      refine ⟨t.extend_right, _⟩,
      simp [ht, isolated_constraint.to_set] },
    { obtain ⟨t, ht⟩ := IH (constrained.LT f g),
      refine ⟨t.extend_right, _⟩,
      simp [ht, isolated_constraint.to_set] } }
end

-- Now we show the sets described by triangular constraints are closed under finite intersections.
-- We already checked nullary intersections (via `.tt_n`),
-- so it remains to handle binary intersections.
-- The idea is to combine the last variable constraints and handle the rest by induction.
-- For the last variable constraints, there are two possibilities.
-- * If at least one is an equality constraint, we pick one such and keep it
--   and use it to rewrite the other constraint(s) in terms of earlier variables
--   (using the inductive hypothesis and the fact we've already shown that
--   a single constraint can be put in triangular form).
-- * Otherwise, both are between constraints and we can simply merge the sets.

lemma triangular_constraints.closed_under_finite_intersections {n : ℕ} :
  closed_under_finite_inters {s | ∃ t : triangular_constraints F n, t.to_set = s} :=
begin
  induction n with n IH;
    refine { mem_univ := ⟨triangular_constraints.tt_n F _, by simp⟩, mem_inter := _ },
  { intros, exact triangular_constraints.zero }, change n.succ with n + 1,
  -- Now equipped with the inductive hypothesis,
  -- we handle the case of an equation as one of the last variable constraints.
  have eq_case :
    ∀ (f : F n) (t₁' : triangular_constraints F n) (t₂ : triangular_constraints F (n+1)),
    ∃ t₃ : triangular_constraints F (n + 1),
    t₃.to_set =
      (triangular_constraints.step (last_variable_constraints.eq f) t₁').to_set ∩ t₂.to_set,
  { intros f t₁' t₂,
    set t₁ := triangular_constraints.step (last_variable_constraints.eq f) t₁',
    rcases t₂ with _ | _ | ⟨_, c₂, t₂'⟩,
    -- Using the equation that the last variable equals f applied to the earlier ones,
    -- convert the last variable constraints of t₂ to constraints on only earlier variables.
    -- (The new constraints cut out the same set as the old last variable constraints
    -- at least when restricted to the set where t₁ holds.)
    have : ∃ t₂'' : triangular_constraints F n,
      t₁.to_set ∩ c₂.to_set = t₁.to_set ∩ {x | fin.init x ∈ t₂''.to_set},
    { -- We actually only care about the equality on the last variable, not all of t₁.
      suffices : ∃ t₂'' : triangular_constraints F n,
        {x : fin (n + 1) → R | x (fin.last n) = f (fin.init x)} ∩ c₂.to_set =
        {x : fin (n + 1) → R | x (fin.last n) = f (fin.init x)} ∩ {x | fin.init x ∈ t₂''.to_set},
      { obtain ⟨t₂'', h⟩ := this,
        refine ⟨t₂'', _⟩,
        change (_ ∩ _) ∩ _ = (_ ∩ _) ∩ _,
        conv_lhs { rw ←inter_right_comm },
        conv_rhs { rw ←inter_right_comm },
        congr' 1,
        exact h },
      rcases c₂ with f₂ | ⟨lower₂, upper₂⟩,
      { -- Convert f(x) = f₂(x) into a triangular system.
        obtain ⟨t, ht⟩ := triangular_constraints_of_constraint hF (constrained.EQ f f₂),
        refine ⟨t, _⟩,
        -- TODO: maybe borrow proof ideas from the other case
        unfold last_variable_constraints.to_set,
        convert_to
          {x : fin (n + 1) → R | x (fin.last n) = f (fin.init x)} ∩
          {x : fin (n + 1) → R | f (fin.init x) = f₂ (fin.init x)} =
          {x : fin (n + 1) → R | x (fin.last n) = f (fin.init x)} ∩
          {x : fin (n + 1) → R | fin.init x ∈ triangular_constraints.to_set _},
        { ext x, simp only [mem_inter_iff, mem_set_of_eq], split; rintros ⟨_, _⟩; cc },
        congr,
        simp_rw ht,
        refl },
      { -- Convert each g(x) < f(x) for g ∈ lower₂, f(x) < h(x) for h ∈ upper₂
        -- into a triangular system, and then combine them:
        -- we can do this using the inductive hypothesis.
        let S : set (fin n → R) :=
          (⋂ (g : F n) (H : g ∈ lower₂), {x | g x < f x}) ∩
          (⋂ (h : F n) (H : h ∈ upper₂), {x | f x < h x}),
        obtain ⟨t, ht⟩ : ∃ t : triangular_constraints F n, t.to_set = S,
        { apply IH.mem_inter; apply IH.mem_fInter,
          { intros g H, exact triangular_constraints_of_constraint hF (constrained.LT g f) },
          { intros h H, exact triangular_constraints_of_constraint hF (constrained.LT f h) } },
        refine ⟨t, _⟩,
        ext x,
        simp only [mem_inter_iff, mem_set_of_eq],
        apply and_congr_right,
        intro hx,
        simp [last_variable_constraints.to_set, hx, ht] } },
    obtain ⟨t₂'', ht₂''⟩ := this,
    -- Using the inductive hypothesis, combine the constraints t₁', t₂' and t₂''.
    -- TODO: Can probably be expressed more efficiently using new IH form.
    -- Otherwise, maybe state a lemma for this IH.mem_inter ⟨_, rfl⟩ ⟨_, rfl⟩ pattern.
    obtain ⟨t₃', ht₃' : t₃'.to_set = t₂''.to_set ∩ t₂'.to_set⟩ := IH.mem_inter ⟨t₂'', rfl⟩ ⟨t₂', rfl⟩,
    obtain ⟨t₄', ht₄' : t₄'.to_set = t₁'.to_set ∩ t₃'.to_set⟩ := IH.mem_inter ⟨t₁', rfl⟩ ⟨t₃', rfl⟩,
    refine ⟨triangular_constraints.step (last_variable_constraints.eq f) t₄', _⟩,
    change _ = _ ∩ (_ ∩ _),
    rw [←inter_assoc, ht₂''],
    simp only [triangular_constraints.to_set, t₁, ht₂'', ht₃', ht₄'],
    ext x,
    simp only [mem_inter_iff, mem_set_of_eq],
    tauto },
  -- Main proof: case analysis on the constraints.
  -- If either is an equality, apply eq_case, possibly after swapping the constraints.
  rintros _ _ ⟨t₁, rfl⟩ ⟨t₂, rfl⟩,
  rcases t₁ with _ | _ | ⟨_, f₁ | ⟨lower₁, upper₁⟩, t₁'⟩, { apply eq_case },
  rcases t₂ with _ | _ | ⟨_, f₂ | ⟨lower₂, upper₂⟩, t₂'⟩, { simp_rw [inter_comm], apply eq_case },
  -- In the remaining case, both are between constraints.
  obtain ⟨t₃', ht₃'⟩ := IH.mem_inter ⟨t₁', rfl⟩ ⟨t₂', rfl⟩,
  classical,
  refine
    ⟨triangular_constraints.step
      (last_variable_constraints.between (lower₁ ∪ lower₂) (upper₁ ∪ upper₂))
      t₃', _⟩,
  ext,
  simp only [triangular_constraints.to_set, last_variable_constraints.to_set, ht₃'],
  rw [finset.bInter_inter, finset.bInter_inter],
  simp only [mem_inter_iff, mem_set_of_eq],
  tauto
end

-- Finally, summarize all the results of this section.

/-- The sets described by triangular systems are the same as
those defined by finitely many constraints. -/
lemma triangular_constraints_iff {n : ℕ} (s : set (fin n → R)) :
  finite_inter_closure (constrained F) s ↔ ∃ t : triangular_constraints F n, t.to_set = s :=
begin
  split,
  { apply preserves_finite_inters_id.bind'
      (triangular_constraints.closed_under_finite_intersections hF),
    intros s hs,
    exact triangular_constraints_of_constraint hF hs },
  { rintros ⟨t, rfl⟩, exact t.to_set_basic }
end

end triangularize

end linear_order

section DUNLO

section projection

-- TODO: `fin.init` and `fin.snoc` aren't great, resulting in some awkward phrasing here;
-- it's probably due to their dependent nature.
-- Compare a hypothetical
--   y ∈ fin.init '' s ↔ ∃ z : R, fin.snoc y z ∈ s
lemma mem_image_fin_init {n : ℕ} {s : set (fin (n+1) → R)} {y : fin n → R} :
  y ∈ s.image fin.init ↔ ∃ z : R, (fin.snoc y z : fin (n+1) → R) ∈ s :=
begin
  split; intro h,
  { obtain ⟨x, hx, rfl⟩ := h,
    refine ⟨x (fin.last n), _⟩,
    simpa using hx },
  { obtain ⟨z, hz⟩ := h,
    refine ⟨fin.snoc y z, hz, _⟩,
    simp }
end

variables [DUNLO R]

-- TODO: for_mathlib
lemma DUNLO_lemma (lower upper : finset R) :
  (∃ x, (∀ g ∈ lower, g < x) ∧ (∀ h ∈ upper, x < h)) ↔
  ∀ (g ∈ lower) (h ∈ upper), g < h :=
begin
  split,
  { rintro ⟨x, hx₁, hx₂⟩ g Hg h Hh,
    exact lt_trans (hx₁ g Hg) (hx₂ h Hh) },
  { letI dlo := classical.DLO R,      -- TODO: This isn't implied by `classical`?
    -- TODO: maybe reformulate all this into a useful lemma:
    -- (s : finset R) : s = ∅ ∨ ∃ max ∈ s, ∀ i ∈ s, i ≤ max
    -- Pretty similar to `exists_max_image`.
    cases hlower : lower.max with lmax;
      [{ rw finset.max_eq_none at hlower, subst lower },
       { have le_lmax : ∀ g ∈ lower, g ≤ lmax,
         { intros g H, apply finset.le_max_of_mem H hlower } }],
    all_goals {                 -- TODO: can't we write it using `;`?
    cases hupper : upper.min with umin;
      [{ rw finset.min_eq_none at hupper, subst upper },
       { have umin_le : ∀ h ∈ upper, umin ≤ h,
         { intros h H, apply finset.min_le_of_mem H hupper } }] },
    { simp },
    { suffices : ∃ (x : R), ∀ (h : R), h ∈ upper → x < h, { simpa },
      obtain ⟨x, hx⟩ := no_bot umin,
      exact ⟨x, λ h H, lt_of_lt_of_le hx (umin_le h H)⟩ },
    { suffices : ∃ (x : R), ∀ (g : R), g ∈ lower → g < x, { simpa },
      obtain ⟨x, hx⟩ := no_top lmax,
      exact ⟨x, λ g H, lt_of_le_of_lt (le_lmax g H) hx⟩ },
    { intro Hgh,
      specialize Hgh lmax (finset.mem_of_max hlower) umin (finset.mem_of_min hupper),
      obtain ⟨x, hx₁, hx₂⟩ := dense Hgh,
      exact ⟨x,
        λ g H, lt_of_le_of_lt (le_lmax g H) hx₁,
        λ h H, lt_of_lt_of_le hx₂ (umin_le h H)⟩ } }
end

variables (hF : F.is_isolating)
include hF

-- Now we show that the projection of the set described by a triangular system of constraints
-- is again described by a triangular system of constraints.
-- For this we need the hypothesis that R is a DUNLO.

lemma triangular_projection {n : ℕ} (t : triangular_constraints F (n+1)) :
  ∃ t' : triangular_constraints F n, t'.to_set = t.to_set.image fin.init :=
begin
  rcases t with _ | _ | ⟨_, f | ⟨lower, upper⟩, t⟩,
  { -- Easy case: for an equality constraint,
    -- there is always a (unique) way to extend to the last variable.
    refine ⟨t, _⟩,
    simp only [triangular_constraints.to_set, last_variable_constraints.to_set],
    ext y,
    -- TODO: use mem_image_fin_init?
    split; intro h,
    { refine ⟨fin.snoc y (f y), ⟨_, _⟩, _⟩; simp [h] },
    { obtain ⟨x, hx, rfl⟩ := h,
      exact hx.2 } },
  { -- Harder case: for a between constraint,
    -- the constraint is satisfiable for given values of the earlier variables
    -- when all of the lower functions are less than all of the upper functions.
    let S := (⋂ (g : F n) (Hg : g ∈ lower) (h : F n) (Hh : h ∈ upper), {x | g x < h x}) ∩ t.to_set,
    have : ∃ t' : triangular_constraints F n, t'.to_set = S,
    { refine (triangular_constraints.closed_under_finite_intersections hF).mem_inter _ ⟨t, rfl⟩,
      apply (triangular_constraints.closed_under_finite_intersections hF).mem_fInter, intros g Hg,
      apply (triangular_constraints.closed_under_finite_intersections hF).mem_fInter, intros h Hh,
      apply triangular_constraints_of_constraint hF (constrained.LT g h) },
    obtain ⟨t', ht'⟩ := this,
    refine ⟨t', _⟩,
    rw ht',
    ext y,
    rw mem_image_fin_init,
    simp only [S, triangular_constraints.to_set, last_variable_constraints.to_set,
      fin.snoc_last, mem_inter_eq, mem_Inter, exists_and_distrib_right, mem_set_of_eq, fin.init_snoc],
    rw iff_iff_eq,
    congr,
    classical,
    have := DUNLO_lemma (lower.image (λ (g : F n), g y)) (upper.image (λ (h : F n), h y)),
    simpa only [←finset.mem_coe, finset.coe_image, ball_image_iff, iff_iff_eq] using this.symm }
end

end projection

end DUNLO

end o_minimal
