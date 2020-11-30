import category_theory.concrete_category
import category_theory.comma
import category_theory.punit

/-
Attempt at avoiding the infinite sequence
`definable_psh`, `definable_fam`, ?, ...
by abstracting over the index category,
and passing to the slice category over X
(or really, the category of elements of X)
to handle a family of types indexed by X.
-/

open category_theory

universes u

local attribute [instance] concrete_category.has_coe_to_sort concrete_category.has_coe_to_fun

variables (C : Type u) [small_category C] [concrete_category.{u} C]

class psh (X : Type u) :=
(mem : Π {K : C}, (K → X) → Prop)
(mem_comp : Π (L K : C) (φ : L ⟶ K) (f : K → X), mem f → mem (f ∘ φ))

-- This isn't the right definition:
-- we only want the objects which satisfy `mem`.
-- We just add the required instance constraint for now.
abbreviation slice (X : Type u) [psh C X] : Type u :=
-- TODO: full_subcategory etc. & fix `concrete_category` instance
comma.{u 0 u} (forget C) (functor.from_punit X)

instance (X : Type u) [psh C X] : concrete_category.{u} (slice C X) :=
{ forget := (comma.fst _ _).comp (forget C),
  forget_faithful := sorry }

-- This improved things a bit. We can now encode the map (Σ Y) → X
-- as an object of the presheaf category on C/X.
-- But where would we actually get the instance?
instance pi.psh {X : Type u} [psh C X] {Y : X → Type u} [psh (slice C X) (Σ x, Y x)] :
  psh C (Π (x : X), Y x) :=
sorry

/-
instance sigma.psh {X : Type u} [psh C X] {Y : X → Type u} [psh (slice C X) (Σ x, Y x)] :
  psh C (sigma Y) :=
sorry
-/

instance pi₂.psh {X : Type u} [psh C X] {Y : X → Type u} [psh (slice C X) (Σ x, Y x)]
  {Z : Π x, Y x → Type u} [psh (slice C (sigma Y)) (Σ (p : sigma Y), Z p.1 p.2)] :
  psh (slice C X) (Σ x, Π y, Z x y) :=
sorry

-- Vague idea: instances for `psh (slice C X)` are expected to be of the form
-- `Σ x, ...`? Will this let us handle multiple `Σ x y, ...` cleanly?

variables
  {X : Type u} [psh C X]
  {Y : X → Type u} [psh (slice C X) (sigma Y)]
  {Z : Π x, Y x → Type u} [psh (slice (slice C X) (sigma Y)) (Σ x y, Z x y)]
--{W : Π x y, Z x y → Type u} [psh (slice (slice (slice C X) (sigma Y)) _) (Σ x y z, W x y z)]

--set_option trace.class_instances true
--#check (show psh C (Π (x : X) (y : Y x), Z x y), by apply_instance)

-- Is there a better plan than creating a separate type class to represent
-- definability of type families with n free variables, for each metatheoretic
-- natural number n?
-- Annoying because every instance will also have to be duplicated in
-- each context length...

-- What we want is something like a "type class class":
--   Type* ↦ definable_psh
--   (X → Type*) ↦ definable_fam
-- in general, if α ↦ C, then (Y → α) ↦ C' derived somehow from C ...

/-
class definable_thing (β : Type*) [has_definable_thingy β] (X : β) := ...?
-/

-- Also, we've now fixed the universe of X to Type u, which is somewhat okay
-- but going to be annoying mainly for Prop, and to some extent things like ℕ
-- Can we fix this without too much trouble?
-- If X inhabits an arbitrary universe, then at least one universe argument of
-- `slice C X` and its `concrete_category` instance will change... then what?
