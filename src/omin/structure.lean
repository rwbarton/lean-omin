import data.equiv.fin

-- definability mockup

open set

local notation R `^` n := fin n → R

section
-- preliminaries on product spaces

variables {R : Type*} {n m : ℕ}

def equiv.pow_mul_pow_equiv_pow_add : R^n × R^m ≃ R^(n+m) :=
calc
R^n × R^m ≃ (fin n ⊕ fin m → R) : (equiv.sum_arrow_equiv_prod_arrow (fin n) (fin m) R).symm
...       ≃ R^(n+m)             : equiv.arrow_congr sum_fin_sum_equiv (equiv.refl _)

def equiv.pow_one_equiv_self : R ≃ R^1 :=
calc
  R ≃ (unit → R) : equiv.symm (equiv.punit_arrow_equiv R)
... ≃ R^1        : equiv.arrow_congr fin_one_equiv.symm (equiv.refl _)

variables (X : set (R^n)) (Y : set (R^m))

def external_prod_aux : Σ (Z : set (R^(n+m))), X × Y ≃ Z :=
⟨_, (equiv.set.prod _ _).symm.trans equiv.pow_mul_pow_equiv_pow_add.subtype_equiv_of_subtype'⟩

def external_prod : set (R^(n+m)) := (external_prod_aux X Y).1

def external_prod_equiv : X × Y ≃ external_prod X Y := (external_prod_aux X Y).2

end

structure struc (R : Type*) :=
(definable : Π {n : ℕ} (A : set (R^n)), Prop)
-- satisfying a pile of axioms from vdD

-- QUESTION: What is the right interface to provide
-- from the perspective of defining examples?

variables {R : Type*}

-- These aren't (necessarily) the missing axioms of `struc`,
-- but would be lemmas proven shortly after the definition.
axiom struc.definable_univ (S : struc R) {n : ℕ} : S.definable (univ : set (R^n))
axiom struc.definable_external_prod (S : struc R) {n m : ℕ}
  {X : set (R^n)} (hX : S.definable X) {Y : set (R^m)} (hY : S.definable Y) :
  S.definable (external_prod X Y)

-- fake example
constant semialg [decidable_linear_ordered_comm_ring R] : struc R

/-- Key notion:
A *definable* set (type) is one equipped with
an isomorphism to a definable subset of some `R^n`.
Then we (mostly?) hide the implementation detail of `R^n` outside this module.
(But we won't be able to hide it completely,
because we still need to be able to talk about continuous maps,
closed and bounded sets, etc.)
-/
class definable (S : struc R) (X : Type*) :=
{n : ℕ}
(Z : set (R^n))
(h : S.definable Z)
(e : X ≃ Z)

-- Remark:
-- Another way to describe this structure is as
-- a finite family of functions from X to R
-- which are jointly injective with definable image.

instance definable.r (S : struc R) : definable S R :=
{ n := 1, Z := set.univ, h := S.definable_univ,
  e := equiv.pow_one_equiv_self.trans (equiv.set.univ _).symm }

instance definable.rn (S : struc R) {n : ℕ} : definable S (R^n) :=
{ n := n, Z := set.univ, h := S.definable_univ, e := (equiv.set.univ _).symm }

/-- Not an instance because it depends on `S.definable Z`
which is not a class. -/
-- Also, it's probably pretty useless. Instead, see below
/-
def definable.subset (S : struc R) {n : ℕ} (Z : set (R^n)) (h : S.definable Z) :
  definable S Z :=
{ n := n, Z := Z, h := h, e := equiv.refl _ }
-/

instance definable.prod (S : struc R)
  (X : Type*) (Y : Type*) [dX : definable S X] [dY : definable S Y] :
  definable S (X × Y) :=
{ n := dX.n + dY.n,
  Z := external_prod dX.Z dY.Z,
  h := S.definable_external_prod dX.h dY.h,
  e := (dX.e.prod_congr dY.e).trans (external_prod_equiv _ _) }

-- Also add Pi of finitely many factors.

-- instance definable.sum ... : definable S (X ⊕ Y)
-- NB: this requires two distinct distinguished elements of R

/-- A subset of a definable set is definable
if its image under the coordinatization is definable. -/
def struc.definable_set (S : struc R)
  {X : Type*} [dX : definable S X]
  (s : set X) : Prop :=
S.definable (subtype.val ∘ dX.e '' s)

/-- Not an instance because it depends on `S.definable_set s`
which is not a class. -/
def definable.subset (S : struc R) {X : Type*} [dX : definable S X]
  {s : set X} (hs : S.definable_set s) : definable S s :=
{ n := dX.n, Z := subtype.val ∘ dX.e '' s, h := hs, e := sorry }

-- & prove it has the expected universal property,
-- once we have definable functions

lemma struc.definable_set.compl (S : struc R)
  {X : Type*} [dX : definable S X]
  {s : set X} (h : S.definable_set s) : S.definable_set sᶜ :=
sorry

lemma struc.definable_set.inter (S : struc R)
  {X : Type*} [dX : definable S X]
  {s t : set X} (hs : S.definable_set s) (ht : S.definable_set t) :
  S.definable_set (s ∩ t) :=
sorry

lemma struc.definable_set.imp (S : struc R)
  {X : Type*} [dX : definable S X]
  {s t : set X} (hs : S.definable_set s) (ht : S.definable_set t) :
  S.definable_set {x | s x → t x} :=
sorry

-- TODO: Is this the best way to express this?
-- Would need to dsimp away function.uncurry afterwards
-- (or we could just do it in the statement)
lemma struc.definable_set.forall (S : struc R)
  {X Y : Type*} [dX : definable S X] [dY : definable S Y]
  {s : X → Y → Prop} (hs : S.definable_set (function.uncurry s)) :
  S.definable_set {x | ∀ y, s x y} :=
sorry

lemma struc.definable_set.eq (S : struc R)
  {X : Type*} [dX : definable S X] :
  S.definable_set {p : X × X | p.1 = p.2} :=
sorry

-- This isn't really important (like `decidable_of_iff` is)
-- because definability is a Prop and not data;
-- however it still seems like a useful idiom.
lemma struc.definable_set_of_iff (S : struc R)
  {X : Type*} [dX : definable S X]
  {s : set X} (t : set X) (h : ∀ x, s x ↔ t x) :
  S.definable_set t → S.definable_set s :=
have s = t := set.ext h,
by { intro, rwa this }

/-- A function between two definable sets is definable
if its graph is a definable subset. -/
def struc.definable_fun (S : struc R)
  {X Y : Type*} [dX : definable S X] [dY : definable S Y]
  (f : X → Y) : Prop :=
S.definable_set {p : X × Y | f p.1 = p.2 }

-- definable functions form a category

lemma struc.definable.id (S : struc R)
  {X : Type*} [dX : definable S X] :
  S.definable_fun (id : X → X) :=
sorry

lemma struc.definable.comp (S : struc R)
  {X Y Z : Type*} [dX : definable S X] [dY : definable S Y] [dZ : definable S Z]
  {g : Y → Z} (hg : S.definable_fun g) {f : X → Y} (hf : S.definable_fun f) :
  S.definable_fun (λ x, g (f x)) :=
sorry

lemma struc.definable.preimage (S : struc R)
  {X : Type*} [dX : definable S X]
  {Y : Type*} [dY : definable S Y]
  {f : X → Y} (hf : S.definable_fun f)
  {s : set Y} (hs : S.definable_set s) :
  S.definable_set (f ⁻¹' s) :=
sorry

lemma struc.definable.val (S : struc R) {X : Type*} [dX : definable S X]
  {s : set X} (hs : S.definable_set s) :
  by letI := definable.subset S hs; exact
  S.definable_fun (subtype.val : s → X) :=
sorry

section prod

variables (S : struc R) {X : Type*} {Y : Type*} [definable S X] [definable S Y]

lemma struc.definable.fst : S.definable_fun (prod.fst : X × Y → X) :=
sorry

lemma struc.definable.snd : S.definable_fun (prod.snd : X × Y → Y) :=
sorry

variables {S}

lemma struc.definable_fun.prod {A : Type*} [dA : definable S A]
  {f : A → X} (hf : S.definable_fun f)
  {g : A → Y} (hg : S.definable_fun g) :
  S.definable_fun (λ a, (f a, g a)) :=
sorry

end prod

-- Similarly, prove the universal properties of (finite) Pi, ⊕, (finite) Sigma
-- with respect to definable functions.

-- TODO: What happens for relations of higher arity?
-- Would this already magically work?
lemma struc.definable.binrel (S : struc R)
  {X : Type*} [dX : definable S X]
  {Y : Type*} [dY : definable S Y]
  {Z : Type*} [dZ : definable S Z]
  {f : X → Y} (hf : S.definable_fun f)
  {g : X → Z} (hg : S.definable_fun g)
  {s : Y → Z → Prop} (hs : S.definable_set {p : Y × Z | s p.1 p.2}) :
  S.definable_set {x | s (f x) (g x)} :=
struc.definable.preimage S (hf.prod hg) hs

lemma struc.definable_set.eq' (S : struc R)
  {X : Type*} [dX : definable S X]
  {Y : Type*} [dY : definable S Y]
  {f : X → Y} (hf : S.definable_fun f)
  {g : X → Y} (hg : S.definable_fun g) :
  S.definable_set {p : X | f p = g p} :=
-- This works, but we need to supply all the arguments manually
-- struc.definable.preimage S (hf.prod hg) (struc.definable_set.eq S)
-- Potential problem: struc.definable.binrel can loop
-- (and would if apply_rules didn't succeed
-- in applying struc.definable_set.eq first)
by apply_rules [struc.definable_set.eq, struc.definable.binrel]

class definable_constants (S : struc R) : Prop :=
(definable_singleton (r : R) : S.definable_set ({r} : set R))

lemma struc.definable.const (S : struc R) {X : Type*} [definable S X] (r : R) :
  S.definable_fun (λ (x : X), r) :=
sorry
