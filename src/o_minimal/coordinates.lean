import data.equiv.basic
import data.fin
import for_mathlib.finvec
import for_mathlib.misc

namespace o_minimal

open function set
open_locale finvec

-- R is the type in which coordinates take values,
-- which we can imagine as being the real numbers,
-- though we do not assume anything about R.
variables (R : Type*)

section coordinates

/--
A type X *has coordinates* valued in R
when it is equipped with an embedding into Rⁿ for some specific n.
Mathematically, we can identify X with a subset of Rⁿ,
but in Lean, the type X is not restricted to being of the form
`subtype s` for some `s : set (fin n → R)`.
Informally, we denote this situation by "X ⊆ Rⁿ".
-/
class has_coordinates (X : Type*) :=
(ambdim : ℕ)
(coords : X → finvec ambdim R)
(inj : injective coords)

def coords {X : Type*} [cX : has_coordinates R X] : X → finvec cX.ambdim R :=
cX.coords

/-- Magic causing `simps` to use `coords` on the left hand side of generated `simp` lemmas. -/
def has_coordinates.simps.coords := @coords R

/- TODO: `simps` generates over-applied lemmas like

  coords R x i = (...) i

rather than

  coords R x = ...

because the type of `coords R x` is itself a function type (`fin n → R`).
We work around this with `{ fully_applied := ff }`
but then the lemmas are under-applied instead:

  coords R = λ x, ...
-/

variables {R}

lemma injective_coords (X : Type*) [cX : has_coordinates R X] : injective (@coords R X cX) :=
cX.inj

-- TODO: generalize to `finvec n X` where `[has_coordinates R X]`;
-- but this will lose the definition as `id`.
/-- Rⁿ tautologically has coordinates given by the identity. -/
@[simps { fully_applied := ff }] instance has_coordinates.finvec (n : ℕ) : has_coordinates R (finvec n R) :=
{ ambdim := n,
  coords := λ x, x,
  inj := injective_id }

/-- R has coordinates given by the usual identification R ≃ R¹. -/
@[simps { fully_applied := ff }] instance has_coordinates.self : has_coordinates R R :=
{ ambdim := 1,
  coords := const (fin 1),
  inj := λ a b h, congr_fun h 0 }

/-- If X ⊆ Rⁿ and Y ⊆ Rᵐ then X × Y ⊆ Rⁿ⁺ᵐ. -/
@[simps { fully_applied := ff, simp_rhs := tt }] instance has_coordinates.prod
  {X Y : Type*} [cX : has_coordinates R X] [cY : has_coordinates R Y] :
  has_coordinates R (X × Y) :=
{ ambdim := cX.ambdim + cY.ambdim,
  coords := λ p, coords R p.1 ++ coords R p.2,
  inj := injective.comp (equiv.injective _) (injective.prod_map cX.inj cY.inj) }

/-- If X ⊆ Rⁿ and S is a subset of X then S ⊆ Rⁿ. -/
@[simps { fully_applied := ff }] instance has_coordinates.subtype {X : Type*} [cX : has_coordinates R X] (s : set X) :
  has_coordinates R s :=
{ ambdim := cX.ambdim,
  coords := λ a, coords R (subtype.val a),
  inj := injective.comp cX.inj subtype.val_injective }

/-- Any subsingleton may be regarded as having coordinates valued in R⁰. -/
@[simps { fully_applied := ff }] def has_coordinates.subsingleton {X : Type*} [subsingleton X] : has_coordinates R X :=
{ ambdim := 0,
  coords := λ x, fin_zero_elim,
  inj := subsingleton_injective _ }

@[simps { fully_applied := ff, rhs_md := semireducible }]
instance pempty.has_coordinates : has_coordinates R pempty := has_coordinates.subsingleton

@[simps { fully_applied := ff, rhs_md := semireducible }]
instance punit.has_coordinates : has_coordinates R punit := has_coordinates.subsingleton

variables (R)

/-- The subset of Rⁿ which is mapped onto by X. -/
def coordinate_image (X : Type*) [cX : has_coordinates R X] := range (@coords R X _)

variables {R}

lemma coordinate_image_prod {X Y : Type*} [cX : has_coordinates R X] [cY : has_coordinates R Y] :
  coordinate_image R (X × Y) = coordinate_image R X ⊠ coordinate_image R Y :=
begin
  apply set.ext,
  refine finvec.rec (λ v w, _),
  rw finvec.mem_prod_iff,
  simp [coordinate_image, finvec.append.inj_iff]
end

end coordinates

section reindexing

/--
If X and Y have coordinates valued in R,
then a function f : X → Y is a *reindexing*
if it fits into a diagram

  X ⊆ Rⁿ
f ↓   ↓ r^*
  Y ⊆ Rᵐ

where the map r^* is given by reindexing the coordinates
according to some map r : fin m → fin n, so that
r^*(x₁, ..., xₙ) = (xᵣ₍₁₎, ..., xᵣ₍ₘ₎).

For example, projections and subset inclusions are reindexings,
as are maps built from these by forming products.
A given map f may be a reindexing in more than one way (i.e., for several r),
for example if both X and Y are empty.
Here we don't care about the choice of r so we make `is_reindexing` a Prop.

A basic fact about definability is that
the preimage of a definable set under a map of the form r^* is definable.
This notion `is_reindexing` will let us reformulate this result
in the language of `has_coordinates`.
-/
inductive is_reindexing
  {X Y : Type*} [cX : has_coordinates R X] [cY : has_coordinates R Y]
  (f : X → Y) : Prop
| mk (σ : fin cY.ambdim → fin cX.ambdim)
     (h : ∀ x i, coords R x (σ i) = coords R (f x) i)
  : is_reindexing

variables {R}

lemma is_reindexing.id (X : Type*) [cX : has_coordinates R X] :
  is_reindexing R (id : X → X) :=
⟨id, λ x i, rfl⟩

lemma is_reindexing.comp
  {X Y Z : Type*} [cX : has_coordinates R X] [cY : has_coordinates R Y] [cZ : has_coordinates R Z]
  {g : Y → Z} (hg : is_reindexing R g) {f : X → Y} (hf : is_reindexing R f) :
  is_reindexing R (g ∘ f) :=
begin
  cases hf with fσ hf,
  cases hg with gσ hg,
  refine ⟨fσ ∘ gσ, λ x i, _⟩,
  simp [hf, hg]
end

lemma is_reindexing.fst
  {X Y : Type*} [cX : has_coordinates R X] [cY : has_coordinates R Y] :
  is_reindexing R (prod.fst : X × Y → X) :=
begin
  refine ⟨fin.cast_add _, λ p i, _⟩,
  change finvec.left (_ ++ _) i = _,
  simp
end

lemma is_reindexing.snd
  {X Y : Type*} [cX : has_coordinates R X] [cY : has_coordinates R Y] :
  is_reindexing R (prod.snd : X × Y → Y) :=
begin
  refine ⟨fin.nat_add _, λ p i, _⟩,
  change finvec.right (_ ++ _) i = _,
  simp
end

lemma is_reindexing.prod
  {X Y Z : Type*} [cX : has_coordinates R X] [cY : has_coordinates R Y] [cZ : has_coordinates R Z]
  {f : X → Y} (hf : is_reindexing R f) {g : X → Z} (hg : is_reindexing R g) :
  is_reindexing R (λ x, (f x, g x)) :=
begin
  cases hf with fσ hf,
  cases hg with gσ hg,
  let σ : fin cY.ambdim ⊕ fin cZ.ambdim → fin cX.ambdim := λ i, sum.cases_on i fσ gσ,
  refine ⟨σ ∘ sum_fin_sum_equiv.symm, λ x, _⟩,
  dsimp only [(∘)],
  -- TODO: lemma for `e : α ≃ β` that `(∀ a, p a (e a)) ↔ (∀ b, p (e.symm b) b)`?
  refine sum_fin_sum_equiv.forall_congr_left.mp _,
  rintro (i|i); rw equiv.symm_apply_apply,
  { refine (hf _ i).trans _,
    refine congr_fun _ i,
    exact finvec.left_append.symm },
  { refine (hg _ i).trans _,
    refine congr_fun _ i,
    exact finvec.right_append.symm }
end

lemma is_reindexing.coords {X : Type*} [cX : has_coordinates R X] :
  is_reindexing R (λ (x : X), coords R x) :=
⟨id, λ x j, rfl⟩

lemma is_reindexing.coord {X : Type*} [cX : has_coordinates R X] (i : fin cX.ambdim) :
  is_reindexing R (λ x, coords R x i) :=
⟨λ _, i, λ x j, rfl⟩

lemma is_reindexing.subtype.val {X : Type*} [cX : has_coordinates R X] {s : set X} :
  is_reindexing R (subtype.val : s → X) :=
⟨id, λ x j, rfl⟩

lemma is_reindexing.finvec.left {n m : ℕ} :
  is_reindexing R (finvec.left : (finvec (n+m) R) → (finvec n R)) :=
⟨fin.cast_add m, λ x j, rfl⟩

lemma is_reindexing.finvec.right {n m : ℕ} :
  is_reindexing R (finvec.right : (finvec (n+m) R) → (finvec m R)) :=
⟨fin.nat_add n, λ x j, rfl⟩

lemma is_reindexing.finvec.init {n : ℕ} :
  is_reindexing R (finvec.init : (finvec (n+1) R) → (finvec n R)) :=
⟨fin.cast_succ, λ x j, rfl⟩

lemma is_reindexing.finvec.snoc {n : ℕ} :
  is_reindexing R (λ (p : finvec n R × R), p.1.snoc p.2) :=
⟨id, by { intros x j, rw finvec.snoc_eq_append, refl }⟩

end reindexing

end o_minimal
