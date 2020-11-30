import data.equiv.fin
import for_mathlib.fin
import tactic.abel
import tactic.fin_cases

/-
Finite vectors, implemented as functions on `fin n`.
The main advantage of `finvec` over alternatives like `vector` is that
extracting coordinates (components) of a `finvec` is just function application,
so it's easy to reason about things like permuting coordinates.
-/

/-- A (homogeneous) "vector" of `n` `α`s, implemented as a function from `fin n`.
The `j`th component of such a vector `x` (where `j : fin n`) is simply `x j`. -/
def finvec (n : ℕ) (α : Type*) : Type* := fin n → α

namespace finvec

variables {α : Type*}

/-- Transport a vector across an equality of dimensions.
This is implemented without using `eq.rec` so that it will reduce
when evaluated at a constructor `⟨j, h : j < n'⟩` of `fin n'`. -/
protected def cast {n n' : ℕ} (h : n = n') : finvec n α → finvec n' α :=
λ x, x ∘ fin.cast h.symm

@[simp] lemma cast_app {n n' : ℕ} {h : n = n'} {x : finvec n α} {j : fin n'} :
  (x.cast h) j = x (j.cast h.symm) :=
rfl

@[simp] lemma cast_id {n : ℕ} {h : n = n} {x : finvec n α} : x.cast h = x :=
by { ext ⟨i, _⟩, refl }

section set

/-- Transport a set of vectors across an equality of dimensions. -/
protected def set.cast {n n' : ℕ} (h : n = n') : set (finvec n α) → set (finvec n' α) :=
λ s, s ∘ finvec.cast h.symm

lemma set.cast_id {n : ℕ} : finvec.set.cast rfl = (id : set (finvec n α) → set (finvec n α)) :=
begin
  ext s x,
  change x.cast rfl ∈ s ↔ x ∈ s,
  rw cast_id
end

lemma set.heq_iff_cast_eq {n n' : ℕ} (h : n = n') {s : set (finvec n α)} {s' : set (finvec n' α)} :
  s == s' ↔ s = finvec.set.cast h.symm s' :=
begin
  cases h,
  rw [heq_iff_eq, set.cast_id],
  refl
end

end set

instance : unique (finvec 0 α) :=
⟨⟨fin_zero_elim⟩, by { intro x, ext i, fin_cases i }⟩

section prod

/-! ### Products

The isomorphism αⁿ⁺ᵐ ≅ αⁿ × αᵐ is ubiquitous in mathematics, and usually
invoked implicitly. Lean maintains a distinction between the two sides of course.
Here, we provide an API which presents `finvec (n+m) α` as though it were
a structure with two fields `left : finvec n α` and `right : finvec m α`,
with constructor `append : finvec n α → finvec m α → finvec (n+m) α`.

The arguments `n m : ℕ` are implicit throughout this API, to be inferred
from the argument or result types; this may seem problematic, since a number
can be written in the form `n+m` in many ways, but actually works well
in practice. -/

variables {n m : ℕ}

/-- Project `αⁿ⁺ᵐ ≅ αⁿ × αᵐ` to the first factor. -/
protected def left : finvec (n + m) α → finvec n α :=
λ x, x ∘ fin.cast_add m

/-- Project `αⁿ⁺ᵐ ≅ αⁿ × αᵐ` to the second factor. -/
protected def right : finvec (n + m) α → finvec m α :=
λ x, x ∘ fin.nat_add n

/-- The canonical equivalence `αⁿ⁺ᵐ ≅ αⁿ × αᵐ`. -/
def append_equiv : finvec (n + m) α ≃ finvec n α × finvec m α :=
calc  (fin (n + m) → α)
    ≃ (fin n ⊕ fin m → α)        : equiv.arrow_congr sum_fin_sum_equiv.symm (equiv.refl _)
... ≃ (fin n → α) × (fin m → α)  : (equiv.sum_arrow_equiv_prod_arrow (fin n) (fin m) α)

/-- The concatenation of two vectors. -/
def append (x : finvec n α) (y : finvec m α) : finvec (n + m) α :=
append_equiv.symm (x, y)

lemma append_equiv_app {z : finvec (n + m) α} : append_equiv z = (z.left, z.right) := rfl

localized "infixr ` ++ ` := finvec.append" in finvec

lemma append_equiv_symm_app {x : finvec n α} {y : finvec m α} :
  append_equiv.symm (x, y) = x ++ y :=
rfl

@[simp] lemma left_append_right (x : finvec (n + m) α) : x.left ++ x.right = x :=
append_equiv.symm_apply_apply x

/-- Induction principle for `finvec (n + m) α`,
imagined as a structure containing its left and right parts. -/
@[elab_as_eliminator]
protected lemma rec {C : finvec (n + m) α → Prop}
  (h : Π (x : finvec n α) (y : finvec m α), C (x ++ y)) (z : finvec (n + m) α) : C z :=
begin
  rw ←left_append_right z,
  apply h
end

@[simp] lemma left_append {x : finvec n α} {y : finvec m α} : (x ++ y).left = x :=
congr_arg prod.fst (append_equiv.apply_symm_apply (x, y) : _)

@[simp] lemma right_append {x : finvec n α} {y : finvec m α} : (x ++ y).right = y :=
congr_arg prod.snd (append_equiv.apply_symm_apply (x, y) : _)

lemma prod_ext {z z' : finvec (n + m) α} :
  z = z' ↔ z.left = z'.left ∧ z.right = z'.right :=
append_equiv.apply_eq_iff_eq.symm.trans prod.mk.inj_iff

lemma append.inj_iff {x x' : finvec n α} {y y' : finvec m α} :
  x ++ y = x' ++ y' ↔ x = x' ∧ y = y' :=
by simp only [append, equiv.apply_eq_iff_eq, prod.mk.inj_iff]

lemma left_zero {x : finvec (n + 0) α} : x.left = x :=
by { ext ⟨_, _⟩, refl }

lemma right_zero {x : finvec (0 + n) α} : x.right = x.cast (zero_add n) :=
funext $ λ _, congr_arg x (by rw fin.nat_add_zero)

@[simp] lemma append_zero {x : finvec n α} {y : finvec 0 α} : x ++ y = x :=
begin
  rw [prod_ext, left_append, left_zero, right_append],
  simp
end

/-- The product (in the sense of `set.prod`) of sets of vectors,
under the isomorphism `αⁿ × αᵐ ≅ αⁿ⁺ᵐ`. -/
def prod (s : set (finvec n α)) (t : set (finvec m α)) :
  set (finvec (n + m) α) :=
{z | z.left ∈ s ∧ z.right ∈ t}

localized "infixr ` ⊠ `:70 := finvec.prod" in finvec

lemma mem_prod_iff {s : set (finvec n α)} {t : set (finvec m α)}
  (z : finvec (n + m) α) : z ∈ s ⊠ t ↔ z.left ∈ s ∧ z.right ∈ t :=
iff.rfl

lemma append_mem_prod_iff {s : set (finvec n α)} {t : set (finvec m α)}
  {x : finvec n α} {y : finvec m α} : x ++ y ∈ s ⊠ t ↔ x ∈ s ∧ y ∈ t :=
begin
  convert mem_prod_iff (x ++ y),
  { rw left_append }, { rw right_append }
end

def prod_univ (s : set (finvec n α)) (m : ℕ) : set (finvec (n + m) α) :=
{z | z.left ∈ s}

section
variables (n)
def univ_prod (n : ℕ) (t : set (finvec m α)) : set (finvec (n + m) α) :=
{z | z.right ∈ t}
end

lemma prod_univ_eq {s : set (finvec n α)} :
  prod_univ s m = s ⊠ (set.univ : set (finvec m α)) :=
by { ext, exact (and_true _).symm }

lemma univ_prod_eq {t : set (finvec m α)} :
  univ_prod n t = (set.univ : set (finvec n α)) ⊠ t :=
by { ext, exact (true_and _).symm }

lemma prod_eq_prod_univ_inter_univ_prod {s : set (finvec n α)} {t : set (finvec m α)} :
  s ⊠ t = prod_univ s m ∩ univ_prod n t :=
rfl

@[simp] lemma append_mem_prod_univ_iff {s : set (finvec n α)}
  {x : finvec n α} {y : finvec m α} : x ++ y ∈ prod_univ s m ↔ x ∈ s :=
begin
  change (x ++ y).left ∈ s ↔ x ∈ s,
  rw left_append
end

@[simp] lemma append_mem_univ_prod_iff {t : set (finvec m α)}
  {x : finvec n α} {y : finvec m α} : x ++ y ∈ univ_prod n t ↔ y ∈ t :=
begin
  change (x ++ y).right ∈ t ↔ y ∈ t,
  rw right_append
end

-- Lemmas for inductively adding coordinates on the right.
-- These lemma statements (and proof) take advantage of
-- the definitional equalities `n + 0 = n`, `n + (m + 1) = (n + m) + 1`.

lemma prod_univ_zero_eq {s : set (finvec n α)} :
  prod_univ s 0 = s :=
begin
  ext x,
  change x.left ∈ s ↔ x ∈ s,
  rw left_zero
end

lemma prod_univ_plus_one_eq {s : set (finvec n α)} :
  prod_univ s (m + 1) = (prod_univ (prod_univ s m) 1 : _) :=
begin
  ext x,
  change _ ∈ s ↔ _ ∈ s,
  refl
end

-- Lemmas for inductively adding coordinates on the left.
-- For these lemmas we do not have corresponding definitional equalities
-- so TODO

lemma univ_prod_zero_like {ι : Sort*} (C : Π {l : ℕ}, set (finvec l α) → ι)
  {t : set (finvec m α)} : C (univ_prod 0 t) = C t :=
begin
  have : 0 + m = m := zero_add m,
  congr',
  rw set.heq_iff_cast_eq this,
  ext x,
  change x.right ∈ t ↔ x.cast _ ∈ t,
  rw right_zero
end

lemma univ_prod_plus_one_like {ι : Sort*} (C : Π {l : ℕ}, set (finvec l α) → ι)
  {t : set (finvec m α)} :
  C (univ_prod (n + 1) t) = C (univ_prod 1 (univ_prod n t)) :=
begin
  have : (n + 1) + m = 1 + (n + m) := by abel,
  congr' 1, { exact this },
  rw set.heq_iff_cast_eq this,
  ext x,
  change x.right ∈ t ↔ (x.cast _).right.right ∈ t,
  congr' 2,
  ext ⟨i, h⟩,
  change x _ = x _,
  congr,
  ext,
  change (n + 1) + i = 1 + (n + i),
  abel
end

end prod

/-
-- TODO: is it useful to introduce this definition?
-- use in `tame_of_def`, `tame_of_constrained` etc.
def finvec_one_equiv_self {α : Type*} : finvec 1 α ≃ α :=
equiv.fun_unique (fin 1) α
-/

section snoc

-- TODO: for append notation; this is a bit ugly
open_locale finvec

/-! ### Appending a single element (snoc)

This section is parallel to the section on products
but based on the isomorphism αⁿ⁺¹ ≅ αⁿ × α.
We name the projections `init : finvec (n+1) α → finvec n α`
(which equals `left` specialized to `m = 1`) and `last : finvec (n+1) α → α`,
with constructor `snoc : finvec n α → α → finvec (n+1) α`. -/

variables {n : ℕ}

protected def init : finvec (n + 1) α → finvec n α :=
λ x, x ∘ fin.cast_succ

lemma left_eq_init {x : finvec (n + 1) α} : x.left = x.init := rfl

-- TODO: simp lemmas? see uses of `simp [finvec.last]`
protected def last : finvec (n + 1) α → α :=
λ x, x (fin.last n)

lemma right_eq_last {x : finvec (n + 1) α} : x.right = function.const (fin 1) x.last :=
begin
  ext i,
  fin_cases i,
  refl
end

/-- The canonical equivalence `αⁿ⁺¹ ≅ αⁿ × α`. -/
def snoc_equiv : finvec (n + 1) α ≃ finvec n α × α :=
calc  (fin (n + 1) → α)
    ≃ (fin n → α) × (fin 1 → α)  : append_equiv
... ≃ (fin n → α) × α            : equiv.prod_congr (equiv.refl _) (equiv.fun_unique (fin 1) α)

def snoc (x : finvec n α) (a : α) : finvec (n + 1) α :=
snoc_equiv.symm (x, a)

lemma snoc_equiv_app {z : finvec (n + 1) α} : snoc_equiv z = (z.init, z.last) := rfl

lemma snoc_equiv_symm_app {x : finvec n α} {a : α} :
  snoc_equiv.symm (x, a) = x.snoc a :=
rfl

lemma init_snoc_last (x : finvec (n + 1) α) : x.init.snoc x.last = x :=
snoc_equiv.symm_apply_apply x

/-- Induction principle for `finvec (n + 1) α`,
imagined as a structure containing its initial part and last element. -/
@[elab_as_eliminator]
protected lemma snoc_rec {C : finvec (n + 1) α → Prop}
  (h : Π (x : finvec n α) (a : α), C (snoc x a)) (z : finvec (n + 1) α) : C z :=
begin
  rw ←init_snoc_last z,
  apply h
end

@[simp] lemma init_snoc {x : finvec n α} {a : α} : (x.snoc a).init = x :=
congr_arg prod.fst (snoc_equiv.apply_symm_apply (x, a) : _)

@[simp] lemma last_snoc {x : finvec n α} {a : α} : (x.snoc a).last = a :=
congr_arg prod.snd (snoc_equiv.apply_symm_apply (x, a) : _)

lemma snoc.inj_iff {x x' : finvec n α} {a a' : α} :
  x.snoc a = x'.snoc a' ↔ x = x' ∧ a = a' :=
by simp only [snoc, equiv.apply_eq_iff_eq, prod.mk.inj_iff]

-- TODO: rather than `function.const (fin 1)`
-- should we use a specialized `finvec_one_equiv_self`?
lemma snoc_eq_append {x : finvec n α} {a : α} :
  x.snoc a = x ++ function.const (fin 1) a :=
begin
  -- TODO: think about whether this proof is still logical
  refine (left_append_right (x.snoc a : fin (n+1) → α)).symm.trans _,
  rw append.inj_iff,
  split,
  { rw [left_eq_init, init_snoc] },
  { rw [right_eq_last, last_snoc] }
end

-- TODO: add versions for `left`, `right`?
lemma mem_image_init {s : set (finvec (n + 1) α)} {y : finvec n α} :
  y ∈ finvec.init '' s ↔ ∃ z : α, finvec.snoc y z ∈ s :=
begin
  split; intro h,
  { obtain ⟨x, hx, rfl⟩ := h,
    refine ⟨x.last, _⟩,
    rw finvec.init_snoc_last,
    exact hx },
  { obtain ⟨z, hz⟩ := h,
    refine ⟨finvec.snoc y z, hz, _⟩,
    simp }
end

-- TODO: comparison to prod, fin.snoc.

end snoc

section tail
-- Same as `finvec.right` but with the "wrong" type:
-- `finvec (n + 1) α → finvec n α` rather than `finvec (1 + n) α → finvec n α`.

variables {n : ℕ}

def tail (x : finvec (n + 1) α) : finvec n α :=
x ∘ fin.succ

lemma univ_prod_one_like_preimage_tail {ι : Sort*} (C : Π {l : ℕ}, set (finvec l α) → ι)
  {t : set (finvec n α)} :
  C (univ_prod 1 t) = C (tail ⁻¹' t) :=
begin
  have : 1 + n = n + 1 := add_comm 1 n,
  congr',
  rw set.heq_iff_cast_eq this,
  ext x,
  change x.right ∈ t ↔ (x.cast _).tail ∈ t,
  congr',
  ext i,
  change x _ = x _,
  congr,
  ext,
  rw [fin.coe_cast, fin.coe_succ],
  apply add_comm
end

end tail

/-- The canonical isomorphism `α² ≅ α × α`. -/
-- TODO: This most likely needs some lemmas. See its use in `o_minimal.mk'`.
def finvec_two_equiv_prod_self {α : Type*} : finvec 2 α ≃ α × α :=
{ to_fun := λ f, (f 0, f 1),
  inv_fun := λ p, finvec.append (λ _, p.1) (λ _, p.2),
  left_inv := λ f, by { ext i, fin_cases i; refl },
  right_inv := λ p, by { cases p, refl } }

-- TODO: instances? e.g. topological_space, add_comm_group, etc.?

end finvec
