import data.equiv.fin
import for_mathlib.fin
import tactic.fin_cases

namespace finvec

variables {α : Type*}

localized "notation R `^` n := fin n → R" in finvec

/-- Transfer a vector across an equality of dimensions. -/
def cast {n n' : ℕ} (h : n = n') : α^n → α^n' :=
λ x, x ∘ fin.cast h.symm

lemma cast_id {n : ℕ} {h : n = n} (x : α^n) : cast h x = x :=
by { ext ⟨i, _⟩, refl }

/-- Project `α^(n+m) ≃ α^n × α^m` to the first factor. -/
def left {n m : ℕ} : α^(n+m) → α^n :=
λ x, x ∘ fin.cast_add m

/-- Project `α^(n+m) ≃ α^n × α^m` to the second factor. -/
def right {n m : ℕ} : α^(n+m) → α^m :=
λ x, x ∘ fin.nat_add n

lemma right_zero {m : ℕ} (x : α^(0+m)) : right x = cast (nat.zero_add _) x :=
funext $ λ _, congr_arg x (by rw fin.nat_add_zero)

/-
lemma right_right {k n m : ℕ} (x : α^((k+n)+m)) :
  right (right (cast (nat.add_assoc _ _ _) x)) = right x :=
funext $ λ _, congr_arg x (by rw fin.nat_add_add)
-/

def append_equiv {n m : ℕ} : α^n × α^m ≃ α^(n+m) :=
calc
α^n × α^m ≃ (fin n ⊕ fin m → α) : (equiv.sum_arrow_equiv_prod_arrow (fin n) (fin m) α).symm
...       ≃ α^(n+m)             : equiv.arrow_congr sum_fin_sum_equiv (equiv.refl _)

def append {n m : ℕ} (x : α^n) (y : α^m) : α^(n+m) :=
append_equiv (x, y)

localized "notation x `++` y := finvec.append x y" in finvec

lemma append_equiv_apply {n m : ℕ} {x : α^n} {y : α^m} : append_equiv (x, y) = x ++ y :=
rfl

@[simp] lemma append_left {n m : ℕ} (x : α^n) (y : α^m) : left (x ++ y) = x :=
begin
  suffices : ∀ p : α^n × α^m, append_equiv p ∘ fin.cast_add _ = p.1,
  { exact this (x, y) },
  -- TODO: improved lemma
  rw append_equiv.forall_congr_left',
  intro p,
  rw equiv.apply_symm_apply,
  refl
end

@[simp] lemma append_right {n m : ℕ} (x : α^n) (y : α^m) : right (x ++ y) = y :=
begin
  suffices : ∀ p : α^n × α^m, append_equiv p ∘ fin.nat_add _ = p.2,
  { exact this (x, y) },
  -- TODO: improved lemma
  rw append_equiv.forall_congr_left',
  intro p,
  rw equiv.apply_symm_apply,
  refl
end

@[simp] lemma append_left_right {n m : ℕ} (x : α^(n+m)) : left x ++ right x = x :=
begin
  revert x,
  rw ←append_equiv.forall_congr_left,
  rintros ⟨l, r⟩,
  change append_equiv (l, r) with l ++ r,
  simp
end

lemma append.inj_iff {n m : ℕ} {x x' : α^n} {y y' : α^m} :
  x ++ y = x' ++ y' ↔ x = x' ∧ y = y' :=
by simp only [append, append_equiv.apply_eq_iff_eq, prod.mk.inj_iff]

def external_prod {n m : ℕ} (s : set (α^n)) (t : set (α^m)) : set (α^(n + m)) :=
{x | left x ∈ s ∧ right x ∈ t}

-- precedence matching ∩
localized "infixr ` ⊠ `:70 := finvec.external_prod" in finvec

lemma external_prod_def {n m : ℕ} (s : set (α^n)) (t : set (α^m)) (x : α^(n+m)) :
  x ∈ s ⊠ t ↔ left x ∈ s ∧ right x ∈ t :=
iff.rfl

lemma append_mem_external_prod {n m : ℕ} (s : set (α^n)) (t : set (α^m)) (x : α^n) (y : α^m) :
  x ++ y ∈ s ⊠ t ↔ x ∈ s ∧ y ∈ t :=
by rw [external_prod_def, append_left, append_right]

def fin_two_fun_equiv_prod_self {α : Type*} : (fin 2 → α) ≃ α × α :=
{ to_fun := λ f, (f 0, f 1),
  inv_fun := λ p, finvec.append (λ _, p.1) (λ _, p.2),
  left_inv := λ f, by { ext i, fin_cases i; refl },
  right_inv := λ p, by { cases p, refl } }

end finvec
