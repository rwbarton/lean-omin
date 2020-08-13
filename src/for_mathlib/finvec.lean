import data.equiv.fin
import for_mathlib.fin

namespace finvec

variables {α : Type*}

localized "notation R `^` n := fin n → R" in finvec

def append_equiv {n m : ℕ} : α^n × α^m ≃ α^(n+m) :=
calc
α^n × α^m ≃ (fin n ⊕ fin m → α) : (equiv.sum_arrow_equiv_prod_arrow (fin n) (fin m) α).symm
...       ≃ α^(n+m)             : equiv.arrow_congr sum_fin_sum_equiv (equiv.refl _)

def append {n m : ℕ} (x : α^n) (y : α^m) : α^(n+m) :=
append_equiv (x, y)

localized "notation x `++` y := finvec.append x y" in finvec

lemma append_equiv_apply {n m : ℕ} {x : α^n} {y : α^m} : append_equiv (x, y) = x ++ y :=
rfl

@[simp] lemma append_left {n m : ℕ} (x : α^n) (y : α^m) : (x ++ y) ∘ fin.cast_add _ = x :=
begin
  suffices : ∀ p : α^n × α^m, append_equiv p ∘ fin.cast_add _ = p.1,
  { exact this (x, y) },
  -- TODO: improved lemma
  rw append_equiv.forall_congr_left',
  intro p,
  rw equiv.apply_symm_apply,
  refl
end

@[simp] lemma append_right {n m : ℕ} (x : α^n) (y : α^m) : (x ++ y) ∘ fin.nat_add _ = y :=
begin
  suffices : ∀ p : α^n × α^m, append_equiv p ∘ fin.nat_add _ = p.2,
  { exact this (x, y) },
  -- TODO: improved lemma
  rw append_equiv.forall_congr_left',
  intro p,
  rw equiv.apply_symm_apply,
  refl
end

def external_prod {n m : ℕ} (s : set (α^n)) (t : set (α^m)) : set (α^(n + m)) :=
{x | x ∘ fin.cast_add m ∈ s ∧ x ∘ fin.nat_add n ∈ t}

-- precedence matching ∩
localized "infixr ` ⊠ `:70 := finvec.external_prod" in finvec

lemma external_prod_def {n m : ℕ} (s : set (α^n)) (t : set (α^m)) (x : α^(n+m)) :
  x ∈ s ⊠ t ↔ x ∘ fin.cast_add m ∈ s ∧ x ∘ fin.nat_add n ∈ t :=
iff.rfl

lemma append_mem_external_prod {n m : ℕ} (s : set (α^n)) (t : set (α^m)) (x : α^n) (y : α^m) :
  x ++ y ∈ s ⊠ t ↔ x ∈ s ∧ y ∈ t :=
by rw [external_prod_def, append_left, append_right]

end finvec
