import data.equiv.fin
import for_mathlib.fin

namespace finvec

variables {α : Type*}

localized "notation R `^` n := fin n → R" in finvec

def external_prod {n m : ℕ} (s : set (α^n)) (t : set (α^m)) : set (α^(n + m)) :=
{x | x ∘ fin.cast_add m ∈ s ∧ x ∘ fin.nat_add n ∈ t}

-- precedence matching ∩
localized "infixr ` ⊠ `:70 := finvec.external_prod" in finvec

lemma external_prod_def {n m : ℕ} (s : set (α^n)) (t : set (α^m)) (x : α^(n+m)) :
  x ∈ s ⊠ t ↔ x ∘ fin.cast_add m ∈ s ∧ x ∘ fin.nat_add n ∈ t :=
iff.rfl

end finvec
