import data.equiv.fin

lemma fin.cast_id {n : ℕ} {h : n = n} : fin.cast h = id :=
by { ext, apply fin.cast_val }

@[simp] lemma fin.nat_add_val {n m : ℕ} (i : fin n) : (i.nat_add m).val = m + i.val :=
rfl

lemma fin.nat_add_zero {n : ℕ} : fin.nat_add 0 = fin.cast (zero_add n).symm :=
by { ext, rw fin.cast_val, apply zero_add }

lemma fin.nat_add_add {n m k : ℕ} :
  fin.nat_add (m+k) = fin.cast (add_assoc m k n).symm ∘ fin.nat_add m ∘ fin.nat_add k :=
by { ext, rw fin.cast_val, apply add_assoc }

@[simp] lemma sum_fin_sum_equiv_inl {m n : ℕ} (i : fin m) :
  sum_fin_sum_equiv (sum.inl i) = fin.cast_add n i :=
rfl

@[simp] lemma sum_fin_sum_equiv_inr {m n : ℕ} (i : fin n) :
  sum_fin_sum_equiv (sum.inr i) = fin.nat_add m i :=
rfl

