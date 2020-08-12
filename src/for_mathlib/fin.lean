import data.fin

lemma fin.cast_id {n : ℕ} {h : n = n} : fin.cast h = id :=
by { ext, apply fin.cast_val }

@[simp] lemma fin.nat_add_val {n m : ℕ} (i : fin n) : (i.nat_add m).val = m + i.val :=
rfl

lemma fin.nat_add_zero {n : ℕ} : fin.nat_add 0 = fin.cast (zero_add n).symm :=
by { ext, rw fin.cast_val, apply zero_add }

lemma fin.nat_add_add {n m k : ℕ} :
  fin.nat_add (m+k) = fin.cast (add_assoc m k n).symm ∘ fin.nat_add m ∘ fin.nat_add k :=
by { ext, rw fin.cast_val, apply add_assoc }

