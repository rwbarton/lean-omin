import o_minimal.structure

namespace finvec

open o_minimal
open_locale finvec

variables {R : Type*} {n n' : ℕ} {A : set (fin n → R)}

-- TODO: use to rewrite cast_id
lemma cast_id' {n : ℕ} {h : n = n} : finvec.cast h = @id (fin n → R) :=
by { ext x ⟨i, _⟩, refl }

lemma heq_iff_cast_eq {B : set (fin n' → R)} (h : n = n') :
  A == B ↔ A = finvec.cast h ⁻¹' B :=
begin
  cases h,
  rw [heq_iff_eq, finvec.cast_id'],
  refl
end

-- CAUTION: Open only in case of emergency.
lemma r_prod_eq : U 1 ⊠ A == @fin.tail n (λ _, R) ⁻¹' A :=
begin
  -- TODO: Fix this garbage proof, and possibly refactor users.
  rw heq_iff_cast_eq (nat.add_comm _ _),
  ext x,
  rw external_prod_def,
  simp,
  rw iff_iff_eq,
  congr,
  ext ⟨i,_⟩,
  simp [right, fin.nat_add],
  congr,
  rw add_comm,
  refl
end

lemma prod_r_eq : A ⊠ U 1 = fin.init ⁻¹' A :=
begin
  ext x,
  rw external_prod_def,
  simp, refl
end

end finvec
