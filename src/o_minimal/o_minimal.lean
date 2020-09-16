import for_mathlib.boolean_subalgebra
import for_mathlib.closure
import for_mathlib.order
import o_minimal.order
import o_minimal.tame.basic

/- Definition of an *o-minimal* structure. -/

namespace o_minimal

set_option old_structure_cmd true   -- TODO: Is this needed?

variables {R : Type*} [DUNLO R]

lemma interval_or_point.def_set {S : struc R} [definable_constants S] [is_definable_le S R] :
  ∀ {i : set R}, interval_or_point i → def_set S i
| _ (interval_or_point.pt _) := def_val_const
| _ interval_or_point.Iii := def_set_univ _
| _ (interval_or_point.Ioi a) := def_set.Ioi a
| _ (interval_or_point.Iio b) := def_set.Iio b
| _ (interval_or_point.Ioo a b _) := def_set.Ioo a b

/-- Tame sets are definable. -/
lemma tame.def_set {S : struc R} [definable_constants S] [is_definable_le S R]
  {s : set R} (h : tame s) : def_set S s :=
tame.induction (def_set_empty _) (λ s _ i ih, i.def_set.union ih) h

/-- An o-minimal structure is one in which every definable subset of R is tame. -/
def is_o_minimal {S : struc R} [definable_constants S] [is_definable_le S R] : Prop := ∀ (s : set R), def_set S s → tame s

/-- An o-minimal structure on a DUNLO `R` is a structure `S` for which:
1. `S` has definable constants.
2. The `≤` relation on `R` is definable in `S`.
3. Every definable subset of `R` is tame (a union of points and open intervals).

Below we verify that this definition agrees with the one of [vdD].
-/
class o_minimal (S : struc R) extends definable_constants S, is_definable_le S R : Prop :=
(tame_of_def : ∀ {s : set R}, def_set S s → tame s)

/-- Version of `o_minimal.tame_of_def` with explicit structure argument.
This is useful because otherwise `S` can only be inferred from the proof of definability,
which we might want to produce automatically. -/
lemma tame_of_def (S : struc R) [o_minimal S] {s : set R} : def_set S s → tame s :=
o_minimal.tame_of_def

/-- Our definition of an o-minimal structure is equivalent to the one in [vdD:1.3.2]. -/
lemma o_minimal_iff_vdD (S : struc R) : o_minimal S ↔
  (def_set S {p : R × R | p.1 < p.2} ∧ ∀ (s : set R), def_set S s ↔ tame s) :=
⟨λ h, by exactI ⟨definable_lt', λ s, ⟨o_minimal.tame_of_def, tame.def_set⟩⟩,
 λ ⟨h₁, h₂⟩,
 { definable_val := λ r, (h₂ _).mpr (tame_single (interval_or_point.pt r)),
   definable_le' := (is_definable_le_of_definable_lt h₁).1,
   tame_of_def := λ s, (h₂ s).mp }⟩

-- TODO: for_mathlib
lemma function.const_injective {α β : Type*} [H : nonempty α] :
  function.injective (function.const α : β → α → β) :=
let ⟨a⟩ := H in λ b₁ b₂ h, congr_fun h a

/-- An alternate constructor expressed in terms of low-level definability. -/
lemma o_minimal.mk' (S : struc R)
  (definable_lt : S.definable {x : finvec 2 R | x 0 < x 1})
  (definable_const : ∀ (r : R), S.definable {x : finvec 1 R | x 0 = r})
  (tame_of_definable :
    ∀ (s : set (finvec 1 R)), S.definable s → tame {r | (λ _, r : finvec 1 R) ∈ s}) :
  o_minimal S :=
{ definable_val := begin
    intro r,
    unfold def_val def_set,
    convert definable_const r,
    apply set.ext,
    simp_rw [set.mem_image],
    change ∀ (x : fin 1 → R), _ ↔ x 0 = r,
    rw (equiv.fun_unique (fin 1) R).forall_congr_left',
    intro r',
    simp only [equiv.fun_unique, equiv.coe_fn_symm_mk, set.mem_singleton_iff,
      exists_eq_left, has_coordinates.self_coords, function.const_injective.eq_iff],
    exact eq_comm
  end,
  definable_le' := begin
    refine (is_definable_le_of_definable_lt _).1,
    unfold def_val def_set,
    convert definable_lt,
    apply set.ext,
    simp_rw [set.mem_image],
    change ∀ (x : finvec 2 R), _ ↔ x 0 < x 1,
    rw finvec.finvec_two_equiv_prod_self.forall_congr_left',
    rintro ⟨x₀, x₁⟩,
    change _ ↔ x₀ < x₁,
    simp [has_coordinates.prod_coords, finvec.finvec_two_equiv_prod_self,
      finvec.append.inj_iff, function.const_injective.eq_iff, ←and_assoc]
  end,
  tame_of_def := begin
    intros s hs,
    convert tame_of_definable _ hs,
    ext x,
    simp [function.const_injective.eq_iff]
  end }

end o_minimal
