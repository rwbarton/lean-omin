import omin.structure
import data.set.intervals

-- compatibility of algebraic + order structures with a structure

variables {R : Type*}

class definable_has_add (S : struc R) [has_add R] : Prop :=
(definable_has_add : S.definable_fun (λ (p : R × R), p.1 + p.2))

class definable_has_mul (S : struc R) [has_mul R] : Prop :=
(definable_has_add : S.definable_fun (λ (p : R × R), p.1 * p.2))

class definable_lt (S : struc R) [has_lt R] : Prop :=
(definable_lt : S.definable_set {p : R × R | p.1 < p.2})

lemma definable_set_lt (S : struc R) [has_lt R] [definable_lt S]
  {X : Type*} [definable S X]
  {f : X → R} (hf : S.definable_fun f) {g : X → R} (hg : S.definable_fun g) :
  S.definable_set {x | f x < g x} :=
sorry

lemma definable_le (S : struc R) [decidable_linear_order R] [definable_lt S] :
  S.definable_set {p : R × R | p.1 ≤ p.2} :=
begin
  apply S.definable_set_of_iff {p : R × R | ¬ p.1 > p.2}, { simp },
  -- rest of the proof should be automated!
  apply_rules [struc.definable_set.compl, definable_set_lt, struc.definable.fst, struc.definable.snd]
end

section interval

instance definable.Ioo (S : struc R) [preorder R]
  [definable_lt S] [definable_constants S] (a b : R) : definable S (set.Ioo a b) :=
definable.subset S $
begin
  change S.definable_set {x : R | a < x ∧ x < b},
  apply_rules [struc.definable_set.inter, definable_set_lt, struc.definable.const, struc.definable.id]
end

-- example from FoMM '20 talk
variables (S : struc R) [preorder R] [definable_lt S] [definable_constants S]
variables (a b : R) (f : set.Ioo a b → R) (hf : S.definable_fun f)

lemma definable_K : S.definable_set {x | ∀ x', f x = f x' → x ≤ x'} :=
sorry

end interval
