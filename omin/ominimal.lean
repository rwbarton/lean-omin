import data.finset
import data.set.finite
import .algebra

-- Maybe a good idea to use intervals bounded by `option R` to handle ±∞?

-- section IOO
-- variables {R : Type*} [preorder R]

-- def IOO (A B : option R) : set R :=
-- {r | (∀ a ∈ A, a < r) ∧ (∀ b ∈ B, r < b)}

-- end IOO

variables {R : Type*} [nonempty R] [decidable_linear_order R] [densely_ordered R] [no_bot_order R] [no_top_order R]

inductive interval_or_point : set R → Prop
| pt (r : R) : interval_or_point {r}
| Iii : interval_or_point set.univ
| Ioi (a : R) : interval_or_point (set.Ioi a)
| Iio (b : R) : interval_or_point (set.Iio b)
| Ioo (a b : R) (h : a < b) : interval_or_point (set.Ioo a b)

def tame_r (s : set R) : Prop :=
∃ (I : finset (set R)), (∀ i ∈ I, interval_or_point i) ∧ s = ⋃ i ∈ I, i

/-- Induction principle:
Every tame set of R can be built up from the empty set
by repeatedly forming the union with a single interval or point. -/
lemma tame_r.induction_on {C : set R → Prop}
  (h₀ : C ∅) (h₁ : ∀ {s : set R} {i : set R}, /- tame_r s → -/ interval_or_point i → C s → C (i ∪ s)) :
  ∀ {s : set R}, tame_r s → C s :=
begin
  suffices : ∀ (I : finset (set R)), (∀ i ∈ I, interval_or_point i) → C (⋃ i ∈ I, i),
  { rintros _ ⟨I, hI, rfl⟩, exact this I hI },
  classical,
  refine finset.induction (by { intro, simpa }) _,
  intros i I hi IH hI,
  rw finset.bUnion_insert,
  exact h₁ (hI i (finset.mem_insert_self i I)) (IH (λ i' hi', hI i' (finset.mem_insert_of_mem hi')))
end

lemma interval_or_point.finite_or_contains_interval {i : set R} (h : interval_or_point i) :
  i.finite ∨ ∃ (a b : R), a < b ∧ set.Ioo a b ⊆ i :=
begin
  rcases h with _|_|⟨a⟩|⟨b⟩|⟨a,b,hab⟩,
  { exact or.inl (set.finite_singleton _) },
  all_goals { right },
  { have a : R := classical.arbitrary R, -- classical is unnecessary, but standard library is annoying here
    obtain ⟨b, h⟩ := no_top a,
    exact ⟨a, b, h, set.subset_univ _⟩ },
  { obtain ⟨b, h⟩ := no_top a,
    exact ⟨a, b, h, λ x ⟨hax, hxb⟩, hax⟩ },
  { obtain ⟨a, h⟩ := no_bot b,
    exact ⟨a, b, h, λ x ⟨hax, hxb⟩, hxb⟩ },
  { exact ⟨a, b, hab, set.subset.refl _⟩ }
end

lemma tame_r.finite_or_contains_interval {s : set R} (h : tame_r s) :
  s.finite ∨ ∃ (a b : R), a < b ∧ set.Ioo a b ⊆ s :=
begin
  revert h,
  refine tame_r.induction_on (or.inl set.finite_empty) _,
  clear s,
  rintros s i hi (fin|⟨a,b,ab,hab⟩),
  { rcases hi.finite_or_contains_interval with ifin|⟨ia,ib,iab,ih⟩,
    { left, exact set.finite.union ifin fin },
    { right, exact ⟨ia, ib, iab, set.subset.trans ih (set.subset_union_left _ _)⟩ } },
  { right, exact ⟨a, b, ab, set.subset.trans hab (set.subset_union_right _ _)⟩ }
end

variables (S : struc R) [definable_constants S] [definable_lt S]

-- TODO: Prove any tame_r set is definable

class o_minimal : Prop :=
(tame_of_definable : ∀ (s : set R), S.definable_set s → tame_r s)
