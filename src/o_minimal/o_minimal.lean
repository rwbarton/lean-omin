import o_minimal.order

namespace o_minimal

/-- A DUNLO is a dense unbounded nonempty linear order.
This is the setting in which we can talk about o-minimal structures.
See [vdD], §1.3, first italicized paragraph.
-/
class DUNLO (R : Type*) extends decidable_linear_order R :=
[dense : densely_ordered R]
[unbounded_below : no_bot_order R]
[unbounded_above : no_top_order R]
[nonempty : nonempty R]

-- These classes are all `Prop`s so these instances should be harmless.
attribute [instance] DUNLO.dense DUNLO.unbounded_below DUNLO.unbounded_above DUNLO.nonempty

instance : DUNLO ℚ := {}

variables {R : Type*} [DUNLO R]

/-- A (nonempty) open interval (possibly unbounded on one or both sides)
or a single point.
One of the building blocks of a tame set. -/
inductive interval_or_point : set R → Prop
| pt (r : R) : interval_or_point {r}
| Iii : interval_or_point set.univ
| Ioi (a : R) : interval_or_point (set.Ioi a)
| Iio (b : R) : interval_or_point (set.Iio b)
| Ioo (a b : R) (h : a < b) : interval_or_point (set.Ioo a b)

/-- A tame subset of `R` is one that can be expressed as
a finite union of intervals and points. -/
def tame (s : set R) : Prop :=
∃ (I : finset (set R)), (∀ i ∈ I, interval_or_point i) ∧ s = ⋃ i ∈ I, i

lemma tame_single {i : set R} (h : interval_or_point i) : tame i :=
⟨{i}, by simp [h]⟩

-- TODO: tame_empty, tame.union

-- TODO: A tame set has a normal form as the union of
-- a minimal list of nonoverlapping intervals and points, arranged in increasing order.
-- Is this useful?

/-- Induction principle:
Every tame set of R can be built up from the empty set
by repeatedly forming the union with a single interval or point. -/
lemma tame.induction {C : set R → Prop}
  (h₀ : C ∅) (h₁ : ∀ {s : set R} {i : set R}, /- tame_r s → -/ interval_or_point i → C s → C (i ∪ s)) :
  ∀ {s : set R}, tame s → C s :=
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

/-- A dichotomy for tame sets: either they are finite
or they contain an entire interval. -/
lemma tame.finite_or_contains_interval {s : set R} (h : tame s) :
  s.finite ∨ ∃ (a b : R), a < b ∧ set.Ioo a b ⊆ s :=
begin
  revert h,
  refine tame.induction (or.inl set.finite_empty) _,
  clear s,
  rintros s i hi (fin|⟨a,b,ab,hab⟩),
  { rcases hi.finite_or_contains_interval with ifin|⟨ia,ib,iab,ih⟩,
    { left, exact set.finite.union ifin fin },
    { right, exact ⟨ia, ib, iab, set.subset.trans ih (set.subset_union_left _ _)⟩ } },
  { right, exact ⟨a, b, ab, set.subset.trans hab (set.subset_union_right _ _)⟩ }
end

variables {R}

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

/-- Our definition of an o-minimal structure is equivalent to the one in [vdD:1.3.2]. -/
lemma o_minimal_iff_vdD (S : struc R) : o_minimal S ↔
  (def_set S {p : R × R | p.1 < p.2} ∧ ∀ (s : set R), def_set S s ↔ tame s) :=
⟨λ h, by exactI ⟨definable_lt', λ s, ⟨o_minimal.tame_of_def, tame.def_set⟩⟩,
 λ ⟨h₁, h₂⟩,
 { definable_val := λ r, (h₂ _).mpr (tame_single (interval_or_point.pt r)),
   definable_le' := (is_definable_le_of_definable_lt h₁).1,
   tame_of_def := λ s, (h₂ s).mp }⟩

end o_minimal
