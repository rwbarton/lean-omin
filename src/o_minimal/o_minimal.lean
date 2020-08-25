import for_mathlib.closure
import o_minimal.order

namespace o_minimal

/-- A DUNLO is a dense unbounded nonempty linear order.
This is the setting in which we can talk about o-minimal structures.
See [vdD], §1.3, first italicized paragraph.
-/
-- Remark: We use `decidable_linear_order` in order to have access to `⊔`, `⊓`.
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

lemma interval_or_point.as_IOO {s : set R} (hs : interval_or_point s) :
  (∃ r, s = {r}) ∨
  (∃ (a : with_bot R) (b : with_top R), s = {x | a < ↑x ∧ ↑x < b}) :=
begin
  -- Use `induction` because `cases` does undesired definitional unfolding.
  induction hs with r a b a b;
  [ exact or.inl ⟨r, rfl⟩,
    refine or.inr ⟨⊥, ⊤, _⟩,
    refine or.inr ⟨a, ⊤, _⟩,
    refine or.inr ⟨⊥, b, _⟩,
    refine or.inr ⟨a, b, _⟩ ];
  { ext x, simp [with_bot.bot_lt_coe, with_top.coe_lt_top, with_bot.coe_lt_coe, with_top.coe_lt_coe] }
end

/-- A tame subset of `R` is one that can be expressed as
a finite union of intervals and points. -/
def tame : set R → Prop :=
finite_union_closure interval_or_point

lemma tame_iff {s : set R} : tame s ↔ ∃ (I : finset (set R)), (∀ i ∈ I, interval_or_point i) ∧ s = ⋃ i ∈ I, i :=
finite_union_closure_iff_bUnion

lemma tame_single {i : set R} (h : interval_or_point i) : tame i :=
finite_union_closure.basic h

lemma tame_empty : tame (∅ : set R) :=
finite_union_closure.empty

lemma tame_univ : tame (set.univ : set R) :=
tame_single interval_or_point.Iii

lemma tame_const {p : Prop} : tame {r : R | p} :=
begin
  by_cases h : p,
  { convert tame_univ, simp [h] },
  { convert tame_empty, simp [h], refl }
end

-- TODO: for_mathlib. after finset.singleton_inter_of_not_mem. Fix proof.
lemma set.singleton_inter_of_mem {α : Type*} {a : α} {s : set α} (h : a ∈ s) : {a} ∩ s = {a} :=
by { ext x, simp [h], intro H, rwa H }

-- Rather specialized lemma for use in closure under finite intersections.
lemma tame_singleton_inter (r : R) (s : set R) : tame ({r} ∩ s) :=
begin
  by_cases h : r ∈ s,
  { rw set.singleton_inter_of_mem h,
    exact tame_single (interval_or_point.pt r) },
  { rw set.singleton_inter_eq_empty.mpr h,
    exact finite_union_closure.empty }
end

lemma with_bot.as_bot_or_coe {α : Type*} : ∀ (a : with_bot α), a = ⊥ ∨ ∃ (x : α), a = x
| none := or.inl rfl
| (some x) := or.inr ⟨x, rfl⟩

lemma with_top.as_top_or_coe {α : Type*} : ∀ (a : with_top α), a = ⊤ ∨ ∃ (x : α), a = x
| none := or.inl rfl
| (some x) := or.inr ⟨x, rfl⟩

lemma tame_IOO (a : with_bot R) (b : with_top R) :
  tame {x : R | a < ↑x ∧ ↑x < b} :=
begin
  rcases with_bot.as_bot_or_coe a with rfl|⟨a, rfl⟩;
  rcases with_top.as_top_or_coe b with rfl|⟨b, rfl⟩;
  simp [with_bot.bot_lt_coe, with_top.coe_lt_top, with_bot.coe_lt_coe, with_top.coe_lt_coe],
  all_goals { try { { apply tame_single, constructor } } }, -- { { } }, because only do it if we're done.
  by_cases h : a < b,
  { exact tame_single (interval_or_point.Ioo a b h) },
  { convert finite_union_closure.empty,
    rw set.eq_empty_iff_forall_not_mem,
    rintros x ⟨hx₁, hx₂⟩,
    exact h (lt_trans hx₁ hx₂) }
end

lemma closed_under_finite_inters_tame : closed_under_finite_inters (tame : set R → Prop) :=
begin
  apply closed_under_finite_inters_finite_union_closure,
  { exact tame_single interval_or_point.Iii },
  { intros s s' hs hs',
    rcases hs.as_IOO with ⟨r, rfl⟩ | ⟨a, b, rfl⟩, { apply tame_singleton_inter },
    rcases hs'.as_IOO with ⟨r', rfl⟩ | ⟨a', b', rfl⟩, { rw set.inter_comm, apply tame_singleton_inter },
    convert tame_IOO (a ⊔ a') (b ⊓ b') using 1,
    ext x,
    simp only [set.mem_inter_iff, set.mem_set_of_eq],
    rw [sup_lt_iff, lt_inf_iff],
    tauto }
end

-- TODO: A tame set has a normal form as the union of
-- a minimal list of nonoverlapping intervals and points, arranged in increasing order.
-- Is this useful?

/-- Induction principle:
Every tame set of R can be built up from the empty set
by repeatedly forming the union with a single interval or point. -/
-- TODO: Generalize this to finite_union_closure
lemma tame.induction {C : set R → Prop}
  (h₀ : C ∅) (h₁ : ∀ {s : set R} {i : set R}, /- tame_r s → -/ interval_or_point i → C s → C (i ∪ s)) :
  ∀ {s : set R}, tame s → C s :=
begin
  suffices : ∀ (I : finset (set R)), (∀ i ∈ I, interval_or_point i) → C (⋃ i ∈ I, i),
  { intros s hs, obtain ⟨I, hI, rfl⟩ := tame_iff.mp hs, exact this I hI },
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

-- TODO: for_mathlib
lemma function.const_injective {α β : Type*} [H : nonempty α] :
  function.injective (function.const α : β → α → β) :=
let ⟨a⟩ := H in λ b₁ b₂ h, congr_fun h a

/-- An alternate constructor expressed in terms of low-level definability. -/
lemma o_minimal.mk' (S : struc R)
  (definable_lt : S.definable {x : fin 2 → R | x 0 < x 1})
  (definable_const : ∀ (r : R), S.definable {x : fin 1 → R | x 0 = r})
  (tame_of_definable :
    ∀ (s : set (fin 1 → R)), S.definable s → tame {r | (λ _, r : fin 1 → R) ∈ s}) :
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
    change ∀ (x : fin 2 → R), _ ↔ x 0 < x 1,
    rw finvec.fin_two_fun_equiv_prod_self.forall_congr_left',
    rintro ⟨x₀, x₁⟩,
    change _ ↔ x₀ < x₁,
    simp [has_coordinates.prod_coords, finvec.fin_two_fun_equiv_prod_self,
      finvec.append.inj_iff, function.const_injective.eq_iff, ←and_assoc]
  end,
  tame_of_def := begin
    intros s hs,
    convert tame_of_definable _ hs,
    ext x,
    simp [function.const_injective.eq_iff]
  end }

end o_minimal
