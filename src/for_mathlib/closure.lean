import data.finset
import data.fintype.basic

/-
Closure under finite unions or intersections.

TODO: Generalize the whole thing to sub-(meet/join)-semilattices?
-/

open set

section finite_unions

variables {α : Type*} (B : set (set α))

/-- The property of a family of sets being closed under finite unions. -/
structure closed_under_finite_unions : Prop :=
(mem_empty : ∅ ∈ B)
(mem_union {s t} : s ∈ B → t ∈ B → s ∪ t ∈ B)

/-- The closure of a family of sets under finite unions. -/
inductive finite_union_closure : set (set α)
| basic {s} : s ∈ B → finite_union_closure s
| empty : finite_union_closure ∅
| union {s t} : finite_union_closure s → finite_union_closure t → finite_union_closure (s ∪ t)

variables {B}

lemma closed_under_finite_unions.mem_bUnion (hB : closed_under_finite_unions B) {t : finset (set α)}
  (ht : ∀ i ∈ t, i ∈ B) : (⋃ i ∈ t, i) ∈ B :=
begin
  classical,
  revert ht,
  refine finset.induction_on t (by simpa using hB.mem_empty) _,
  intros a s _ ih ht,           -- TODO: use rintros -
  have h₁ : a ∈ B := ht a (finset.mem_insert_self a s),
  have h₂ : (⋃ i ∈ s, i) ∈ B := ih (λ i hi, ht i (finset.mem_insert_of_mem hi)),
  simpa using hB.mem_union h₁ h₂
end

/-- The closure of B under finite unions is closed under finite unions. -/
lemma closed_under_finite_unions_finite_union_closure :
  closed_under_finite_unions (finite_union_closure B) :=
{ mem_empty := finite_union_closure.empty,
  mem_union := λ _ _ hs ht, hs.union ht }

/-- The closure of B under finite unions contains B. -/
lemma closed_under_finite_unions_contains_self : B ⊆ finite_union_closure B :=
λ s, finite_union_closure.basic

/-- The closure of B under finite unions can also be described as
the class of sets which can be written as a finite union of members of B. -/
lemma finite_union_closure_iff_bUnion {s : set α} :
  s ∈ finite_union_closure B ↔
  ∃ t : finset (set α), (∀ i ∈ t, i ∈ B) ∧ s = ⋃ i ∈ t, i :=
begin
  split,
  { apply finite_union_closure.rec; clear s,
    { intros s hs,
      exact ⟨{s}, by simp [hs]⟩ },
    { exact ⟨∅, by simp⟩ },
    { rintros s s' hs hs' ⟨t, ht, hst⟩ ⟨t', ht', hst'⟩,
      classical,
      refine ⟨t ∪ t', _, _⟩,
      { intros _ hi,
        cases finset.mem_union.mp hi; solve_by_elim },
      { rw finset.bUnion_union, cc } } },
  { rintro ⟨t, ht, rfl⟩,
    refine closed_under_finite_unions_finite_union_closure.mem_bUnion (λ i hi, _),
    apply finite_union_closure.basic,
    exact ht i hi }
end

end finite_unions

section finite_inters

variables {α β : Type*} (B : set (set α))

/-- The property of a family of sets being closed under finite intersections. -/
structure closed_under_finite_inters : Prop :=
(mem_univ : univ ∈ B)
(mem_inter {s t} : s ∈ B → t ∈ B → s ∩ t ∈ B)

/-- The closure of a family of sets under finite intersections. -/
inductive finite_inter_closure : set (set α)
| basic {s} : s ∈ B → finite_inter_closure s
| univ : finite_inter_closure univ
| inter {s t} : finite_inter_closure s → finite_inter_closure t → finite_inter_closure (s ∩ t)

variables {B}

-- TODO: Fix name; this is actually mem_sInter or something
lemma closed_under_finite_inters.mem_bInter (hB : closed_under_finite_inters B) {t : finset (set α)}
  (ht : ∀ i ∈ t, i ∈ B) : (⋂ i ∈ t, i) ∈ B :=
begin
  classical,
  revert ht,
  refine finset.induction_on t (by simpa using hB.mem_univ) _,
  intros a s _ ih ht,           -- TODO: use rintros -
  have h₁ : a ∈ B := ht a (finset.mem_insert_self a s),
  have h₂ : (⋂ i ∈ s, i) ∈ B := ih (λ i hi, ht i (finset.mem_insert_of_mem hi)),
  simpa using hB.mem_inter h₁ h₂
end

-- TODO: Naming?
lemma closed_under_finite_inters.mem_fInter (hB : closed_under_finite_inters B)
  {ι : Type*} {t : finset ι} (s : ι → set α) (hs : ∀ i ∈ t, s i ∈ B) : (⋂ i ∈ t, s i) ∈ B :=
begin
  classical,
  revert hs,
  refine finset.induction_on t (by simpa using hB.mem_univ) _,
  intros a t' _ ih hs,           -- TODO: use rintros -
  rw finset.bInter_insert,
  apply hB.mem_inter (hs a (finset.mem_insert_self _ _)) (ih $ λ i hi, hs i (finset.mem_insert_of_mem hi))
end

/-- The closure of B under finite intersections is closed under finite intersections. -/
lemma closed_under_finite_inters_finite_inter_closure :
  closed_under_finite_inters (finite_inter_closure B) :=
{ mem_univ := finite_inter_closure.univ,
  mem_inter := λ _ _ hs ht, hs.inter ht }

/-- The closure of B under finite intersections contains B. -/
lemma closed_under_finite_inters_contains_self : B ⊆ finite_inter_closure B :=
λ s, finite_inter_closure.basic

/-- The closure of B under finite intersections can also be described as
the class of sets which can be written as a finite intersection of members of B. -/
lemma finite_inter_closure_iff_bInter {s : set α} :
  s ∈ finite_inter_closure B ↔
  ∃ t : finset (set α), (∀ i ∈ t, i ∈ B) ∧ s = ⋂ i ∈ t, i :=
begin
  split,
  { apply finite_inter_closure.rec; clear s,
    { intros s hs,
      exact ⟨{s}, by simp [hs]⟩ },
    { exact ⟨∅, by simp⟩ },
    { rintros s s' hs hs' ⟨t, ht, hst⟩ ⟨t', ht', hst'⟩,
      classical,
      refine ⟨t ∪ t', _, _⟩,
      { intros _ hi,
        cases finset.mem_union.mp hi; solve_by_elim },
      { rw finset.bInter_inter, cc } } },
  { rintro ⟨t, ht, rfl⟩,
    refine closed_under_finite_inters_finite_inter_closure.mem_bInter (λ i hi, _),
    apply finite_inter_closure.basic,
    exact ht i hi }
end

structure preserves_finite_inters (Φ : set α → set β) : Prop :=
(map_univ : Φ univ = univ)
(map_inter : ∀ {s t}, Φ (s ∩ t) = Φ s ∩ Φ t)

lemma preserves_finite_inters.bind {Φ : set α → set β} (hΦ : preserves_finite_inters Φ)
  {A : set (set α)} {B : set (set β)} (h : ∀ s ∈ A, Φ s ∈ finite_inter_closure B) :
  ∀ s ∈ finite_inter_closure A, Φ s ∈ finite_inter_closure B :=
begin
  apply finite_inter_closure.rec,
  { exact h },
  { rw hΦ.map_univ, exact finite_inter_closure.univ },
  { intros _ _ _ _ IHs IHt,     -- TODO: rcases -
    rw hΦ.map_inter,
    exact IHs.inter IHt }
end

end finite_inters

-- Okay, now for a real theorem.
variables {α : Type*} (B : set (set α))

/-- Suppose finite intersections of members of B
belong to the closure of B under finite unions.
Then the latter is closed under finite intersections. -/
lemma closed_under_finite_inters_finite_union_closure
  (h₀ : univ ∈ finite_union_closure B)
  (h₂ : ∀ {s t}, s ∈ B → t ∈ B → s ∩ t ∈ finite_union_closure B) :
  closed_under_finite_inters (finite_union_closure B) :=
begin
  refine ⟨h₀, λ s₀ s' hs₀ hs', _⟩,
  revert s',
  induction hs₀ with s hs s₁ s₂ hs₁ hs₂ IH₁ IH₂; clear s₀,
  { intros s'₀ hs'₀,
    induction hs'₀ with s' hs' s'₁ s'₂ hs'₁ hs'₂ IH'₁ IH'₂; clear s'₀,
    { exact h₂ hs hs' },
    { convert finite_union_closure.empty, simp },
    { convert finite_union_closure.union IH'₁ IH'₂, rw inter_union_distrib_left } },
  { intros,
    convert finite_union_closure.empty, simp },
  { intros s' hs',
    convert finite_union_closure.union (IH₁ s' hs') (IH₂ s' hs'),
    rw union_inter_distrib_right }
end

/-- Suppose finite intersections and complements of members of B
belong to the closure of B under finite unions.
Then the latter is closed under complements. -/
lemma closed_under_complements_finite_union_closure
  (h₀ : univ ∈ finite_union_closure B)
  (h₂ : ∀ {s t}, s ∈ B → t ∈ B → s ∩ t ∈ finite_union_closure B)
  (hc : ∀ {s}, s ∈ B → sᶜ ∈ finite_union_closure B) :
  ∀ {s}, s ∈ finite_union_closure B → sᶜ ∈ finite_union_closure B :=
begin
  intros s' h,                  -- TODO: replace with rintros - h
  induction h with s h s t hs ht IHs IHt,
  { exact hc h },
  { convert h₀, simp },
  { rw compl_union,
    exact (closed_under_finite_inters_finite_union_closure B @h₀ @h₂).mem_inter IHs IHt }
end
