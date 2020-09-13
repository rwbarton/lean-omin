import order.boolean_algebra
import for_mathlib.closure

variables {B : Type*} [boolean_algebra B]
-- Main example of interest: B = set α, or a boolean subalgebra.

-- Other descriptions are possible (the dual one using ⊤ and ⊓, for a start);
-- we could provide alternate constructors for these.
structure is_boolean_subalgebra (s : set B) : Prop :=
(mem_bot : ⊥ ∈ s)
(mem_sup {x y} : x ∈ s → y ∈ s → x ⊔ y ∈ s)
(mem_compl {x} : x ∈ s → xᶜ ∈ s)

lemma is_boolean_subalgebra.mem_inf {s : set B} (h : is_boolean_subalgebra s)
  {x y} (hx : x ∈ s) (hy : y ∈ s) : x ⊓ y ∈ s :=
begin
  convert h.mem_compl (h.mem_sup (h.mem_compl hx) (h.mem_compl hy)),
  simp
end

lemma is_boolean_subalgebra.mem_top {s : set B} (h : is_boolean_subalgebra s) :
  ⊤ ∈ s :=
begin
  convert h.mem_compl h.mem_bot,
  rw compl_bot
end

namespace boolean_subalgebra

/-- The smallest boolean subalgebra containing a given set `s`. -/
inductive gen (s : set B) : set B
| basic {x} : x ∈ s → gen x
| bot : gen ⊥
| sup {x y} : gen x → gen y → gen (x ⊔ y)
| compl {x} : gen x → gen (xᶜ)

lemma gen.is_boolean_subalgebra {s : set B} : is_boolean_subalgebra (gen s) :=
⟨gen.bot, λ x y, gen.sup, λ x, gen.compl⟩

-- TODO(?): These lemmas don't have quite the same shape as the constructors
-- (phrased in terms of ∈, not function application)

lemma gen.top {s : set B} : ⊤ ∈ gen s :=
gen.is_boolean_subalgebra.mem_top

lemma gen.inf {s : set B} {x y} : x ∈ gen s → y ∈ gen s → x ⊓ y ∈ gen s :=
gen.is_boolean_subalgebra.mem_inf

lemma gen_subset_iff_subset {s t : set B} (ht : is_boolean_subalgebra t) :
  gen s ⊆ t ↔ s ⊆ t :=
begin
  split; intro h,
  { intros x hx,
    exact h (gen.basic hx) },
  { intros x₀ hx₀,
    induction hx₀ with x hx x y hx hy IHx IHy x hx IHx; clear x₀,
    { exact h hx },
    { exact ht.mem_bot },
    { exact ht.mem_sup IHx IHy },
    { exact ht.mem_compl IHx } }
end

lemma gen_subset_gen_iff_subset_gen {s t : set B} :
  gen s ⊆ gen t ↔ s ⊆ gen t :=
gen_subset_iff_subset gen.is_boolean_subalgebra

lemma self_subset_gen {s : set B} : s ⊆ gen s :=
by rw ←gen_subset_gen_iff_subset_gen

lemma gen_mono {s t : set B} (h : s ⊆ t) : gen s ⊆ gen t :=
begin
  rw gen_subset_gen_iff_subset_gen,
  exact set.subset.trans h self_subset_gen,
end

end boolean_subalgebra

variables {α : Type*}
lemma finite_union_closure_subset_gen {s : set (set α)} :
  finite_union_closure s ⊆ boolean_subalgebra.gen s :=
begin
  intros x hx,
  induction hx with x hx x y hx hy IHx IHy,
  { exact boolean_subalgebra.gen.basic hx },
  { exact boolean_subalgebra.gen.bot },
  { exact boolean_subalgebra.gen.sup IHx IHy }
end
