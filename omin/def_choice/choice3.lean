import algebra.module.ordered
import order.conditionally_complete_lattice
import ..oqm
-- import ..tame

-- Definable choice in 1 dimension.

section

-- TODO: for_mathlib order.bounds
-- also add mem_lower_bounds/is_least_def/etc.

lemma is_lub_def {α : Type*} [preorder α] (s : set α) (x : α) :
  is_lub s x ↔ (∀ a ∈ s, a ≤ x) ∧ (∀ y, (∀ a ∈ s, a ≤ y) → x ≤ y) :=
iff.rfl

lemma is_glb_def {α : Type*} [preorder α] (s : set α) (x : α) :
  is_glb s x ↔ (∀ a ∈ s, x ≤ a) ∧ (∀ y, (∀ a ∈ s, y ≤ a) → y ≤ x) :=
iff.rfl

end

section

open_locale classical

noncomputable def roption.orelse_pure {α : Type*} (a : roption α) (b : α) : α :=
if h : a.dom then a.get h else b

lemma roption.orelse_pure_eq_iff {α : Type*} {a : roption α} {b : α} (x : α) :
  a.orelse_pure b = x ↔ (x ∈ a ∨ (¬ ∃ y, y ∈ a) ∧ b = x) :=
begin
  unfold roption.orelse_pure,
  split_ifs; split; simp [h, roption.mem_eq]
end

end

local infixr ` <|| `:2 := roption.orelse_pure
local notation x ` >>* `:55 f:55 := f <$> x
--local infixr ` >>* `:55 := roption.my_fmap

open o_minimal

universe u

instance {R : Type u} {S : struc R} : is_definable S punit :=
begin
  constructor,
  convert S.definable_univ 0,
  apply set.eq_univ_of_forall,
  intro x,
  use ⟨⟩,
  ext i,
  fin_cases i
end

variables {R : Type u} [OQM R]

local notation `½` := (1/2 : ℚ)

variables {S : struc R} [o_minimal_add S]
variables {Y : Type u} [has_coordinates R Y] [is_definable S Y]

/-
lemma def_fun.rat_smul (q : ℚ) : def_fun S (λ (r : R), q • r) :=
begin
  unfold def_fun,
  induction q using rat.num_denom_cases_on' with n d hd,
  -- need to clear denominators to get {p : R × R | n • p.fst = d • p.snd},
  -- prove definability of nsmul by constant
  sorry
end
-/

lemma half_add_half {a : R} : ½ • a + ½ • a = a :=
by { rw ←add_smul, norm_num }

lemma def_fun.half : def_fun S (λ (r : R), ½ • r) :=
begin
  unfold def_fun,
  have : def_set S {p : R × R | p.1 = p.2 + p.2} :=
    def_set_eq def_fun.fst (definable.add def_fun.snd def_fun.snd),
  convert this,
  ext ⟨x, y⟩,
  dsimp,
  split; intro h,
  { subst y,
    rw half_add_half },
  { subst x,
    rw [smul_add, half_add_half] }
end

noncomputable def one : has_one R :=
⟨classical.some (no_top 0)⟩

local attribute [instance] one

/-
let's try to prove:
axiom definable_choice_1 {s : set (Y × R)} (hs : def_set S s) (h : prod.fst '' s = set.univ) :
  ∃ g : Y → R, def_fun S g ∧ ∀ y, (y, g y) ∈ s
-/

variables (S)

-- This is a structure just to avoid Lean instance cache nonsense
structure def_pfun_set (f : set R →. Y) : Prop :=
(def_graph : ∀ ⦃K : Type u⦄ [has_coordinates R K] [is_definable S K],
  -- f is definable after composition with any definable K → set R ≅ set (K × R) is
  -- resulting K →. R is definable if its graph is a definable subset of K × R
  ∀ s : set (K × R), def_set S s → def_set S {p : K × Y | p.2 ∈ f {r | (p.1, r) ∈ s}})

-- Goal: Prove the following type is inhabited.
def definable_choice_function : Type u :=
{choice : set R →. R //
 def_pfun_set S choice ∧ choice.dom = set.nonempty ∧ ∀ X H, tame X → (choice X).get H ∈ X}

-- going to run out of names for these quickly
structure def_rel_set (rel : set R → Y → Prop) : Prop :=
(def_graph : ∀ ⦃K : Type u⦄ [has_coordinates R K] [is_definable S K],
  ∀ s : set (K × R), def_set S s → def_set S {p : K × Y | rel {r | (p.1, r) ∈ s} p.2})

variables {S}

/-- Construct a definable partial function on sets from a definable relation.
This is sensible when the relation is single-valued:
`r` s.t. `rel X r` is unique if it exists. -/
noncomputable def pfun_of_rel (rel : set R → R → Prop) : set R →. R := λ X,
{ dom := ∃ r, rel X r,
  get := λ h, classical.some h }

lemma mem_pfun_of_rel_iff {rel : set R → R → Prop} (uni : ∀ X r r', rel X r → rel X r' → r = r')
  (X : set R) (r : R) : r ∈ pfun_of_rel rel X ↔ rel X r :=
begin
  split; intro H,
  { rcases H with ⟨H, rfl⟩,
    apply classical.some_spec },
  { exact ⟨⟨r, H⟩, uni _ _ _ (classical.some_spec _) H⟩ }
end

lemma def_pfun_of_rel {rel : set R → R → Prop} (uni : ∀ X r r', rel X r → rel X r' → r = r')
  (drel : def_rel_set S rel) : def_pfun_set S (pfun_of_rel rel) :=
begin
  constructor,
  introsI K _ _ s ds,
  convert drel.def_graph s ds,
  ext ⟨k, r⟩,
  apply mem_pfun_of_rel_iff uni
end

def the_least_rel (X : set R) (e : R) : Prop := is_least X e

noncomputable def the_least : set R →. R := pfun_of_rel the_least_rel

lemma def_the_least_rel : def_rel_set S (the_least_rel : set R → R → Prop) :=
begin
  constructor,
  introsI K _ _ s ds,
  dunfold the_least_rel is_least lower_bounds,
  -- now probably automatable
  apply def_set.and,
  { refine def_fun.preimage _ ds,
    exact def_fun.prod' def_fun.fst def_fun.snd },
  { apply def_set.forall,
    apply def_set.imp,
    { refine def_fun.preimage _ ds,
      exact (def_fun.fst.comp def_fun.fst).prod' def_fun.snd },
    { exact definable_le (def_fun.snd.comp def_fun.fst) def_fun.snd } }
end

lemma def_the_least : def_pfun_set S (the_least : set R →. R) :=
begin
  refine def_pfun_of_rel _ def_the_least_rel,
  apply is_least.unique
end

-- Now repeat for inf, sup.

noncomputable def the_inf : set R →. R := pfun_of_rel is_glb
noncomputable def the_sup : set R →. R := pfun_of_rel is_lub

lemma def_the_inf : def_pfun_set S (the_inf : set R →. R) :=
begin
  refine def_pfun_of_rel (λ _ _ _, is_glb.unique) _,
  constructor, introsI K _ _ s ds,
  simp_rw is_glb_def,
  apply def_set.and,
  { apply def_set.forall,
    apply def_set.imp,
    { refine def_fun.preimage _ ds,
      exact def_fun.prod' (def_fun.fst.comp def_fun.fst) def_fun.snd },
    { exact definable_le (def_fun.snd.comp def_fun.fst) def_fun.snd } },
  { apply def_set.forall,
    apply def_set.imp,
    { apply def_set.forall,
      apply def_set.imp,
      { refine def_fun.preimage _ ds,
        exact def_fun.prod' (def_fun.fst.comp (def_fun.fst.comp def_fun.fst)) def_fun.snd },
      { exact definable_le (def_fun.snd.comp def_fun.fst) def_fun.snd } },
    { exact definable_le def_fun.snd (def_fun.snd.comp def_fun.fst) } }
end

-- We don't actually use this yet (because we don't know how to)
-- lemma def_the_sup : def_pfun_set S (the_sup : set R →. R) := sorry

-- context
variables {Γ : Type*} [has_coordinates R Γ] [is_definable S Γ]

section
variables (S)
structure def_pfun_set_ctx (f : Γ → set R →. Y) : Prop :=
(def_graph : ∀ ⦃K : Type u⦄ [has_coordinates R K] [is_definable S K],
  ∀ s : set (K × R), def_set S s → def_set S {p : (Γ × K) × Y | p.2 ∈ f p.1.1 {r | (p.1.2, r) ∈ s}})

structure def_fun_set_ctx (f : Γ → set R → Y) : Prop :=
(def_graph : ∀ ⦃K : Type u⦄ [has_coordinates R K] [is_definable S K],
  ∀ s : set (K × R), def_set S s → def_set S {p : (Γ × K) × Y | f p.1.1 {r | (p.1.2, r) ∈ s} = p.2})

end

-- Definability of compound actions.
-- In the course of building these up, we also accumulate a context Γ.

lemma def_pfun_set_ctx.orelse_pure {f : Γ → set R →. R} {g : Γ → set R → R}
  (df : def_pfun_set_ctx S f) (dg : def_fun_set_ctx S g) :
  def_fun_set_ctx S (λ γ X, f γ X <|| g γ X) :=
begin
  constructor, introsI K _ _ s ds,
  replace df := df.1 s ds,
  replace dg := dg.1 s ds,
  simp_rw roption.orelse_pure_eq_iff,
  refine df.or (def_set.and _ dg),
  refine def_set.not (def_set.exists _),
  let φ : ((Γ × K) × R) × R → (Γ × K) × R := λ p, (p.1.1, p.2),
  have dφ : def_fun S φ := (def_fun.fst.comp def_fun.fst).prod' def_fun.snd,
  exact dφ.preimage df,
end

-- In `g`, the context has been extended by the result of `f`.

lemma def_pfun_set_ctx.bind {f : Γ → set R →. Y} {g : Γ → set R → Y → R}
  (df : def_pfun_set_ctx S f) (dg : def_fun_set_ctx S (λ (p : Γ × Y) X, g p.1 X p.2)) :
  def_pfun_set_ctx S (λ γ X, f γ X >>* g γ X) :=
begin
  constructor, introsI K _ _ s ds,
  replace df := df.1 s ds,
  replace dg := dg.1 s ds,
  simp only [exists_prop, roption.mem_map_iff, roption.map_eq_map],
  apply def_set.exists,
  apply def_set.and,
  { let φ : ((Γ × K) × R) × Y → (Γ × K) × Y := λ p, ((p.1.1.1, p.1.1.2), p.2),
    have dφ : def_fun S φ,
    { apply def_fun.prod',
      { apply def_fun.prod',
        { apply def_fun.fst.comp,
          apply def_fun.fst.comp,
          apply def_fun.fst },
        { apply def_fun.snd.comp,
          apply def_fun.fst.comp,
          apply def_fun.fst } },
      { exact def_fun.snd } },
    exact dφ.preimage df },
  { let φ : ((Γ × K) × R) × Y → ((Γ × Y) × K) × R := λ p, (((p.1.1.1, p.2), p.1.1.2), p.1.2),
    have dφ : def_fun S φ,
    { refine def_fun.prod' _ (def_fun.snd.comp def_fun.fst),
      refine def_fun.prod' _ (def_fun.snd.comp (def_fun.fst.comp def_fun.fst)),
      refine def_fun.prod' _ def_fun.snd,
      exact def_fun.fst.comp (def_fun.fst.comp def_fun.fst) },
    exact dφ.preimage dg }
end

-- Convert between versions with & without a context

lemma def_pfun_set.of_empty_ctx {f : set R →. Y} (df : def_pfun_set_ctx S (λ (p : punit) X, f X)) :
  def_pfun_set S f :=
begin
  constructor, introsI K _ _ s ds,
  have := df.1 s ds,
  let φ : K × Y → (punit × K) × Y := λ p, ((⟨⟩, p.1), p.2),
  have dφ : def_fun S φ := (def_fun_const.prod' def_fun.fst).prod' def_fun.snd,
  exact dφ.preimage this
end

lemma def_fun_set.of_empty_ctx {f : set R →. Y} (df : def_pfun_set S f) :
  def_pfun_set_ctx S (λ (γ : Γ) X, f X) :=
begin
  constructor, introsI K _ _ s ds,
  have := df.1 s ds,
  let φ : (Γ × K) × Y → K × Y := λ p, (p.1.2, p.2),
  have dφ : def_fun S φ := (def_fun.snd.comp def_fun.fst).prod' def_fun.snd,
  exact dφ.preimage this
end

-- TODO: "generalize" core library's `guard` to return `punit`?
-- TODO: super hack: we return 0 (ignored) instead of `punit`
-- just to be able to use `def_pfun_set.bind` in its current form;
-- but we could generalize the types involved in `def_pfun_set` to
-- arbitrary definable types to avoid this
-- TODO: We might have already generalized it enough.
def zero_when_nonempty : set R →. R :=
λ X, { dom := X.nonempty, get := λ _, (0 : R) }

noncomputable def chosen_one : set R →. R := λ X,
zero_when_nonempty X >>* λ _,
the_least X <||
(the_inf X >>* λ a,
  (the_sup {b | a < b ∧ set.Ioo a b ⊆ X} >>* λ b, ½ • (a + b)) <||
  a + 1) <||
(the_sup {b | set.Iio b ⊆ X} >>* λ b, b - 1) <||
0

lemma dom_chosen_one : (chosen_one : set R →. R).dom = set.nonempty :=
rfl

--set_option pp.all true
lemma def_chosen_one : def_pfun_set S (chosen_one : set R →. R) :=
begin
  apply def_pfun_set.of_empty_ctx,
  apply def_pfun_set_ctx.bind,
  { -- TODO: factor out this proof
    constructor,
    introsI K _ _ s ds,
    change def_set S {p | ∃ (H : ∃ _, _), (0 : R) = _},
    simp_rw exists_prop,
    apply def_set.and,
    { apply def_set.exists,
      refine def_fun.preimage _ ds,
      apply def_fun.prod',
      { apply def_fun.snd.comp,
        apply def_fun.fst.comp,
        exact def_fun.fst },
      { exact def_fun.snd } },
    { apply def_set_eq,
      { exact def_fun_const },
      { exact def_fun.snd } } },
  -- Now for the fun part
  apply def_pfun_set_ctx.orelse_pure,
  { apply def_fun_set.of_empty_ctx,
    apply def_the_least },
  apply def_pfun_set_ctx.orelse_pure,
  { apply def_pfun_set_ctx.bind,
    { apply def_fun_set.of_empty_ctx,
      apply def_the_inf },
    apply def_pfun_set_ctx.orelse_pure,
    { apply def_pfun_set_ctx.bind,
      { -- have := @def_the_sup R _ S _,
        -- now what? we need to know {b : R | γ.snd < b ∧ set.Ioo γ.snd b ⊆ X}
        -- depends definably on `γ.snd : R` and `X : set R`
        -- Definability of `Γ → set R → set R`?
        -- For now: let's just brute force it in a non-compositional way.
        constructor, introsI K _ _ s ds,
        simp only [the_sup, mem_pfun_of_rel_iff (@is_lub.unique R _), is_lub_def],
        apply def_set.and,
        { apply def_set.forall,
          apply def_set.imp,
          { apply def_set.and,
            { refine definable_lt _ def_fun.snd,
              apply def_fun.snd.comp,
              apply def_fun.fst.comp,
              apply def_fun.fst.comp,
              apply def_fun.fst },
            { apply def_set.forall,
              apply def_set.imp,
              { apply def_set.and,
                { refine definable_lt _ def_fun.snd,
                  apply def_fun.snd.comp,
                  apply def_fun.fst.comp,
                  apply def_fun.fst.comp,
                  apply def_fun.fst.comp,
                  apply def_fun.fst },
                { refine definable_lt def_fun.snd _,
                  apply def_fun.snd.comp,
                  apply def_fun.fst } },
              { refine def_fun.preimage _ ds,
                apply def_fun.prod',
                { apply def_fun.snd.comp,
                  apply def_fun.fst.comp,
                  apply def_fun.fst.comp,
                  apply def_fun.fst },
                { exact def_fun.snd } } } },
          { apply definable_le,
            { apply def_fun.snd },
            { apply def_fun.snd.comp,
              apply def_fun.fst } } },
        { apply def_set.forall,
          apply def_set.imp,
          { apply def_set.forall,
            apply def_set.imp,
            { apply def_set.and,
              { refine definable_lt _ def_fun.snd,
                apply def_fun.snd.comp,
                apply def_fun.fst.comp,
                apply def_fun.fst.comp,
                apply def_fun.fst.comp,
                apply def_fun.fst },
              { apply def_set.forall,
                apply def_set.imp,
                { apply def_set.and,
                  { refine definable_lt _ def_fun.snd,
                    { apply def_fun.snd.comp,
                      apply def_fun.fst.comp,
                      apply def_fun.fst.comp,
                      apply def_fun.fst.comp,
                      apply def_fun.fst.comp,
                      apply def_fun.fst } },
                  { refine definable_lt def_fun.snd _,
                    { apply def_fun.snd.comp,
                      apply def_fun.fst } } },
                { refine def_fun.preimage _ ds,
                  apply def_fun.prod',
                  { apply def_fun.snd.comp,
                    apply def_fun.fst.comp,
                    apply def_fun.fst.comp,
                    apply def_fun.fst.comp,
                    apply def_fun.fst },
                  { exact def_fun.snd } } } },
            { refine definable_le def_fun.snd _,
              exact def_fun.snd.comp def_fun.fst } },
          { refine definable_le _ def_fun.snd,
            exact def_fun.snd.comp def_fun.fst } } },
      { constructor, introsI K _ _ s ds,
        refine def_set_eq _ def_fun.snd,
        { refine def_fun.half.comp _,
          apply definable.add,
          { apply def_fun.snd.comp,
            apply def_fun.fst.comp,
            apply def_fun.fst.comp,
            apply def_fun.fst },
          { apply def_fun.snd.comp,
            apply def_fun.fst.comp,
            apply def_fun.fst } } } },
    { constructor, introsI K _ _ s ds,
      apply def_set_eq,
      { apply definable.add,
        { apply def_fun.snd.comp,
          apply def_fun.fst.comp,
          apply def_fun.fst },
        { apply def_fun_const } },
      { exact def_fun.snd } } },
  apply def_pfun_set_ctx.orelse_pure,
  { apply def_pfun_set_ctx.bind,
    -- like before, but simpler
    { constructor, introsI K _ _ s ds,
      simp only [the_sup, mem_pfun_of_rel_iff (@is_lub.unique R _), is_lub_def],
      apply def_set.and,
      { apply def_set.forall,
        apply def_set.imp,
        { apply def_set.forall,
          apply def_set.imp,
          { exact definable_lt def_fun.snd (def_fun.snd.comp def_fun.fst) },
          { refine def_fun.preimage _ ds,
            refine def_fun.prod' _ def_fun.snd,
            exact def_fun.snd.comp (def_fun.fst.comp (def_fun.fst.comp def_fun.fst)) } },
        { exact definable_le def_fun.snd (def_fun.snd.comp def_fun.fst) } },
      { apply def_set.forall,
        apply def_set.imp,
        { apply def_set.forall,
          apply def_set.imp,
          { apply def_set.forall,
            apply def_set.imp,
            { exact definable_lt def_fun.snd (def_fun.snd.comp def_fun.fst) },
            { refine def_fun.preimage _ ds,
              refine def_fun.prod' _ def_fun.snd,
              exact def_fun.snd.comp (def_fun.fst.comp (def_fun.fst.comp (def_fun.fst.comp def_fun.fst))) } },
          { exact definable_le def_fun.snd (def_fun.snd.comp def_fun.fst) } },
        { exact definable_le (def_fun.snd.comp def_fun.fst) def_fun.snd } } },
    { constructor, introsI K _ _ s ds,
      -- TODO: definable.sub
      simp only [sub_eq_add_neg],
      exact def_set_eq (definable.add (def_fun.snd.comp (def_fun.fst.comp def_fun.fst)) def_fun_const) def_fun.snd } },
  { constructor, introsI K _ _ s ds,
    exact def_set_eq def_fun_const def_fun.snd }
end

-- STILL TO DO:
-- * Prove that, when `X` is tame and nonempty, `chosen_one X` is an element of `X`.
-- Hopefully it's not too hard to reason about what `chosen_one` will produce;
-- but it still requires understanding the local behavior of tame sets.
