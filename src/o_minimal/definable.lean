import category_theory.category
import o_minimal.structure
import o_minimal.coordinates

universe u

namespace o_minimal

open set

-- Carrier for the (o-minimal) structure.
variables {R : Type u}

-- A structure on `R`.
variables (S : struc R)

/--
A type with coordinates valued in R is *definable* with respect to a given structure S on R
if the corresponding subset of Rⁿ is definable according to S.
-/
class is_definable (X : Type*) [has_coordinates R X] : Prop :=
(is_definable [] : S.definable (coordinate_image R X))

instance is_definable.self : is_definable S R :=
begin
  constructor,
  convert S.definable_univ 1,
  ext,
  simp [coordinate_image],
  use (x 0),
  ext i,
  have : i = 0 := by cc,
  subst i
end

-- TODO: Generalize to [is_definable S X] : is_definable S (finvec n X)
instance is_definable.rn {n : ℕ} : is_definable S (finvec n R) :=
begin
  constructor,
  convert S.definable_univ n,
  ext,
  simp [coordinate_image]
end

variables {X : Type*} [has_coordinates R X] [is_definable S X]
variables {Y : Type*} [has_coordinates R Y] [is_definable S Y]
variables {Z : Type*} [has_coordinates R Z] [is_definable S Z]
variables {W : Type*} [has_coordinates R W] [is_definable S W]

instance is_definable.prod : is_definable S (X × Y) :=
begin
  constructor,
  rw coordinate_image_prod,
  exact S.definable_external_prod (is_definable.is_definable S X) (is_definable.is_definable S Y)
end

-- TODO: instances matching the rest of has_coordinates

section definable_set
/-
We first discuss what it means for 
a subset `s : set X` to be definable
when `X` is a definable type. -/

def def_set (s : set X) : Prop := S.definable (coords R '' s)

variables {S}

/-- The subtype of a definable type determined by a definable set is definable.
Unfortunately, this can't be a global instance because of the hypothesis `hs`. -/
def is_definable.subtype {s : set X} (hs : def_set S s) : is_definable S s :=
{ is_definable := begin
    unfold def_set at hs,
    convert hs,
    ext x,
    simp [coordinate_image]
  end }

variables (X)

lemma def_set_empty : def_set S (∅ : set X) :=
begin
  convert S.definable_empty _,
  simp [def_set]
end

lemma def_set_univ : def_set S (set.univ : set X) :=
by simpa [def_set] using is_definable.is_definable S X

variable {X}

lemma def_set.inter {s t : set X} (hs : def_set S s) (ht : def_set S t) :
  def_set S (s ∩ t) :=
begin
  convert S.definable_inter hs ht,
  simp [def_set, image_inter (injective_coords X)]
end

lemma def_set.union {s t : set X} (hs : def_set S s) (ht : def_set S t) :
  def_set S (s ∪ t) :=
begin
  convert S.definable_union hs ht,
  simp [def_set, image_union]
end

lemma def_set.diff {s t : set X} (hs : def_set S s) (ht : def_set S t) :
  def_set S (s \ t) :=
begin
  convert S.definable_diff hs ht,
  simp [def_set, image_diff (injective_coords X)],
end

lemma def_set.compl {s : set X} (hs : def_set S s) : def_set S (sᶜ) :=
by { rw compl_eq_univ_diff, exact (def_set_univ _).diff hs }

lemma def_set.compl' {s : set X} (hs : def_set S sᶜ) : def_set S s :=
by { rw ←compl_compl s, exact hs.compl }

lemma def_set.iff {s t : set X} (hs : def_set S s) (ht : def_set S t) :
  def_set S {x : X | x ∈ s ↔ x ∈ t} :=
begin
  simp only [iff_iff_and_or_not_and_not],
  exact (hs.inter ht).union (hs.compl.inter ht.compl)
end

lemma def_set_Inter {ι : Type*} [fintype ι] {t : ι → set X}
  (ht : ∀ i, def_set S (t i)) : def_set S (⋂ i, t i) :=
suffices ∀ {s : set ι}, set.finite s → def_set S (⋂ i ∈ s, t i),
by { convert this finite_univ, simp },
λ s hs, finite.induction_on hs
  (by { convert def_set_univ _, simp, apply_instance }) -- why is apply_instance needed here?
  (λ i s _ _ IH, by { convert (ht i).inter IH, simp })

lemma def_set_Union {ι : Type*} [fintype ι] {t : ι → set X}
  (ht : ∀ i, def_set S (t i)) : def_set S (⋃ i, t i) :=
begin
  apply def_set.compl',
  rw compl_Union,
  exact def_set_Inter (λ i, (ht i).compl)
end

lemma def_set.or {s t : X → Prop} (hs : def_set S {x : X | s x}) (ht : def_set S {x : X | t x}) :
  def_set S {x | s x ∨ t x} :=
hs.union ht

lemma def_set.and {s t : X → Prop} (hs : def_set S {x : X | s x}) (ht : def_set S {x : X | t x}) :
  def_set S {x | s x ∧ t x} :=
hs.inter ht

lemma def_set.not {s : X → Prop} (hs : def_set S {x : X | s x}) :
  def_set S {x | ¬ s x} :=
hs.compl

lemma def_set.imp {s t : X → Prop} (hs : def_set S {x : X | s x}) (ht : def_set S {x : X | t x}) :
  def_set S {x | s x → t x} :=
begin
  simp [imp_iff_not_or], -- classical!
  exact hs.not.or ht
end

lemma def_set.forall_fintype {ι : Type*} [fintype ι] {t : ι → set X}
  (ht : ∀ i, def_set S (t i)) : def_set S {x | ∀ i, x ∈ t i} :=
begin
  convert def_set_Inter ht using 1,
  ext x,
  simp
end

lemma def_set.exists_fintype {ι : Type*} [fintype ι] {t : ι → set X}
  (ht : ∀ i, def_set S (t i)) : def_set S {x | ∃ i, x ∈ t i} :=
begin
  convert def_set_Union ht using 1,
  ext x,
  simp
end

lemma def_set.proj {s : set (X × Y)} (hs : def_set S s) : def_set S (prod.fst '' s) :=
begin
  unfold def_set,
  convert S.definable_proj hs using 1,
  ext z,
  rw [image_image, image_image],
  simp only [has_coordinates.prod_coords, finvec.left_append]
end

-- Is it better to use `{p : Y × X | s p.2 p.1}`?
-- After all, Lean prefers to form `Z × Y × X = Z × (Y × X)`
lemma def_set.exists {s : X → Y → Prop} (hs : def_set S {p : X × Y | s p.1 p.2}) :
  def_set S {x | ∃ y, s x y} :=
begin
  convert def_set.proj hs,
  ext, simp
end

lemma def_set.forall {s : X → Y → Prop} (hs : def_set S {p : X × Y | s p.1 p.2}) :
  def_set S {x | ∀ y, s x y} :=
begin
  -- classical!!
  have : ∀ (s : X → Y → Prop) (hs : def_set S {p : X × Y | s p.1 p.2}),
    def_set S {x | ∀ y, ¬ s x y},
  { intros t ht, simpa using ht.exists.not },
  simpa using this (λ x y, ¬ s x y) hs.not,
end

lemma def_set.reindex {f : X → Y} (hf : is_reindexing R f)
  {s : set Y} (hs : def_set S s) : def_set S (f ⁻¹' s) :=
begin
  cases hf with fσ hf,
  unfold def_set,
  -- The preimage f ⁻¹' s, as a subset of the Rⁿ in which X lives,
  -- is the intersection of X with the preimage of s under the reindexing.
  convert S.definable_inter (is_definable.is_definable S X) (S.definable_reindex fσ hs),
  ext z,
  suffices : (∃ (x : X), f x ∈ s ∧ coords R x = z) ↔
    z ∈ range (coords R) ∧ ∃ (y : Y), y ∈ s ∧ coords R y = z ∘ fσ,
  { simpa },
  -- TODO: funext'd version of `is_reindexing.hf`
  replace hf : ∀ (x : X), coords R x ∘ fσ = coords R (f x) := λ x, funext (λ i, (hf x i)),
  split,
  { rintro ⟨x, hfx, rfl⟩,
    refine ⟨mem_range_self _, f x, hfx, (hf x).symm⟩ },
  { rintro ⟨⟨x, rfl⟩, y, hy, H⟩,
    rw hf x at H,
    replace hf := injective_coords _ H,
    subst y,
    exact ⟨x, hy, rfl⟩ }
end

lemma def_set_diag : def_set S {p : X × X | p.1 = p.2} :=
begin
  unfold def_set,
  -- The image of the diagonal of X in Rⁿ × Rⁿ
  -- is the diagonal of Rⁿ intersected with X × X.
  convert S.definable_inter
    (S.definable_external_prod (is_definable.is_definable S X) (is_definable.is_definable S X))
    S.definable_diag_rn,
  ext z,
  rw [mem_inter_iff, finvec.mem_prod_iff],
  change _ ↔ _ ∧ finvec.left z = finvec.right z,
  split,
  { rintro ⟨⟨x, y⟩, h, rfl⟩,
    change x = y at h,
    simp [coordinate_image, h] },
  { rintro ⟨⟨hz₁, _⟩, hz₂⟩,
    rcases hz₁ with ⟨x, hx⟩,
    refine ⟨⟨x, x⟩, rfl, _⟩,
    convert finvec.left_append_right _,
    refine finvec.append.inj_iff.mpr _,
    simp [hx, hz₂] }
end

lemma def_set.prod_univ {s : set X} (hs : def_set S s) :
  def_set S {p : X × Y | p.1 ∈ s} :=
def_set.reindex is_reindexing.fst hs

lemma def_set.univ_prod {t : set Y} (ht : def_set S t) :
  def_set S {p : X × Y | p.2 ∈ t} :=
def_set.reindex is_reindexing.snd ht

lemma def_set.prod {s : set X} (hs : def_set S s) {t : set Y} (ht : def_set S t) :
  def_set S (s.prod t) :=
hs.prod_univ.inter ht.univ_prod

end definable_set

section definable_fun
-- Now we introduce definable functions between definable types.
-- They are the functions whose graphs are definable sets.

/-- A function f : X → Y is definable if its graph is a definable set. -/
def def_fun (f : X → Y) : Prop := def_set S {p : X × Y | f p.1 = p.2}

variables {S}

lemma def_fun.id : def_fun S (id : X → X) :=
def_set_diag

lemma def_fun.comp {g : Y → Z} (hg : def_fun S g) {f : X → Y} (hf : def_fun S f) :
  def_fun S (g ∘ f) :=
begin
  suffices : def_set S {p : X × Z | ∃ y, f p.1 = y ∧ g y = p.2},
  { unfold def_fun,
    convert this,
    ext ⟨x, z⟩,
    simp },
  apply def_set.exists,
  apply def_set.and,
  { have : is_reindexing R (λ p : (X × Z) × Y, (p.1.1, p.2)),
    { apply_rules [is_reindexing.prod, is_reindexing.fst, is_reindexing.snd, is_reindexing.comp] },
    exact def_set.reindex this hf },
  { have : is_reindexing R (λ p : (X × Z) × Y, (p.2, p.1.2)),
    { apply_rules [is_reindexing.prod, is_reindexing.fst, is_reindexing.snd, is_reindexing.comp] },
    exact def_set.reindex this hg }
end

lemma is_reindexing.def_fun {f : X → Y} (hf : is_reindexing R f) :
  def_fun S f :=
begin
  cases hf with fσ hf,
  unfold def_fun,
  unfold def_set,
  convert S.definable_inter
    (S.definable_prod_rn (is_definable.is_definable S X))
    (S.definable_reindex_aux fσ (def_set_univ Y)),
  ext z,
  split,
  { rintro ⟨⟨x, y⟩, h, rfl⟩,
    change f x = y at h, subst y,
    show _ ∧ _ ∧ _,
    simp only [mem_range_self, and_true, image_univ, has_coordinates.prod_coords, finvec.left_append, finvec.right_append, finvec.append_mem_prod_univ_iff],
    refine ⟨⟨x, _⟩, _⟩,
    { simp },
    { ext i,
      apply hf, }, },
  { rintro ⟨⟨x, hx⟩, ⟨hz, ⟨y, ⟨⟩, hy⟩⟩⟩,
    simp only [mem_image, mem_set_of_eq],
    use [(x,y)],
    split,
    { apply @injective_coords R,
      ext i,
      show coords R (f x) i = coords R y i,
      rw ← hf,
      rw [← hx, ← hy] at hz,
      exact congr_fun hz i },
    { simp [hx, hy] } }
end

lemma def_fun.preimage {f : X → Y} (hf : def_fun S f) {s : set Y} (hs : def_set S s) :
  def_set S (f ⁻¹' s) :=
begin
  -- f ⁻¹' s = {x | ∃ (p : X × Y), p.1 = x ∧ p ∈ Γ(f)}
  convert def_set.proj (hf.inter ((def_set_univ _).prod hs)) using 1,
  ext, simp
end

lemma def_fun.coords : def_fun S (λ x : X, coords R x) :=
is_reindexing.def_fun is_reindexing.coords

lemma def_fun.coord (i : fin (has_coordinates.ambdim R X)) : def_fun S (λ x : X, coords R x i) :=
is_reindexing.def_fun (is_reindexing.coord i)

lemma def_fun.coord_rn {n : ℕ} (i : fin n) : def_fun S (λ x : finvec n R, x i) :=
def_fun.coord i

lemma def_fun.fst : def_fun S (prod.fst : X × Y → X) :=
is_reindexing.def_fun is_reindexing.fst

lemma def_fun.snd : def_fun S (prod.snd : X × Y → Y) :=
is_reindexing.def_fun is_reindexing.snd

lemma def_fun.prod' {f : X → Y} {g : X → Z} (hf : def_fun S f) (hg : def_fun S g) :
  def_fun S (λ x, (f x, g x)) :=
begin
  unfold def_fun,
  let p1 : X × (Y × Z) → X × Y := λ p, (p.1, p.2.1),
  have hp1 : def_fun S p1,
  { apply is_reindexing.def_fun,
    apply is_reindexing.fst.prod (is_reindexing.fst.comp is_reindexing.snd) },
  let p2 : X × (Y × Z) → X × Z := λ p, (p.1, p.2.2),
  have hp2 : def_fun S p2,
  { apply is_reindexing.def_fun,
    apply is_reindexing.fst.prod (is_reindexing.snd.comp is_reindexing.snd) },
  convert (hp1.preimage hf).inter (hp2.preimage hg),
  ext ⟨x,y,z⟩,
  show (f x, g x) = (y,z) ↔ _,
  simp only [mem_inter_eq, prod.mk.inj_iff, mem_set_of_eq, preimage_set_of_eq],
end

lemma def_fun.prod {f : X → Z} {g : Y → W} (hf : def_fun S f) (hg : def_fun S g) :
  def_fun S (prod.map f g) :=
(hf.comp def_fun.fst).prod' (hg.comp def_fun.snd)

lemma def_fun_subtype_val {s : set X} {hs : def_set S s} :
  by haveI := is_definable.subtype hs; exact
  def_fun S (subtype.val : s → X) :=
by haveI := is_definable.subtype hs; exact
is_reindexing.subtype.val.def_fun

lemma def_fun.finvec.left {n m : ℕ} : def_fun S (λ x : finvec (n+m) R, x.left) :=
is_reindexing.finvec.left.def_fun

lemma def_fun.finvec.right {n m : ℕ} : def_fun S (λ x : finvec (n+m) R, x.right) :=
is_reindexing.finvec.right.def_fun

lemma def_fun.finvec.init {n : ℕ} : def_fun S (λ x : finvec (n+1) R, x.init) :=
is_reindexing.finvec.init.def_fun

lemma def_fun.finvec.snoc' {n : ℕ} : def_fun S (λ p : finvec n R × R, p.1.snoc p.2) :=
is_reindexing.finvec.snoc.def_fun

lemma def_fun.finvec.snoc {n : ℕ} {f : X → finvec n R} (hf : def_fun S f) {g : X → R} (hg : def_fun S g) :
  def_fun S (λ x, (f x).snoc (g x)) :=
def_fun.finvec.snoc'.comp (hf.prod' hg)

lemma def_set_eq {f g : X → Y} (hf : def_fun S f) (hg : def_fun S g) :
  def_set S {x | f x = g x} :=
(hf.prod' hg).preimage def_set_diag

lemma def_fun.cancel {g : Y → Z} (dg : def_fun S g) (hg : function.injective g)
  {f : X → Y} (h : def_fun S (g ∘ f)) : def_fun S f :=
begin
  unfold def_fun,
  suffices : def_set S {p : X × Y | (g ∘ f) p.fst = g p.snd},
  { convert ←this,
    ext,
    apply hg.eq_iff },
  apply def_set_eq,
  { exact h.comp def_fun.fst },
  { exact dg.comp def_fun.snd }
end

lemma def_fun_subtype_mk {s : set X} {hs : def_set S s}
  {f : Y → X} (df : def_fun S f) (h : ∀ y, f y ∈ s) :
  by haveI := is_definable.subtype hs; exact
  def_fun S (λ y, (⟨f y, h y⟩ : s)) :=
by haveI := is_definable.subtype hs; exact
def_fun.cancel def_fun_subtype_val subtype.val_injective df

lemma def_fun_subtype_iff {s : set X} {ds : def_set S s} {f : Y → s} :
  by haveI := is_definable.subtype ds; exact
  def_fun S f ↔ def_fun S (subtype.val ∘ f) :=
by haveI := is_definable.subtype ds; exact
⟨λ h, def_fun_subtype_val.comp h, λ h, def_fun_subtype_val.cancel subtype.val_injective h⟩

lemma def_fun.image {f : X → Y} (hf : def_fun S f) {s : set X} (hs : def_set S s) :
  def_set S (f '' s) :=
show def_set S {y | ∃ x, x ∈ s ∧ f x = y}, from
def_set.exists $
  (def_fun.preimage def_fun.snd hs).and
  (def_set_eq (hf.comp def_fun.snd) (def_fun.fst))

lemma def_fun.range {f : X → Y} (hf : def_fun S f) : def_set S (range f) :=
by { rw ←image_univ, exact hf.image (def_set_univ _) }

end definable_fun

section definable_val
-- Finally, a "value" (element) of X is definable
-- if the corresponding singleton set is definable.
--
-- This notion is mostly used for bootstrapping
-- because in the o-minimal project we're only interested in
-- structures S on R in which every r ∈ R is definable,
-- which forces every value of every definable type to be definable.

/-- A value `x : X` is definable if `{x}` is definable. -/
def def_val (x : X) : Prop := def_set S ({x} : set X)

variables (S)

/-- A structure `S` on `R` has *definable constants*
if every `r : R` is definable. -/
class definable_constants : Prop :=
(definable_val : ∀ (r : R), def_val S r)

variables {S}

-- These primed lemmas take `def_val` arguments
-- and have unprimed variants which use a `definable_constants S` assumption.

lemma def_set_eq_const' {f : X → Y} (hf : def_fun S f) {y : Y} (hy : def_val S y) :
  def_set S {x | f x = y} :=
show def_set S (f ⁻¹' {y}), from
hf.preimage hy

lemma def_set_const_eq' {f : X → Y} (hf : def_fun S f) {y : Y} (hy : def_val S y) :
  def_set S {x | y = f x} :=
by { convert def_set_eq_const' hf hy, simp_rw [eq_comm] }

lemma def_fun_const' {y : Y} (hy : def_val S y) : def_fun S (λ (x : X), y) :=
def_set_const_eq' def_fun.snd hy

lemma def_val_const [definable_constants S] {x : X} : def_val S x :=
begin
  unfold def_val,
  have : {x} = ⋂ i, {x' : X | coords R x' i = coords R x i},
  { ext x',
    rw [mem_singleton_iff, mem_Inter],
    exact (@injective_coords R X _).eq_iff.symm.trans function.funext_iff },
  rw this,
  apply def_set_Inter,
  intro i,
  exact def_set_eq_const' (def_fun.coord i) (definable_constants.definable_val _)
end

lemma def_set_eq_const [definable_constants S] {f : X → Y} (hf : def_fun S f) (y : Y) :
  def_set S {x | f x = y} :=
def_set_eq_const' hf def_val_const

lemma def_set_const_eq [definable_constants S] {f : X → Y} (hf : def_fun S f) (y : Y) :
  def_set S {x | y = f x} :=
def_set_const_eq' hf def_val_const

lemma def_fun_const [definable_constants S] {y : Y} : def_fun S (λ (x : X), y) :=
def_fun_const' def_val_const

-- TODO: more lemmas as needed.

end definable_val

end o_minimal
