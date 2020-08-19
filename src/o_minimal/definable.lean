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
A bundled *definable type*, with respect to a given structure S on R:
this is a type that has coordinates valued in R
which, as a subset of Rⁿ, is definable according to S.
-/
structure Def : Type (u+1) :=
(carrier : Type u)
[coords : has_coordinates R carrier]
(definable : S.definable (coordinate_image R carrier))

instance : has_coe_to_sort (Def S) := ⟨_, Def.carrier⟩

attribute [instance] Def.coords

variables {S}

-- TODO: Naming?
def coord {X : Def S} : X → fin X.coords.ambdim → R :=
@coords R X.carrier X.coords

lemma range_coord {X : Def S} : range (@coord R S X) = coordinate_image R X :=
rfl

@[simps] def Def.prod (X Y : Def S) : Def S :=
{ carrier := X.carrier × Y.carrier,
  definable := begin
    rw coordinate_image_prod,
    exact S.definable_external_prod X.definable Y.definable
  end }

@[simp] lemma Def.prod.coord_left {X Y : Def S} (p : X.prod Y) :
  finvec.left (coord p) = coord p.1 :=
by apply finvec.append_left

@[simp] lemma Def.prod.coord_right {X Y : Def S} (p : X.prod Y) :
  finvec.right (coord p) = coord p.2 :=
by apply finvec.append_right

section definable_set
/-
We first discuss what it means for 
a subset `s : set X` to be definable when `X : Def S`. -/

variables {X Y : Def S}

def def_set (s : set X) : Prop := S.definable (coord '' s)

variable (X)

lemma def_set_empty : def_set (∅ : set X) :=
begin
  convert S.definable_empty _,
  simp [def_set]
end

lemma def_set_univ : def_set (set.univ : set X) :=
begin
  simpa [def_set] using X.definable
end

variable {X}

lemma def_set.inter {s t : set X} (hs : def_set s) (ht : def_set t) :
  def_set (s ∩ t) :=
begin
  convert S.definable_inter hs ht,
  have : function.injective (@coord R S X) := X.coords.inj,
  simp [def_set, image_inter this]
end

lemma def_set.union {s t : set X} (hs : def_set s) (ht : def_set t) :
  def_set (s ∪ t) :=
begin
  convert S.definable_union hs ht,
  simp [def_set, image_union (@coord R S X)]
end

lemma def_set.diff {s t : set X} (hs : def_set s) (ht : def_set t) :
  def_set (s \ t) :=
begin
  convert S.definable_diff hs ht,
  have : function.injective (@coord R S X) := X.coords.inj,
  simp [def_set, image_diff this],
end

lemma def_set.compl {s : set X} (hs : def_set s) :
  def_set (sᶜ) :=
by { rw compl_eq_univ_diff, exact (def_set_univ _).diff hs }

-- TODO:
-- finite intersections, unions

lemma def_set.or {s t : X → Prop} (hs : def_set {x : X | s x}) (ht : def_set {x : X | t x}) :
  def_set {x | s x ∨ t x} :=
hs.union ht

lemma def_set.and {s t : X → Prop} (hs : def_set {x : X | s x}) (ht : def_set {x : X | t x}) :
  def_set {x | s x ∧ t x} :=
hs.inter ht

lemma def_set.not {s : X → Prop} (hs : def_set {x : X | s x}) :
  def_set {x | ¬ s x} :=
hs.compl

lemma def_set.imp {s t : X → Prop} (hs : def_set {x : X | s x}) (ht : def_set {x : X | t x}) :
  def_set {x | s x → t x} :=
begin
  simp [classical.imp_iff_not_or], -- classical!
  exact hs.not.or ht
end

lemma def_set.proj {s : set (X.prod Y)} (hs : def_set s) : def_set (prod.fst '' s) :=
begin
  unfold def_set,
  convert S.definable_proj hs using 1,
  ext z,
  simp, dsimp, simp, refl
end

lemma def_set.exists {s : X → Y → Prop} (hs : def_set {p : X.prod Y | s p.1 p.2}) :
  def_set {x | ∃ y, s x y} :=
begin
  convert def_set.proj hs,
  ext, simp, finish
end

lemma def_set.forall {s : X → Y → Prop} (hs : def_set {p : X.prod Y | s p.1 p.2}) :
  def_set {x | ∀ y, s x y} :=
begin
  -- classical!!
  have : ∀ (s : X → Y → Prop) (hs : def_set {p : X.prod Y | s p.1 p.2}),
    def_set {x | ∀ y, ¬ s x y},
  { intros t ht, simpa using ht.exists.not },
  simpa using this (λ x y, ¬ s x y) hs.not,
end

lemma def_set.reindex {X Y : Def S} {f : X → Y} (hf : is_reindexing R f)
  {s : set Y} (hs : def_set s) : def_set (f ⁻¹' s) :=
begin
  cases hf with fσ hf,
  unfold def_set,
  -- The preimage f ⁻¹' s, as a subset of the Rⁿ in which X lives,
  -- is the intersection of X with the preimage of s under the reindexing.
  convert S.definable_inter X.definable (S.definable_reindex fσ hs),
  ext z,
  suffices : (∃ (x : X), f x ∈ s ∧ coord x = z) ↔
    z ∈ range (@coord R S X) ∧ ∃ (y : Y), y ∈ s ∧ coord y = z ∘ fσ,
  { simpa },
  -- TODO: funext'd version of `is_reindexing.hf`
  replace hf : ∀ (x : X), coord x ∘ fσ = coord (f x) := λ x, funext (λ i, (hf x i)),
  split,
  { rintro ⟨x, hfx, rfl⟩,
    refine ⟨mem_range_self _, f x, hfx, (hf x).symm⟩ },
  { rintro ⟨⟨x, rfl⟩, y, hy, H⟩,
    rw hf x at H,
    replace hf := injective_coords H,
    subst y,
    exact ⟨x, hy, rfl⟩ }
end

lemma def_set_diag {X : Def S} : def_set {p : X.prod X | p.1 = p.2} :=
begin
  unfold def_set,
  -- The image of the diagonal of X in Rⁿ × Rⁿ
  -- is the diagonal of Rⁿ intersected with X × X.
  convert S.definable_inter
    (S.definable_external_prod X.definable X.definable)
    S.definable_diag_rn,
  ext z,
  rw [mem_inter_iff, finvec.external_prod_def],
  change _ ↔ _ ∧ finvec.left z = finvec.right z,
  split,
  { rintro ⟨⟨x, y⟩, h, rfl⟩,
    change x = y at h,
    simp [coordinate_image, coord, h] },
  { rintro ⟨⟨hz₁, _⟩, hz₂⟩,
    rcases hz₁ with ⟨x, hx⟩,
    refine ⟨⟨x, x⟩, rfl, _⟩,
    convert finvec.append_left_right _,
    refine finvec.append.inj_iff.mpr _,
    simp [hx, hz₂] }
end

lemma def_set.prod_univ {X Y : Def S} {s : set X} (hs : def_set s) :
  def_set {p : X.prod Y | p.1 ∈ s} :=
def_set.reindex (is_reindexing.fst R) hs

lemma def_set.univ_prod {X Y : Def S} {t : set Y} (ht : def_set t) :
  def_set {p : X.prod Y | p.2 ∈ t} :=
def_set.reindex (is_reindexing.snd R) ht

lemma def_set.prod {X Y : Def S} {s : set X} (hs : def_set s) {t : set Y} (ht : def_set t) :
  def_set (show set (X.prod Y), from s.prod t) :=
hs.prod_univ.inter ht.univ_prod

end definable_set

section definable_fun
-- Now we introduce definable functions between definable types.
-- They are the functions whose graphs are definable sets.

variables {X Y Z : Def S}

/-- A function f : X → Y is definable if its graph is a definable set. -/
def def_fun (f : X → Y) : Prop := def_set {p : X.prod Y | f p.1 = p.2}

lemma def_fun.id (X : Def S) : def_fun (id : X → X) :=
def_set_diag

lemma def_fun.comp {g : Y → Z} (hg : def_fun g) {f : X → Y} (hf : def_fun f) :
  def_fun (g ∘ f) :=
begin
  suffices : def_set {p : X.prod Z | ∃ y, f p.1 = y ∧ g y = p.2},
  { unfold def_fun,
    convert this,
    ext ⟨x, z⟩,
    simp },
  apply def_set.exists,
  apply def_set.and,
  -- TODO: Minor annoyance: can't just write (a, b) to construct ↥(X.prod Y).
  { have : is_reindexing R (λ p : (X.prod Z).prod Y, show X.prod Y, from (p.1.1, p.2)),
    { apply_rules [is_reindexing.prod, is_reindexing.fst, is_reindexing.snd, is_reindexing.comp] },
    exact def_set.reindex this hf },
  { have : is_reindexing R (λ p : (X.prod Z).prod Y, show Y.prod Z, from (p.2, p.1.2)),
    { apply_rules [is_reindexing.prod, is_reindexing.fst, is_reindexing.snd, is_reindexing.comp] },
    exact def_set.reindex this hg }
end

lemma is_reindexing.def_fun {f : X → Y} (hf : is_reindexing R f) :
  def_fun f :=
begin
  cases hf with fσ hf,
  unfold def_fun,
  unfold def_set,
  convert S.definable_inter (S.definable_prod_rn X.definable) (S.definable_reindex_aux fσ (def_set_univ Y)),
  ext z,
  split,
  { rintro ⟨⟨x, y⟩, h, rfl⟩,
    change f x = y at h, subst y,
    show _ ∧ _ ∧ _,
    simp only [Def.prod.coord_left, mem_range_self, and_true, image_univ, Def.prod.coord_right],
    refine ⟨⟨⟨x, _⟩, ⟨⟩⟩, _⟩,
    { simp only [Def.prod.coord_left], refl },
    { ext i,
      apply hf, }, },
  { rintro ⟨⟨⟨x, hx⟩, ⟨⟩⟩, ⟨hz, ⟨y, ⟨⟩, hy⟩⟩⟩,
    simp only [mem_image, mem_set_of_eq],
    use [(x,y)],
    split,
    { apply @injective_coords R,
      ext i,
      show coords R (f x) i = coords R y i,
      rw ← hf,
      rw [← hx, ← hy] at hz,
      exact congr_fun hz i },
    { -- we need simp lemmas that relate coords and coord
      show finvec.append (coords R x) (coord y) = _,
      simp [hx, hy], } }
end

lemma def_fun.preimage {f : X → Y} (hf : def_fun f) {s : set Y} (hs : def_set s) :
  def_set (f ⁻¹' s) :=
begin
  -- f ⁻¹' s = {x | ∃ (p : X × Y), p.1 = x ∧ p ∈ Γ(f)}
  convert def_set.proj (hf.inter ((def_set_univ _).prod hs)) using 1,
  ext,
  suffices : f x ∈ s ↔ ∃ y, f x = y ∧ y ∈ s, { simpa },
  finish
end

lemma def_fun.fst :
  def_fun (show (X.prod Y) → X, from prod.fst) :=
begin
  apply is_reindexing.def_fun,
  exact (is_reindexing.fst R)
end

lemma def_fun.snd :
  def_fun (show (X.prod Y) → Y, from prod.snd) :=
begin
  apply is_reindexing.def_fun,
  exact (is_reindexing.snd R)
end

lemma def_fun.prod' {f : X → Y} {g : X → Z} (hf : def_fun f) (hg : def_fun g) :
  def_fun (show X → (Y.prod Z), from λ x, (f x, g x)) :=
begin
  unfold def_fun,
  let p1 : X.prod (Y.prod Z) → X.prod Y := λ p, (p.1, p.2.1),
  have hp1 : def_fun p1,
  { apply is_reindexing.def_fun,
    apply (is_reindexing.fst R).prod R
      ((is_reindexing.fst R).comp R (is_reindexing.snd R)) },
  let p2 : X.prod (Y.prod Z) → X.prod Z := λ p, (p.1, p.2.2),
  have hp2 : def_fun p2,
  { apply is_reindexing.def_fun,
    apply (is_reindexing.fst R).prod R
      ((is_reindexing.snd R).comp R (is_reindexing.snd R)) },
  convert (hp1.preimage hf).inter (hp2.preimage hg),
  ext ⟨x,y,z⟩,
  show (f x, g x) = (y,z) ↔ _,
  simp only [mem_inter_eq, prod.mk.inj_iff, mem_set_of_eq, preimage_set_of_eq],
end

lemma def_fun.prod {W : Def S} {f : X → Z} {g : Y → W} (hf : def_fun f) (hg : def_fun g) :
  def_fun (show (X.prod Y) → (Z.prod W), from prod.map f g) :=
(hf.comp def_fun.fst).prod' (hg.comp def_fun.snd)

lemma def_set_eq {X Y : Def S} {f g : X → Y} (hf : def_fun f) (hg : def_fun g) :
  def_set {x | f x = g x} :=
(hf.prod' hg).preimage (def_set_diag)

lemma def_fun.image {X Y : Def S} {f : X → Y} (hf : def_fun f) {s : set X} (hs : def_set s) :
  def_set (f '' s) :=
begin
  show def_set {y | ∃ x, x ∈ s ∧ f x = y},
  apply def_set.exists,
  apply (def_fun.preimage def_fun.snd hs).and
    (def_set_eq (hf.comp def_fun.snd) (def_fun.fst)),
end


end definable_fun

end o_minimal
