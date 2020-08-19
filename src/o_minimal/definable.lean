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

lemma def_set_empty : def_set (∅ : set X) :=
begin
  convert S.definable_empty _,
  simp [def_set]
end

lemma def_set_univ : def_set (set.univ : set X) :=
begin
  simpa [def_set] using X.definable
end

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
by { rw compl_eq_univ_diff, exact (def_set_univ).diff hs }

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

lemma def_set.exists {s : X → Y → Prop} (hs : def_set {p : X.prod Y | s p.1 p.2}) :
  def_set {x | ∃ y, s x y} :=
begin
  unfold def_set,
  convert S.definable_proj hs using 1,
  ext z,
  simp, dsimp, simp, refl
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

lemma def_set_eq {X : Def S} : def_set {p : X.prod X | p.1 = p.2} :=
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

end definable_set

section definable_fun
-- Now we introduce definable functions between definable types.
-- They are the functions whose graphs are definable sets.

variables {X Y Z : Def S}

/-- A function f : X → Y is definable if its graph is a definable set. -/
def def_fun (f : X → Y) : Prop := def_set {p : X.prod Y | f p.1 = p.2}

lemma def_fun.id (X : Def S) : def_fun (id : X → X) :=
def_set_eq

lemma def_fun.comp {g : Y → Z} (hg : def_fun g) {f : X → Y} (hf : def_fun f) :
  def_fun (g ∘ f) :=
begin
  suffices : def_set {p : X.prod Z | ∃ y, f p.1 = y ∧ g y = p.2},
  { unfold def_fun,
    convert this,
    ext ⟨x, z⟩,
    simp },
  apply def_set.exists,
  apply def_set.inter,
  -- TODO: Minor annoyance: can't just write (a, b) to construct ↥(X.prod Y).
  { have : is_reindexing R (λ p : (X.prod Z).prod Y, show X.prod Y, from (p.1.1, p.2)),
    { apply_rules [is_reindexing.prod, is_reindexing.fst, is_reindexing.snd, is_reindexing.comp] },
    exact def_set.reindex this hf },
  { have : is_reindexing R (λ p : (X.prod Z).prod Y, show Y.prod Z, from (p.2, p.1.2)),
    { apply_rules [is_reindexing.prod, is_reindexing.fst, is_reindexing.snd, is_reindexing.comp] },
    exact def_set.reindex this hg }
end

end definable_fun

end o_minimal
