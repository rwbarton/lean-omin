import category_theory.concrete_category
import o_minimal.definable

/-
The category of (literal) definable subsets of Rⁿ
and definable functions between them (not just continuous ones).
Used as the index category for "definable sheaves".
-/

namespace o_minimal

universe u

variables {R : Type u} (S : struc R)

structure Def : Type u :=
(ambdim : ℕ)
(to_set : set (finvec ambdim R))
(is_definable : def_set S to_set)

variables {S}

instance : has_coe_to_sort (Def S) :=
⟨Type u, λ X, X.to_set⟩

instance is_definable.Def (K : Def S) : is_definable S K :=
is_definable.subtype K.is_definable

@[ext] structure Hom (X Y : Def S) : Type u :=
(to_fun : X → Y)
(is_definable : def_fun S to_fun)

instance {X Y : Def S} : has_coe_to_fun (Hom X Y) :=
⟨_, λ f, f.to_fun⟩

instance : category_theory.small_category (Def S) :=
{ hom := Hom,
  id := λ X, ⟨id, def_fun.id⟩,
  comp := λ X Y Z f g, ⟨g.1 ∘ f.1, g.2.comp f.2⟩ }

instance : category_theory.concrete_category.{u} (Def S) :=
{ forget := { obj := λ X, X, map := λ X Y f, f },
  forget_faithful := by tidy }

section pullback

variables {X Y Z : Def S} (f : X ⟶ Z) (g : Y ⟶ Z)

def Def.pullback : Def S :=
{ ambdim := X.ambdim + Y.ambdim,
  to_set :=
    {p | ∃ (hX : p.left ∈ X.to_set) (hY : p.right ∈ Y.to_set),
         f.to_fun ⟨p.left, hX⟩ = g.to_fun ⟨p.right, hY⟩},
  is_definable := begin
    -- TODO: This proof is bad; but how to fix it?
    have := def_set_eq (f.is_definable.comp def_fun.fst) (g.is_definable.comp def_fun.snd),
    change S.definable _ at this,
    change S.definable _,
    convert this using 1,
    ext u,
    revert u,
    refine finvec.rec (λ v w, _),
    simp only [has_coordinates.subtype_coords, set.mem_image,
      function.comp_app, has_coordinates.finvec_coords, set.mem_set_of_eq,
      set.image_id', has_coordinates.prod_coords, subtype.val_eq_coe, prod.exists],
    change (∃ (hX : (v.append w).left ∈ X.to_set) (hY : (v.append w).right ∈ Y.to_set), _) ↔ _,
    split; rintro ⟨x, y, H⟩,
    { exact ⟨⟨v, by simpa using x⟩, ⟨w, by simpa using y⟩, by simpa using H, rfl⟩ },
    { obtain ⟨H₁, H₂⟩ := H,
      obtain ⟨rfl, rfl⟩ := finvec.append.inj_iff.mp H₂, clear H₂,
      refine ⟨by simp, by simp, by simp [H₁]⟩ }
  end }

def Def.pullback.π₁ : Def.pullback f g ⟶ X :=
{ to_fun := λ p, ⟨p.val.left, p.property.fst⟩,
  is_definable := def_fun_subtype_mk (def_fun.finvec.left.comp def_fun_subtype_val) _ }

def Def.pullback.π₂ : Def.pullback f g ⟶ Y :=
{ to_fun := λ p, ⟨p.val.right, p.property.snd.fst⟩,
  is_definable := def_fun_subtype_mk (def_fun.finvec.right.comp def_fun_subtype_val) _ }

end pullback

/-- A (generating) covering family of a given object `K : Def S`.
By definition, it is a finite family of definable maps which is
jointly surjective. -/
structure Def.cover (K : Def S) :=
(n : ℕ)
(obj : fin n → Def S)
(map : Π i, obj i ⟶ K)
(jointly_surjective : ∀ k, ∃ i l, map i l = k)

lemma Def.set_subcanonical
  {K : Def S} (𝓛 : K.cover) (s : set K) (h : Π i, def_set S (𝓛.map i ⁻¹' s)) :
  def_set S s :=
begin
  have : ∀ i, def_set S (𝓛.map i '' (𝓛.map i ⁻¹' s)) :=
    λ i, (𝓛.map i).is_definable.image (h i),
  convert def_set_Union this,
  ext k,
  simp only [set.mem_Union, set.mem_image, set.mem_preimage],
  split; intro hk,
  { obtain ⟨i, l, rfl⟩ := 𝓛.jointly_surjective k,
    refine ⟨i, l, hk, rfl⟩ },
  { obtain ⟨i, l, hl, rfl⟩ := hk,
    exact hl }
end

lemma Def.subcanonical {Y : Type*} [has_coordinates R Y] [is_definable S Y]
  {K : Def S} (𝓛 : K.cover) (f : K → Y) (h : Π i, def_fun S (f ∘ 𝓛.map i)) :
  def_fun S f :=
begin
  unfold def_fun at ⊢ h,
  -- We could pull back the cover to K × Y and use the previous proof,
  -- but it seems easier to just repeat it
  have : ∀ i, def_set S ((λ (p : 𝓛.obj i × Y), (𝓛.map i p.1, p.2)) '' _) :=
    λ i, ((𝓛.map i).is_definable.prod def_fun.id).image (h i),
  convert def_set_Union this using 1,
  ext ⟨k, y⟩,
  simp only [set.mem_Union, set.mem_image, prod.mk.inj_iff, function.comp_app,
    set.mem_set_of_eq, exists_eq_left', prod.exists],
  split,
  { rintro rfl,
    obtain ⟨i, l, rfl⟩ := 𝓛.jointly_surjective k,
    refine ⟨i, l, rfl, rfl⟩ },
  { rintro ⟨i, l, hl, rfl⟩,
    rw hl }
end

def Def.cover.pullback {K : Def S} (𝓛 : K.cover) {K' : Def S} (φ : K' ⟶ K) : K'.cover :=
{ n := 𝓛.n,
  obj := λ i, Def.pullback φ (𝓛.map i),
  map := λ i, Def.pullback.π₁ φ (𝓛.map i),
  jointly_surjective := λ k',
    let ⟨i, l, h⟩ := 𝓛.jointly_surjective (φ k') in
    ⟨i, ⟨finvec.append k' l, by simp, by simp, by simpa using h.symm⟩,
     by { ext1, apply finvec.left_append }⟩ }

-- TODO: add lemmas for the properties of `Def.cover.pullback` that we actually use
-- (for example, we probably don't actually need it to be formed from pullbacks)

end o_minimal
