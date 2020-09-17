import .def_coords

universe u

namespace o_minimal

open_locale finvec

variables {R : Type u} (S : struc R)

-- We set up a minimal theory of (literal) definable subsets of Rⁿ
-- and definable functions between them.

/-- A bundled definable subset of some Rⁿ. -/
structure Def : Type u :=
(ambdim : ℕ)
(to_set : set (finvec ambdim R))
(is_definable : S.definable to_set)

variables {S}

instance : has_coe_to_sort (Def S) :=
⟨Type u, λ X, X.to_set⟩

lemma Def.is_def_coords (X : Def S) : S.def_coords (set.univ : set X) :=
begin
  unfold struc.def_coords,
  convert X.is_definable,
  simp
end

variables (S)

def struc.definable_fun {X Y : Def S} (f : X → Y) : Prop :=
S.def_coords {z : X × Y | f z.1 = z.2}

variables {S}

@[ext] structure Hom (X Y : Def S) : Type u :=
(to_fun : X → Y)
(is_definable : S.definable_fun to_fun)

instance {X Y : Def S} : has_coe_to_fun (Hom X Y) :=
⟨_, λ f, f.to_fun⟩

--instance : category_theory.has_hom (Def S) := { hom := Hom }
local infixr ` ⟶ `:10 := Hom

@[simp] lemma Hom.to_fun_eq_coe {X Y : Def S} (f : X ⟶ Y) :
  f.to_fun = f :=
rfl

-- TODO float out proofs of definability of identity, composition
-- (useful later in presheaf stuff, notably representable instance)

def Def.id (X : Def S) : X ⟶ X :=
{ to_fun := id,
  is_definable := struc.def_coords.diag X.is_def_coords }

def Hom.comp {X Y Z : Def S} (g : Y ⟶ Z) (f : X ⟶ Y) : X ⟶ Z :=
{ to_fun := g.to_fun ∘ f.to_fun,
  is_definable := begin
    suffices : S.def_coords {p : X × Z | ∃ y, f p.1 = y ∧ g y = p.2},
    { convert this,
      ext ⟨x, z⟩,
      simp [struc.definable_fun] },
    have dXZY : S.def_coords (set.univ : set ((X × Z) × Y)) :=
      (X.is_def_coords.prod_univ Z.is_def_coords).prod_univ Y.is_def_coords,
    apply struc.def_coords.exists,
    apply struc.def_coords.inter,
    { let φ : (X × Z) × Y → X × Y := λ p, (p.1.1, p.2),
      have : is_reindexing R φ :=
        is_reindexing.prod R ((is_reindexing.fst R).comp R (is_reindexing.fst R)) (is_reindexing.snd R),
      refine struc.def_coords.reindex dXZY this f.is_definable },
    { let φ : (X × Z) × Y → Y × Z := λ p, (p.2, p.1.2),
      have : is_reindexing R φ :=
        is_reindexing.prod R (is_reindexing.snd R) ((is_reindexing.snd R).comp R (is_reindexing.fst R)),
      refine struc.def_coords.reindex dXZY this g.is_definable },
  end }

lemma Hom.comp_id {X Y : Def S} (f : X ⟶ Y) : f.comp (Def.id X) = f :=
by { ext, refl }

lemma Hom.id_comp {X Y : Def S} (f : X ⟶ Y) : (Def.id Y).comp f = f :=
by { ext, refl }

lemma Hom.comp_assoc {W X Y Z : Def S} (h : Y ⟶ Z) (g : X ⟶ Y) (f : W ⟶ X) :
  (h.comp g).comp f = h.comp (g.comp f) :=
rfl

def pt : Def S :=
{ ambdim := 0,
  to_set := set.univ,
  is_definable := S.definable_univ 0 }

/-! ### Presheaf stuff -/

variables (S)

class definable_psh (X : Type*) :=
(definable : Π {K : Def S}, (K → X) → Prop)
(definable_precomp : ∀ {L K : Def S} (φ : L ⟶ K) {f : K → X},
  definable f → definable (f ∘ φ))

def definable {X : Type*} [definable_psh S X] (x : X) : Prop :=
definable_psh.definable (λ (_ : (pt : Def S)), x)

variables {S}

def definable_psh.definable' {X : Type*} (h : definable_psh S X) {K : Def S} (f : K → X) : Prop :=
definable_psh.definable f

instance Def.definable_psh (X : Def S) : definable_psh S X :=
{ definable := λ K f, S.definable_fun f,
  definable_precomp := begin
    rintros L K φ f h,
    exact ((⟨f, h⟩ : K ⟶ X).comp φ).is_definable
  end }

instance {X Y : Type*} [definable_psh S X] [definable_psh S Y] : definable_psh S (X × Y) :=
{ definable := λ K f, definable_psh.definable (prod.fst ∘ f) ∧ definable_psh.definable (prod.snd ∘ f),
  definable_precomp := begin
    rintros L K φ _ ⟨h₁, h₂⟩,
    exact ⟨definable_psh.definable_precomp φ h₁, definable_psh.definable_precomp φ h₂⟩,
  end }

instance function.definable_psh {X Y : Type*} [hX : definable_psh S X] [hY : definable_psh S Y] :
  definable_psh S (X → Y) :=
{ definable := λ K f, ∀ (M : Def S) {g : M → K × X} (h : definable_psh.definable g),
    definable_psh.definable (function.uncurry f ∘ g),
  definable_precomp := λ L K φ f hf M g hg, begin
    suffices : definable_psh.definable (λ m, (φ (g m).1, (g m).2)),
    { apply hf M this },
    split,
    { exact definable_psh.definable_precomp ⟨λ m, (g m).1, hg.1⟩
        (show definable_psh.definable φ, from φ.is_definable) },
    { exact hg.2 }
  end }

lemma definable_fun {X Y : Type*} [definable_psh S X] [definable_psh S Y]
  {f : X → Y} : definable S f ↔
  ∀ {K : Def S} (φ : K → X), definable_psh.definable φ → definable_psh.definable (f ∘ φ) :=
sorry                           -- somehow have to use K × * ≃ K

lemma definable_app {X Y : Type*} [definable_psh S X] [definable_psh S Y]
  {f : X → Y} (hf : definable S f) {x : X} (hx : definable S x) : definable S (f x) :=
begin
  rw definable_fun at hf,
  exact hf _ hx
end

lemma definable_prod_mk {X Y : Type*} [definable_psh S X] [definable_psh S Y] :
  definable S (prod.mk : X → Y → X × Y) :=
-- I have no idea how to come up with these proofs.
-- Maybe we should tweak the type of definable_precomp (or write a lemma)
-- that takes the underlying map φ and its proof of definability separately
-- so that Lean has a better chance of guessing what's happening?
λ L g h L' g' h',
⟨definable_psh.definable_precomp ⟨λ x, (g' x).fst, h'.1⟩ h.2, h'.2⟩

variables (S)

/- TODO:
* instance definable_psh S Prop
* class represented [has_coordinates R X] expressing compatibility
* prove this notion of definability of functions, sets reduces
  to the original one in the represented case
* prove definability of basic constants (like `∩`)
Then:
* prove stuff like `is_least : set R → R → Prop` is definable
-/

end o_minimal
