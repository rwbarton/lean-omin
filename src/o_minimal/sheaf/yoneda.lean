import o_minimal.sheaf.constants

namespace o_minimal

variables {R : Type*} {S : struc R}
variables {X : Type*} [definable_sheaf S X]
variables {X' : Type*} [definable_sheaf S X']
variables {X'' : Type*} [definable_sheaf S X'']
variables {L K : Def S}

lemma definable_fun {f : X → X'} :
  definable S f ↔
  ∀ (K : Def S) (φ : K → X), definable_sheaf.definable φ → definable_sheaf.definable (f ∘ φ) :=
begin
  -- TODO: Merge with following proof?
  split; intro H,
  { cases H,
    intros K φ hφ,
    exact H K K (λ k, (k, φ k)) ⟨def_fun.id, hφ⟩ },
  { refine ⟨λ M L φ hφ, _⟩,
    exact H _ _ hφ.2 }
end

lemma definable_yoneda {f : K → X} :
  definable S f ↔ definable_sheaf.definable f :=
begin
  split; intro H,
  { cases H,
    -- This proof is a bit mysterious, related to the perhaps
    -- odd definition of `definable S`.
    -- Really we could use any `Def S` as the first argument
    -- to `H`; `K` is just one we have handy here.
    exact H K K (λ k, (k, k)) ⟨def_fun.id, def_fun.id⟩ },
  { refine ⟨λ M L φ hφ, _⟩,
    exact definable_sheaf.definable_precomp ⟨_, hφ.2⟩ f H }
end

lemma Def.definable_iff_def_fun {f : L → K} : definable S f ↔ def_fun S f :=
definable_yoneda

lemma Def.definable_iff_def_set {s : set K} : definable S s ↔ def_set S s :=
definable_yoneda

instance self.definable_sheaf : definable_sheaf S R :=
definable_sheaf.rep

section

variables (S)

class definable_rep (W : Type*) [has_coordinates R W]
  extends is_definable S W, definable_sheaf S W :=
(eq : ∀ (K : Def S) (f : K → W), definable_sheaf.definable f ↔ def_fun S f)

instance self.definable_rep : definable_rep S R := { eq := λ K f, iff.rfl }

instance Def.definable_rep {K : Def S} : definable_rep S K :=
{ eq := λ _ f, iff.rfl }

variables (W : Type*) [has_coordinates R W] [is_definable S W]

def as_Def : Def S :=
{ ambdim := _,
  to_set := coordinate_image R W,
  is_definable := def_fun.coords.range }

-- TODO: Should we adjust the definition of `has_coordinates`
-- to make this computable?
noncomputable def equiv_Def : W ≃ as_Def S W :=
equiv.of_bijective (set.range_factorization (@coords R W _))
⟨λ w₁ w₂ h, @injective_coords R W _ w₁ w₂ (subtype.ext_iff.mp h),
 set.surjective_onto_range⟩

variables {S W}

lemma def_fun_equiv_Def : def_fun S (equiv_Def S W) :=
def_fun_subtype_mk def_fun.coords _

lemma def_fun_equiv_Def_symm : def_fun S (equiv_Def S W).symm :=
begin
  refine def_fun.cancel def_fun_equiv_Def (equiv.injective _) _,
  simpa using def_fun.id
end

end

variables {Y : Type*} [has_coordinates R Y] [definable_rep S Y]
variables {Y' : Type*} [has_coordinates R Y'] [definable_rep S Y']
variables {Z : Type*} [has_coordinates R Z] [definable_rep S Z]

lemma definable_iff_from_Def {f : Y → X} :
  definable S f ↔ definable_sheaf.definable (f ∘ (equiv_Def S Y).symm) :=
begin
  rw definable_fun,
  split; intro H,
  { apply H,
    rw definable_rep.eq,
    apply def_fun_equiv_Def_symm },
  { intros K φ hφ,
    rw definable_rep.eq at hφ,
    have : def_fun S (equiv_Def S Y ∘ φ) := def_fun_equiv_Def.comp hφ,
    convert definable_sheaf.definable_precomp ⟨equiv_Def S Y ∘ φ, this⟩ _ H,
    change φ = ((equiv_Def S Y).symm ∘ equiv_Def S Y) ∘ φ,
    simp }
end

lemma definable_iff_def_fun {f : Y → Z} :
  definable S f ↔ def_fun S f :=
begin
  rw definable_iff_from_Def,
  rw definable_rep.eq,
  split; intro H,
  { convert H.comp def_fun_equiv_Def,
    change f = f ∘ _,
    simp },
  { exact H.comp def_fun_equiv_Def_symm }
end

lemma definable_iff_def_set {s : set Y} :
  definable S s ↔ def_set S s :=
begin
  rw definable_iff_from_Def,
  split; intro H,
  { convert def_fun_equiv_Def.preimage H,
    change s = s ∘ _,
    simp },
  { exact def_fun_equiv_Def_symm.preimage H }
end

-- Yoneda embedding commutes with products
instance prod.definable_rep : definable_rep S (Y × Y') :=
begin
  refine { eq := λ K f, _ },
  change _ ∧ _ ↔ _,
  rw [definable_rep.eq, definable_rep.eq],
  split; intro H,
  { convert def_fun.prod' H.1 H.2,
    ext; refl },
  { exact ⟨def_fun.fst.comp H, def_fun.snd.comp H⟩ }
end

lemma definable_iff_uncurry {f : X → X' → X''} :
  definable S f ↔ definable S (function.uncurry f) :=
⟨λ H, definable.uncurry.app H, λ H, definable.curry.app H⟩

lemma definable_iff_def_fun₂ {f : Y → Y' → Z} :
  definable S f ↔ def_fun S (function.uncurry f) :=
definable_iff_uncurry.trans definable_iff_def_fun

lemma definable_iff_def_rel₂ {s : Y → Y' → Prop} :
  definable S s ↔ def_set S {p : Y × Y' | s p.1 p.2} :=
definable_iff_uncurry.trans definable_iff_def_set

-- TODO: Does this hold more generally than for representable codomains?
lemma definable_of_graph {f : X → Y} (df : definable S {p : X × Y | f p.1 = p.2}) :
  definable S f :=
begin
  rw definable_fun,
  intros K φ hφ,
  rw ←definable_yoneda at hφ,
  rw definable_rep.eq,
  change def_set S ({p : X × Y | f p.1 = p.2} ∘ (λ (q : K × Y), (φ q.1, q.2))),
  rw ←definable_iff_def_set,
  refine df.comp _,
  -- TODO: use more convenient lemmas
  begin [defin]
    intro q,
    app, app, exact definable.prod_mk.definable _,
    app, exact hφ.definable _,
    app, exact definable.fst.definable _, var,
    app, exact definable.snd.definable _, var
  end
end

def subtype.definable_rep {s : set Y} (ds : definable S s) : definable_rep S s :=
{ eq := λ K f, (definable_rep.eq K (subtype.val ∘ f)).trans def_fun_subtype_iff.symm,
  .. is_definable.subtype (definable_iff_def_set.mp ds) }

end o_minimal
