import o_minimal.Def

/-
Definable sheaves.

Here we provide just enough definitions, instances and lemmas
to set up the tactic environment. The eventual frontend for all this
is intended to consist of `definable` and the `definable_sheaf` class,
but there is still plenty of construction to do.
-/

namespace o_minimal

universe u

variables {R : Type u} (S : struc R)

class definable_sheaf (X : Type*) :=
(definable : Π {K : Def S}, (K → X) → Prop)
(definable_precomp : ∀ {L K : Def S} (φ : L ⟶ K) (f : K → X),
  definable f → definable (f ∘ φ))
(definable_cover : ∀ {K : Def S} (f : K → X) (𝓛 : Def.cover K),
  (∀ i, definable (f ∘ 𝓛.map i)) → definable f)

namespace definable_sheaf

variables {S}

def rep {W : Type*} [has_coordinates R W] [is_definable S W] :
  definable_sheaf S W :=
{ definable := λ K f, def_fun S f,
  definable_precomp := λ L K φ f hf, hf.comp φ.is_definable,
  definable_cover := λ K f 𝓛 h, Def.subcanonical 𝓛 f h }

instance Def.definable_sheaf {X : Def S} : definable_sheaf S X :=
definable_sheaf.rep

variables {X Y : Type*} [definable_sheaf S X] [definable_sheaf S Y]

instance prod.definable_sheaf : definable_sheaf S (X × Y) :=
{ definable := λ K f,
    definable_sheaf.definable (prod.fst ∘ f) ∧
    definable_sheaf.definable (prod.snd ∘ f),
  definable_precomp := λ L K φ _ h,
    ⟨definable_sheaf.definable_precomp φ _ h.1,
     definable_sheaf.definable_precomp φ _ h.2⟩,
  definable_cover := λ K f 𝓛 h,
    ⟨definable_sheaf.definable_cover _ 𝓛 (λ i, (h i).1),
     definable_sheaf.definable_cover _ 𝓛 (λ i, (h i).2)⟩ }

instance fun.definable_sheaf : definable_sheaf S (X → Y) :=
{ definable := λ K f,
    ∀ (L : Def S) (g : L → K × X) (h : definable_sheaf.definable g),
      definable_sheaf.definable (function.uncurry f ∘ g),
  definable_precomp := λ L K φ f hf M g hg,
    hf M (λ m, (φ (g m).1, (g m).2))
      ⟨definable_sheaf.definable_precomp ⟨λ m, (g m).1, hg.1⟩ φ φ.is_definable, hg.2⟩,
  definable_cover := λ K f 𝓛 h K' g hg, begin
    let g₁ : K' ⟶ K := ⟨λ k', (g k').1, hg.1⟩,
    let 𝓛' := 𝓛.pullback g₁,
    apply definable_sheaf.definable_cover _ 𝓛',
    intro i,
    specialize h i (𝓛'.obj i)
      (λ l', (Def.pullback.π₂ g₁ _ l', (g (𝓛'.map i l')).2))
      ⟨(Def.pullback.π₂ g₁ _).is_definable, definable_sheaf.definable_precomp _ _ hg.2⟩,
    dsimp only [function.uncurry, function.comp] at ⊢ h,
    convert h,
    ext x,
    congr,
    exact x.property.snd.snd,
  end }

/-- Intended to be an implementation detail of the tactic mode.
In "user code", use `definable` instead. -/
structure sect (Γ : Def S) (X : Type*) [definable_sheaf S X] :=
(to_fun : Γ → X)
(definable : definable_sheaf.definable to_fun)

def sect.precomp {Γ' Γ : Def S} (σ : sect Γ X) (φ : Γ' ⟶ Γ) : sect Γ' X :=
{ to_fun := σ.to_fun ∘ φ.to_fun,
  definable := definable_sheaf.definable_precomp φ σ.to_fun σ.definable }

lemma definable_fun_iff {Γ : Def S} {f : Γ → X → Y} :
  definable_sheaf.definable f ↔
  ∀ (Γ' : Def S) (π : Hom Γ' Γ) (σ : sect Γ' X),
    definable_sheaf.definable (λ i', f (π.to_fun i') (σ.to_fun i')) :=
⟨λ H Γ' π σ, H Γ' (λ γ', (π.to_fun γ', σ.to_fun γ')) ⟨π.is_definable, σ.definable⟩,
 λ H M g hg, H M ⟨_, hg.1⟩ ⟨_, hg.2⟩⟩

/- The weird binder types are because this lemma is intended to be applied
by a special `defin` tactic. -/
lemma definable_app {Γ : Def S}
  (f : Γ → X → Y) {hf : definable_sheaf.definable f}
  (x : Γ → X) {hx : definable_sheaf.definable x} :
  definable_sheaf.definable (λ i, f i (x i)) :=
hf Γ (λ γ, (γ, x γ)) ⟨def_fun.id, hx⟩

end definable_sheaf

structure definable {X : Type*} [definable_sheaf S X] (x : X) : Prop :=
(definable : ∀ (K : Def S), definable_sheaf.definable (λ (i : K), x))

end o_minimal
