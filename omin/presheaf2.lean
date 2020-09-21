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

instance pt.unique : unique (pt : Def S) :=
⟨⟨⟨fin_zero_elim, trivial⟩⟩, λ x, by { ext i, fin_cases i }⟩

/-! ### Presheaf stuff -/

variables (S)

-- TODO: generalize to Sort?
class definable_psh (X : Type*) :=
(definable : Π {K : Def S}, (K → X) → Prop)
(definable_precomp : ∀ {L K : Def S} (φ : L ⟶ K) {f : K → X},
  definable f → definable (f ∘ φ))

-- TODO: apply bug??
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

lemma pt.definable {K : Def S} {f : K → (pt : Def S)} : definable_psh.definable f :=
begin
  change S.definable _,
  convert K.is_def_coords using 1,
  ext x,
  split,
  { rintros ⟨⟨k, p⟩, -, rfl⟩,
    refine ⟨k, trivial, _⟩,
    simp },
  { rintros ⟨k, -, rfl⟩,
    refine ⟨⟨k, default _⟩, show _ = _, by cc, _⟩,
    simp }
end

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
begin
  split; intro H,
  { intros K φ hφ,
    -- TODO: This proof is awkward
    specialize H K,
    swap,
    { exact (λ k, (default _, φ k)) },
    exact H ⟨pt.definable, hφ⟩ },
  { intros K φ hφ,
    exact H _ hφ.2 }
end

lemma definable_app {X Y : Type*} [definable_psh S X] [definable_psh S Y]
  {f : X → Y} (hf : definable S f) {x : X} (hx : definable S x) : definable S (f x) :=
begin
  rw definable_fun at hf,
  exact hf _ hx
end

lemma definable.app_ctx {Γ X Y : Type*} [definable_psh S Γ] [definable_psh S X] [definable_psh S Y]
  {f : Γ → X → Y} (hf : definable S f) {x : Γ → X} (hx : definable S x) :
  definable S (λ γ, f γ (x γ)) :=
begin
  rw definable_fun at ⊢ hf hx,
  intros K φ hφ,
  change definable_psh.definable (λ k, f (φ k) (x (φ k))),
  specialize hf φ hφ,
  specialize hf K,
  swap, { exact λ k, (k, x (φ k)) },
  exact hf ⟨(Def.id K).is_definable, hx φ hφ⟩
end

lemma definable_yoneda {K : Def S} {X : Type*} [definable_psh S X]
  {f : K → X} : definable_psh.definable f ↔ definable S f :=
begin
  rw definable_fun,
  split,
  { intros h L φ hφ,
    exact definable_psh.definable_precomp ⟨φ, hφ⟩ h },
  { intros H,
    refine H id _,
    exact (Def.id K).is_definable }
end

lemma definable_prod_mk {X Y : Type*} [definable_psh S X] [definable_psh S Y] :
  definable S (prod.mk : X → Y → X × Y) :=
-- I have no idea how to come up with these proofs.
-- Maybe we should tweak the type of definable_precomp (or write a lemma)
-- that takes the underlying map φ and its proof of definability separately
-- so that Lean has a better chance of guessing what's happening?
λ L g h L' g' h',
⟨definable_psh.definable_precomp ⟨λ x, (g' x).fst, h'.1⟩ h.2, h'.2⟩

lemma definable_fst {X Y : Type*} [definable_psh S X] [definable_psh S Y] :
  definable S (prod.fst : X × Y → X) :=
begin
  rw definable_fun,
  intros K φ hφ,
  exact hφ.1
end

lemma definable_snd {X Y : Type*} [definable_psh S X] [definable_psh S Y] :
  definable S (prod.snd : X × Y → Y) :=
begin
  rw definable_fun,
  intros K φ hφ,
  exact hφ.2
end

lemma definable.prod_mk {W X Y : Type*} [definable_psh S W] [definable_psh S X] [definable_psh S Y]
  {f : W → X} (hf : definable S f) {g : W → Y} (hg : definable S g) :
  definable S (λ w, (f w, g w)) :=
begin
  rw definable_fun at ⊢ hf hg,
  intros K φ hφ,
  exact ⟨hf φ hφ, hg φ hφ⟩
end

lemma definable_fun₂ {X Y Z : Type*} [definable_psh S X] [definable_psh S Y] [definable_psh S Z]
  {f : X → Y → Z} :
  (∀ {L : Def S} (φ : L → X), definable S φ → definable S (f ∘ φ)) ↔
  (∀ {L : Def S} (φ : L → X × Y), definable S φ → definable S (function.uncurry f ∘ φ)) :=
begin
  split; intro H,
  { intros L φ hφ,
    rw definable_fun at ⊢,
    intros K ψ hψ,
    have : definable S (prod.fst ∘ φ),
    { rw ←definable_yoneda at ⊢ hφ,
      exact hφ.1 },
    specialize H (λ l, (φ l).1) this,
    rw definable_fun at H,
    specialize H ψ hψ,
    specialize H K,
    swap, { exact λ k, (k, (φ (ψ k)).2) },
    refine H ⟨(Def.id K).is_definable, _⟩, clear H,
    rw ←definable_yoneda at hφ,
    exact definable_psh.definable_precomp ⟨ψ, hψ⟩ hφ.2 },
  { intros L φ hφ,
    rw definable_fun,
    intros K ψ hψ,
    intros K' ψ' hψ',
    dsimp [function.uncurry, function.comp],
    specialize H (λ k', (φ (ψ (ψ' k').1), (ψ' k').2)),
    have : definable S (λ k', (φ (ψ (ψ' k').1), (ψ' k').2)),
    { rw ←definable_yoneda at ⊢ hφ,
      split,
      { refine definable_psh.definable_precomp ⟨λ k', ψ (ψ' k').fst, _⟩ hφ,
        exact (Hom.comp ⟨ψ, hψ⟩ ⟨_, hψ'.1⟩).is_definable },
      { exact hψ'.2 } },
    specialize H this,
    rw definable_fun at H,
    exact H _ (Def.id _).is_definable }
end

lemma definable_comp {X Y Z : Type*} [definable_psh S X] [definable_psh S Y] [definable_psh S Z] :
  definable S (function.comp : (Y → Z) → (X → Y) → (X → Z)) :=
begin
  -- TODO: Make these 4 lines a lemma.
  rw definable_fun,
  intros L₁ φ₁ hφ₁,
  rw definable_yoneda at ⊢ hφ₁,
  revert L₁,
  -- end lemma
  rw definable_fun₂,
  rw definable_fun₂,
  rintros L φ hφ,
  rw ←definable_yoneda at hφ,
  obtain ⟨⟨hφ₁, hφ₂⟩, hφ₃⟩ := hφ,
  rw definable_yoneda at hφ₁ hφ₂ hφ₃,
  dsimp [function.uncurry, function.comp],
  exact hφ₁.app_ctx (hφ₂.app_ctx hφ₃)
end

lemma definable.comp {X Y Z : Type*} [definable_psh S X] [definable_psh S Y] [definable_psh S Z]
  {g : Y → Z} (hg : definable S g) {f : X → Y} (hf : definable S f) :
  definable S (g ∘ f) :=
definable_app (definable_app definable_comp hg) hf

lemma definable.comp_ctx {Γ X Y Z : Type*} [definable_psh S Γ] [definable_psh S X] [definable_psh S Y] [definable_psh S Z]
  {g : Γ → Y → Z} (hg : definable S g) {f : Γ → X → Y} (hf : definable S f) :
  definable S (λ γ, g γ ∘ f γ) :=
definable.app_ctx (definable.comp definable_comp hg) hf

lemma definable_curry {X Y Z : Type*} [definable_psh S X] [definable_psh S Y] [definable_psh S Z] :
  definable S (function.curry : (X × Y → Z) → X → Y → Z) :=
begin
  -- TODO: Make these 4 lines a lemma.
  rw definable_fun,
  intros L₁ φ₁ hφ₁,
  rw definable_yoneda at ⊢ hφ₁,
  revert L₁,
  -- end lemma
  rw definable_fun₂,
  rw definable_fun₂,
  rintros L φ hφ,
  rw ←definable_yoneda at hφ,
  obtain ⟨⟨hφ₁, hφ₂⟩, hφ₃⟩ := hφ,
  rw definable_yoneda at hφ₁ hφ₂ hφ₃,
  exact definable.app_ctx hφ₁ (hφ₂.prod_mk hφ₃)
end

instance Prop.definable_psh : definable_psh S Prop :=
{ definable := λ K s, S.def_coords s,
  definable_precomp := λ L K φ f hf, sorry } -- preimage

instance set.definable_psh {X : Type*} [definable_psh S X] : definable_psh S (set X) :=
show definable_psh S (X → Prop), by apply_instance

lemma definable_and : definable S (∧) :=
begin
  suffices : definable S (λ r : Prop × Prop, r.1 ∧ r.2),
  { exact definable_app definable_curry this },
  rw definable_fun,
  rintros K φ ⟨hφ₁, hφ₂⟩,
  exact hφ₁.inter hφ₂
end

lemma definable.and {W : Type*} [definable_psh S W]
  {f : W → Prop} (hf : definable S f) {g : W → Prop} (hg : definable S g) :
  definable S (λ w, f w ∧ g w) :=
definable.app_ctx (definable.comp definable_and hf) hg

lemma definable_inter {X : Type*} [definable_psh S X] :
  definable S ((∩) : set X → set X → set X) :=
begin
  suffices : definable S (λ (r : set X × set X) (x : X), r.1 x ∧ r.2 x),
  { exact (definable_app definable_curry this : _) },
  -- TODO: Make these 4 lines a lemma.
  rw definable_fun,
  intros L₁ φ₁ hφ₁,
  rw definable_yoneda at ⊢ hφ₁,
  revert L₁,
  -- end lemma
  rw definable_fun₂,
  intros L φ hφ,
  rw ←definable_yoneda at hφ,
  obtain ⟨⟨hφ₁, hφ₂⟩, hφ₃⟩ := hφ,
  rw definable_yoneda at hφ₁ hφ₂ hφ₃,
  apply definable.and,
  { exact hφ₁.app_ctx hφ₃ },
  { exact hφ₂.app_ctx hφ₃ }
end

/-
instance foo {X Y : Type*} [definable_psh S X] [definable_psh S Y]
  {p : X → Prop}
  : definable_psh S (Π (x : X) (h : p x), Y) :=
sorry
-/

lemma definable_definable {X : Type*} [definable_psh S X] :
  definable S (definable S : X → Prop) :=
begin
  rw definable_fun,
  intros K φ hφ,
  change S.def_coords _,
  convert K.is_def_coords,
  apply set.eq_univ_of_forall,
  intro x,
  change definable S (φ x),
  apply definable_app,
  { rw ←definable_yoneda, exact hφ },
  -- now we need to know that every point of a representable guy
  -- is definable. this needs definable constants!
  sorry
  -- In general, the definable elements of a structure
  -- might or might not form a definable set.
  -- Counterexample: take (ℝ, +, *) without constants;
  -- definable elements are the algebraic real numbers,
  -- but only tame sets can be definable.
  -- However, once the structure has definable constants,
  -- then everything is definable and of course the set `univ` is definable.
end
-- Important note: it is definitely *not* true that
-- `definable S` = `set.univ` on *every* X with a definable_psh structure;
-- just represented guys.

/-
similarly, in an o-minimal structure:

lemma definable_finite [DUNLO R] [o_minimal S] :
  definable S (set.finite : set R → Prop) := sorry

because "finite" is equivalent to "does not contain an interval"
on the tame = definable sets, which are the only ones that matter.
-/

instance self : definable_psh S R := sorry

variables (S)

#exit
class definable_fam {X : Type*} [definable_psh S X] (Y : X → Sort*) :=
(definable : Π {K : Def S} (x : K → X) (hx : definable_psh.definable x), (Π k, Y (x k)) → Prop)
-- s.t. blah blah blah...

instance moo {X : Type*} {Y : X → Type*} [definable_psh S X] [definable_fam S Y] :
  definable_psh S (Π (x : X), Y x) :=
sorry

constant choice : Π (X : set R), X.nonempty → X

example : definable S (set.nonempty : set R → Prop) :=
sorry

instance : definable_fam S (set.nonempty : set R → Prop) := sorry

instance pi {X : Type*} [definable_psh S X] {Y Z : X → Sort*} [definable_fam S Y] [definable_fam S Z] :
  definable_fam S (λ x, Y x → Z x) :=
sorry

instance subtype {X : Type*} [definable_psh S X] : definable_fam S (λ (s : set X), s) :=
sorry

example : definable S ((λ x hx₁ hx₂, choice x hx₁) : Π (X : set R), X.nonempty → X.nonempty → X) :=
sorry

-- can we do without this `definable_fam` stuff? even as a hack?
-- or maybe stick with this for now?

/- TODO:
* class represented [has_coordinates R X] expressing compatibility
* prove this notion of definability of functions, sets reduces
  to the original one in the represented case
Then:
* prove stuff like `is_least : set R → R → Prop` is definable
-/

end o_minimal
