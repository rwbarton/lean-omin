import data.matrix.notation
import o_minimal.sheaf.yoneda

namespace o_minimal

universe u

variables {R : Type*} (S : struc R)

structure map_to (X : Type*) [has_coordinates R X] [definable_rep S X] :=
(obj : Type*)
[has_coordinates : has_coordinates R obj]
[definable_rep : definable_rep S obj]
(to_fun : obj → X)
(is_definable : definable S to_fun)

attribute [instance] map_to.has_coordinates map_to.definable_rep

/-- General (finite) cover of a representable by representables. -/
structure cover (X : Type*) [has_coordinates R X] [definable_rep S X] :=
(n : ℕ)
(map : fin n → map_to S X)
(jointly_surjective : ∀ x, ∃ i l, (map i).to_fun l = x)

variables {S}

-- TODO: Can we avoid the messy pullback construction in `o_minimal.Def` using these?

noncomputable def Def.cover_of_general {K : Def S} (𝓛 : cover S K) : K.cover :=
{ n := 𝓛.n,
  obj := λ i, as_Def S (𝓛.map i).obj,
  map := λ i,
    ⟨(𝓛.map i).to_fun ∘ (equiv_Def S (𝓛.map i).obj).symm,
     (definable_iff_def_fun.mp (𝓛.map i).is_definable).comp def_fun_equiv_Def_symm⟩,
  jointly_surjective := λ k,
    let ⟨i, l, h⟩ := 𝓛.jointly_surjective k in
    ⟨i, (equiv_Def S (𝓛.map i).obj) l, show (𝓛.map i).to_fun _ = k, by simp [h]⟩ }

def cover.pullback {X' X : Type*} [has_coordinates R X'] [definable_rep S X']
  [has_coordinates R X] [definable_rep S X] (𝓛 : cover S X) (f : X' → X) (df : definable S f) :
  cover S X' :=
{ n := 𝓛.n,
  map := λ i,
  { obj := {p : X' × (𝓛.map i).obj | f p.1 = (𝓛.map i).to_fun p.2},
    definable_rep := subtype.definable_rep $ definable_iff_def_set.mpr $ def_set_eq
      ((definable_iff_def_fun.mp df).comp def_fun.fst)
      ((definable_iff_def_fun.mp (𝓛.map i).is_definable).comp def_fun.snd),
    to_fun := prod.fst ∘ subtype.val,
    is_definable := definable.fst.comp definable.subtype.val },
  jointly_surjective := λ x',
    let ⟨i, l, h⟩ := 𝓛.jointly_surjective (f x') in
    ⟨i, ⟨⟨x', l⟩, h.symm⟩, rfl⟩ }

def cover_of_Def {K : Def S} (𝓛 : K.cover) : cover S K :=
{ n := 𝓛.n,
  map := λ i,
  { obj := 𝓛.obj i,
    to_fun := 𝓛.map i,
    is_definable := definable_iff_def_fun.mpr (𝓛.map i).is_definable },
  jointly_surjective := 𝓛.jointly_surjective }

variables {X : Type*} [has_coordinates R X] [definable_rep S X]
variables {Y : Type*} [definable_sheaf S Y]

lemma definable_cover_of_Def {K : Def S} (f : K → Y) (𝓛 : cover S K)
  (h : ∀ i, definable S (f ∘ (𝓛.map i).to_fun)) : definable S f :=
begin
  rw definable_yoneda,
  let 𝓛' := Def.cover_of_general 𝓛,
  apply definable_sheaf.definable_cover _ 𝓛',
  intro i,
  rw ←definable_yoneda,
  refine (h i).comp _,
  rw definable_iff_def_fun,
  apply def_fun_equiv_Def_symm
end

lemma definable_cover (f : X → Y) (𝓛 : cover S X)
  (h : ∀ i, definable S (f ∘ (𝓛.map i).to_fun)) : definable S f :=
begin
  rw definable_fun,
  intros K φ hφ,
  let 𝓛' := 𝓛.pullback φ (definable_yoneda.mpr hφ),
  rw ←definable_yoneda at ⊢ hφ,
  apply definable_cover_of_Def _ 𝓛',
  intro i,
  change definable S (f ∘ (φ ∘ (𝓛'.map i).to_fun)),
  let ψ : (𝓛'.map i).obj → (𝓛.map i).obj := λ z, z.val.snd,
  have dψ : definable S ψ := definable.snd.comp definable.subtype.val,
  have : φ ∘ (𝓛'.map i).to_fun = (𝓛.map i).to_fun ∘ ψ,
  { ext x,
    exact x.property },
  rw this,
  refine (h i).comp dψ
end

-- Building covers.

def sep_cover (s : set X) (ds : definable S s) : cover S X :=
{ n := 2,
  map :=
  ![{ obj := s,
      definable_rep := subtype.definable_rep ds,
      to_fun := subtype.val,
      is_definable := begin
        -- TODO: lemma
        rw definable_iff_def_fun,
        exact @def_fun_subtype_val R S X _ _ s (definable_iff_def_set.mp ds)
      end },
    { obj := ↥(sᶜ),
      definable_rep := subtype.definable_rep (definable.app definable.compl ds),
      to_fun := subtype.val,
      is_definable := begin
        -- TODO: lemma
        rw definable_iff_def_fun,
        exact @def_fun_subtype_val R S X _ _ _ (def_set.compl $ definable_iff_def_set.mp ds)
      end } ],
  jointly_surjective := begin
    intro x,
    by_cases hx : x ∈ s,
    { refine ⟨0, by exact ⟨x, hx⟩, by exact rfl⟩ },
    { refine ⟨1, by exact ⟨x, hx⟩, by exact rfl⟩ }
  end }

-- TODO: is this true for any sheaf X?
lemma definable_if (f : X → Y) (s : set X) (ds : definable S s)
  (hpos : definable S (f ∘ (subtype.val : s → X)))
  (hneg : definable S (f ∘ (subtype.val : sᶜ → X))) :
  definable S f :=
begin
  apply definable_cover f (sep_cover s ds),
  intro i,
  fin_cases i,
  { exact hpos },
  { exact hneg }
end

end o_minimal
