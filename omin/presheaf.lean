import o_minimal.definable

open o_minimal

variables {R : Type*} (S : struc R)

/-- A *definable presheaf* structure on a type X
consists of the data of, for every definable set S ⊆ Rⁿ,
a predicate `definable` on functions S → X, satisfying the axiom:
for every definable map φ : T → S, precomposition by φ
preserves definable functions into X. -/
-- TODO: Refactor to be prior to def_set/def_fun?
class definable_presheaf (X : Type*) :=
(definable : Π {n : ℕ} {s : set (fin n → R)} (ds : def_set S s),
  (s → X) → Prop)
(definable_precomp : Π {n m : ℕ} {s : set (fin n → R)} {ds : def_set S s}
  {t : set (fin m → R)} {dt : def_set S t} (φ : t → s)
  (dφ : @def_fun R S _ _ (is_definable.subtype dt) _ _ (is_definable.subtype ds) φ)
--(dφ : S.definable {z | ∃ (hz : finvec.left z ∈ t), (φ ⟨finvec.left z, hz⟩).val = finvec.right z})
  (f : s → X), definable ds f → definable dt (f ∘ φ))

-- TODO: sheaf conditions

instance Prop.definable_presheaf : definable_presheaf S Prop :=
{ definable := λ n s ds a, @def_set R S _ _ (is_definable.subtype ds) a,
  definable_precomp := λ n m s ds t dt φ dφ a da,
  @def_fun.preimage R S _ _ (is_definable.subtype dt) _ _ (is_definable.subtype ds) φ dφ a da }

-- for now don't make this an instance, because of diamond problem with ×
def definable_presheaf_of_is_definable {X : Type*} [has_coordinates R X] [is_definable S X] :
  definable_presheaf S X :=
{ definable := λ n s ds f, by haveI := is_definable.subtype ds; exact def_fun S f,
  definable_precomp := λ n m s ds t dt φ dφ a da,
  by haveI := is_definable.subtype ds; haveI := is_definable.subtype dt; exact da.comp dφ }

structure defin {X : Type*} [definable_presheaf S X] {Y : Type*} [definable_presheaf S Y]
  (F : X → Y) : Prop :=
(preserves_definable : ∀ {n : ℕ} {s : set (fin n → R)} (ds : def_set S s) {f : s → X},
  definable_presheaf.definable ds f → definable_presheaf.definable ds (F ∘ f))

section yoneda
local attribute [instance] definable_presheaf_of_is_definable
-- A definable map between representables is definable in the new sense
-- if and only if it was definable in the old one.
-- A definable set in a representable is definable in the new sense
-- if and only if it was definable in the old one.

variables {X : Type*} [has_coordinates R X] [is_definable S X]
variables {Y : Type*} [has_coordinates R Y] [is_definable S Y]

lemma def_fun_iff_defin {f : X → Y} : def_fun S f ↔ defin S f :=
sorry

lemma def_set_iff_defin {s : set X} : def_set S s ↔ defin S s :=
sorry

end yoneda

instance prod.definable_presheaf {X Y : Type*} [definable_presheaf S X] [definable_presheaf S Y] :
  definable_presheaf S (X × Y) :=
{ definable := λ n s ds a,
    definable_presheaf.definable ds (λ x, (a x).fst) ∧
    definable_presheaf.definable ds (λ x, (a x).snd),
  definable_precomp := λ n m s ds t dt φ dφ a da,
    ⟨definable_presheaf.definable_precomp φ dφ (λ x, (a x).fst) da.1,
     definable_presheaf.definable_precomp φ dφ (λ x, (a x).snd) da.2⟩ }

instance Pi.definable_presheaf {X Y : Type*} [definable_presheaf S X] [definable_presheaf S Y] :
  definable_presheaf S (X → Y) :=
{ definable := λ n s ds a,
    by haveI : is_definable S s := is_definable.subtype ds;
       haveI : definable_presheaf S s := definable_presheaf_of_is_definable S;
       exact defin S (λ (p : s × X), a p.1 p.2),
  definable_precomp := sorry }

-- TODO: prove exponential law for `defin`
-- prove (un)currying preserves `defin`

-- TODO: prove definability of ∧ : Prop → Prop → Prop, etc.
-- this amounts to definable sets forming a boolean algebra!

instance subtype.definable_presheaf {X : Type*} [definable_presheaf S X] (A : set X) :
  definable_presheaf S A :=
{ definable := λ n s ds a, definable_presheaf.definable ds (subtype.val ∘ a),
  definable_precomp := sorry }

class compat_definable_coordinates (X : Type*) [has_coordinates R X] [definable_presheaf S X]
-- * definable, like in `is_definable`
-- * `definable_presheaf` structure equals the one from `definable_presheaf_of_is_definable`

