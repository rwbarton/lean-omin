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

instance (K : Def S) : is_definable S K :=
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

end o_minimal
