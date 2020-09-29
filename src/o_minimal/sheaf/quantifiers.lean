import o_minimal.sheaf.yoneda

-- Lemmas for proving definability of propositions with quantifiers
-- `∀ (x : X), P x`, `∃ (x : X), P x`. Here `X` must be representable.

namespace o_minimal

variables {R : Type*} {S : struc R}
variables {X : Type*} [has_coordinates R X] [definable_rep S X]

lemma definable_forall : definable S (λ (p : X → Prop), ∀ x, p x) :=
begin
  rw definable_fun,
  intros K φ hφ,
  rw ←definable_yoneda at ⊢ hφ,
  rw definable_iff_def_set,
  rw definable_iff_def_rel₂ at hφ,
  apply def_set.forall hφ,
end

-- Helper lemma for applying `definable_forall` in a `[defin]` block.
lemma definable_sheaf.forall {Γ : Def S}
  (p : Γ → X → Prop) {hp : definable_sheaf.definable p} :
  definable_sheaf.definable (λ i, ∀ x, p i x) :=
begin
  apply definable_sheaf.definable_app (λ i (p : X → Prop), ∀ x, p x),
  { exact hp },
  { exact definable_forall.definable _ }
end

-- Not directly related to quantifiers,
-- but frequently appears in "bounded" ones.
lemma definable_sheaf.imp {Γ : Def S}
  (p : Γ → Prop) {hp : definable_sheaf.definable p}
  (q : Γ → Prop) {hq : definable_sheaf.definable q} :
  definable_sheaf.definable (λ i, p i → q i) :=
def_set.imp hp hq

-- `definable S Exists`
lemma definable_Exists : definable S (λ (p : X → Prop), ∃ x, p x) :=
begin
  rw definable_fun,
  intros K φ hφ,
  rw ←definable_yoneda at ⊢ hφ,
  rw definable_iff_def_set,
  rw definable_iff_def_rel₂ at hφ,
  apply def_set.exists hφ,
end

lemma definable_nonempty : definable S (set.nonempty : set X → Prop) :=
begin [defin]
  intro s,
  app, exact definable_Exists.definable _,
  intro x,
  app, app, exact definable.mem.definable _, var, var
end

end o_minimal

namespace defin.interactive
setup_tactic_parser

meta def all (var : parse ident_) : defin unit :=
do `[refine o_minimal.definable_sheaf.forall _],
   intro var

meta def imp : defin unit :=
`[refine o_minimal.definable_sheaf.imp _ _]

end defin.interactive

namespace o_minimal

variables {R : Type*} {S : struc R}
variables {X : Type*} [has_coordinates R X] [definable_rep S X]

lemma definable_subset : definable S ((⊆) : set X → set X → Prop) :=
begin [defin]
  intro s,
  intro t,
  all x,
  imp,
  { app, app, exact definable.mem.definable _, var, var },
  { app, app, exact definable.mem.definable _, var, var }
end

lemma definable_powerset : definable S (set.powerset : set X → set (set X)) :=
begin [defin]
  intro s,
  intro t,
  app, app, exact definable_subset.definable _, var, var
end

end o_minimal
