import o_minimal.sheaf.tactic

namespace o_minimal

variables {R : Type*} {S : struc R}
variables {X Y Z : Type*} [definable_sheaf S X] [definable_sheaf S Y] [definable_sheaf S Z]

-- TODO: consistent naming

lemma definable.const : definable S (@function.const X Y) :=
begin [defin]
  intro x,
  intro y,
  var
end

lemma definable_comp : definable S (@function.comp X Y Z) :=
begin [defin]
  intro f,
  intro g,
  intro x,
  app, var,
  app, var, var
end

lemma definable.app {f : X → Y} (hf : definable S f) {x : X} (hx : definable S x) :
  definable S (f x) :=
begin [defin]
  app,
  exact hf.definable _,
  exact hx.definable _
end

lemma definable.comp {g : Y → Z} (hg : definable S g) {f : X → Y} (hf : definable S f) :
  definable S (g ∘ f) :=
(definable_comp.app hg).app hf

lemma definable.prod_mk : definable S (@prod.mk X Y) :=
begin [defin]
  intro x,
  intro y,
  exact ⟨x.definable, y.definable⟩
end

lemma definable.fst : definable S (prod.fst : X × Y → X) :=
begin [defin]
  intro p,
  exact p.definable.1
end

lemma definable.snd : definable S (prod.snd : X × Y → Y) :=
begin [defin]
  intro p,
  exact p.definable.2
end

lemma definable.curry : definable S (@function.curry X Y Z) :=
begin [defin]
  intro f,
  intro x,
  intro y,
  app, var,
  app, app, exact definable.prod_mk.definable _, var, var
end

lemma definable.uncurry : definable S (@function.uncurry X Y Z) :=
begin [defin]
  intro f,
  intro p,
  app, app, var,
  app, exact definable.fst.definable _, var,
  app, exact definable.snd.definable _, var
end

instance punit.definable_sheaf : definable_sheaf S punit :=
{ definable := λ K f, true,
  definable_precomp := λ L K φ f hf, trivial,
  definable_cover := λ K f 𝓛 h, trivial }

lemma definable.star : definable S punit.star :=
begin [defin]
  exact trivial
end

instance Prop.definable_sheaf : definable_sheaf S Prop :=
{ definable := λ K f, def_set S f,
  definable_precomp := λ L K φ f hf, φ.is_definable.preimage hf,
  definable_cover := λ K f 𝓛 h, Def.set_subcanonical 𝓛 f h }

lemma definable.and : definable S and :=
begin [defin]
  intro p,
  intro q,
  exact def_set.inter p.definable q.definable
end

lemma definable.or : definable S or :=
begin [defin]
  intro p,
  intro q,
  exact def_set.union p.definable q.definable
end

lemma definable.imp : definable S ((→) : Prop → Prop → Prop) :=
begin [defin]
  intro p,
  intro q,
  exact def_set.imp p.definable q.definable
end

lemma definable.not : definable S not :=
begin [defin]
  intro p,
  exact def_set.compl p.definable
end

lemma definable.iff : definable S iff :=
begin [defin]
  intro p,
  intro q,
  exact def_set.iff p.definable q.definable
end

instance set.definable_sheaf : definable_sheaf S (set X) :=
show definable_sheaf S (X → Prop), by apply_instance

lemma definable.mem : definable S ((∈) : X → set X → Prop) :=
begin [defin]
  intro x,
  intro s,
  app, var, var
end

lemma definable.inter : definable S ((∩) : set X → set X → set X) :=
begin [defin]
  intro s,
  intro t,
  intro x,
  app,
  app,
  exact definable.and.definable _,
  app, app, exact definable.mem.definable _, var, var,
  app, app, exact definable.mem.definable _, var, var
end

lemma definable.union : definable S ((∪) : set X → set X → set X) :=
begin [defin]
  intro s,
  intro t,
  intro x,
  app,
  app,
  exact definable.or.definable _,
  app, app, exact definable.mem.definable _, var, var,
  app, app, exact definable.mem.definable _, var, var
end

lemma definable.compl : definable S (set.compl : set X → set X) :=
begin [defin]
  intro s,
  intro x,
  app, exact definable.not.definable _,
  app, app, exact definable.mem.definable _, var, var
end

lemma definable.diff : definable S ((\) : set X → set X → set X) :=
begin [defin]
  intro s,
  intro t,
  intro x,
  app, app, exact definable.and.definable _,
  app, app, exact definable.mem.definable _, var, var,
  -- unnecessarily complicated, but hey why not
  -- TODO: `change`
  app,
  intro a,
  app, exact definable.not.definable _,
  app, app, exact definable.mem.definable _, var, var,
  var
end

-- Quantification over X is not definable in general.
-- Needs a special property of X: "quasicompactness"?
-- See `quantifiers` (for now, just over representables)

instance subtype.definable_sheaf {s : set X} : definable_sheaf S s :=
{ definable := λ K f, definable_sheaf.definable (subtype.val ∘ f),
  definable_precomp := λ L K φ f hf,
    definable_sheaf.definable_precomp φ (subtype.val ∘ f) hf,
  definable_cover := λ K f 𝓛 hf,
    definable_sheaf.definable_cover (subtype.val ∘ f) 𝓛 hf }

instance {p : X → Prop} : definable_sheaf S {x // p x} :=
show definable_sheaf S (set_of p), by apply_instance

-- instance prop.definable_sheaf {p : Prop} : definable_sheaf S p := sorry

-- TODO: With an instance for Pi types, can we state the definable dependence on `s`?
lemma definable.subtype.val {s : set X} : definable S (subtype.val : s → X) :=
begin [defin]
  intro v,
  exact v.definable
end

lemma definable_of_subtype_val {s : set Y} {f : X → s}
  (hf : definable S (subtype.val ∘ f)) : definable S f :=
begin
  cases hf with hf,
  exact ⟨λ K, hf K⟩
end

-- How to state definable subtype.mk?
/-
lemma definable.subtype.mk {s : set X} :
  definable S (subtype.mk : Π (x : X), x ∈ s → s) :=
begin
end
-/

lemma definable_subtype.map {s : set X} {t : set Y} {f : X → Y} (hf : definable S f)
  (h : ∀ x ∈ s, f x ∈ t) : definable S (subtype.map f h : s → t) :=
definable_of_subtype_val $ hf.comp definable.subtype.val

end o_minimal
