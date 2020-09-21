import .presheaf2
import .def_choice.choice

namespace o_minimal

variables {R : Type*} {S : struc R}

/- NB:
Some lemmas in this file have an unnecessarily strong [OQM R] hypothesis
where [DUNLO R] (or maybe even nothing) would be enough;
that's just because they are lemmas about things which were defined
under a standing hypothesis of [OQM R].
Since the proofs of these "lemmas" are all omitted, it's also possible
that some required hypotheses (like [is_definable_le S R]) may be missing.
-/

/- Remark:
In Type, `roption X` is the "partial map classifier X⁺": Σ (φ : Ω), X^φ.
(Here Ω = Prop is the subobject classifier.)
f : K → roption X cuts out a subset K' ⊆ K (where f is "defined"),
given by a pullback square

  K' → X
  ↓    ↓
  K  → X⁺

We want K' to be defined and the restriction f' : K' → X to be definable.
In this way, `roption X` models the "*definable* partial map classifier" for `X`.

We could also consider `option X = X ⊕ unit`, and under the "sheafy" semantics
of ⊕, we would end up with an equivalent definable_psh structure.
This is not because the topos of sheaves on Def is boolean (it isn't)
but because we choose to interpret `Prop` as the classifier for *definable* subobjects
and, in Sh(Def), definable subobjects are decidable (complementable).
(Contrast Sh(𝔻, closed topology) [𝔻 = definable sets + *continuous* definable maps]
where definable or even closed subobjects are not decidable--only clopen subobjects are.
If we force definable subobjects to be decidable, we turn Sh(𝔻) into Sh(Def).)
-/
instance roption.definable_psh {X : Type*} [definable_psh S X] : definable_psh S (roption X) :=
{ definable := λ K f, sorry,
  definable_precomp := sorry }

instance pfun.definable_psh {X Y : Type*} [definable_psh S X] [definable_psh S Y] :
  definable_psh S (X →. Y) :=
show definable_psh S (X → roption Y), by apply_instance

lemma definable_orelse_pure {X : Type*} [definable_psh S X] :
  definable S (λ (a : roption X) (b : X), a.orelse_pure b) :=
sorry

-- Ideally, we could also say the `pfun_of_rel` depends definably on `rel`.
-- However, we will only use a fixed list of `rel`s (`is_least`, `is_glb`, etc.)
-- so we don't actually need it.
lemma definable_pfun_of_rel [OQM R]
  (rel : set R → R → Prop) (uni) (hrel : definable S rel) :
  definable S (pfun_of_rel rel uni) :=
sorry

-- Presumably, this lemma has the same content as the earlier
-- lemma def_is_least : def_rel_set S (is_least : set R → R → Prop).
-- Also, this one should be generalizable to any
--   {X : Type*} [definable_psh S X] [partial_order X] [definable_le S X]
-- in place of R!
lemma definable_the_least [OQM R] [is_definable_le S R] :
  definable S (the_least : set R →. R) :=
sorry

lemma definable_roption_map {X Y : Type*} [definable_psh S X] [definable_psh S Y] :
  definable S (roption.map : (X → Y) → (roption X → roption Y)) :=
sorry

lemma definable_Ioo [DUNLO R] [is_definable_le S R] :
  definable S (set.Ioo : R → R → set R) :=
sorry

lemma definable_interval_above [DUNLO R] [is_definable_le S R] :
  definable S (λ (X : set R) a, {b | a < b ∧ set.Ioo a b ⊆ X}) :=
sorry

lemma definable_chosen_one [OQM R] : definable S (@chosen_one R _) :=
sorry -- test case once we have a working tactic mode

end o_minimal
