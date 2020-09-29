import data.pfun
import o_minimal.sheaf.covers

section orelse_pure

open_locale classical

noncomputable def roption.orelse_pure {α : Type*} (x : roption α) (y : α) :=
if h : x.dom then x.get h else y

lemma roption.orelse_pure_eq_iff {α : Type*} {x : roption α} {y : α} (z : α) :
  x.orelse_pure y = z ↔ (z ∈ x ∨ ¬ x.dom ∧ z = y) :=
begin
  unfold roption.orelse_pure,
  split_ifs with h; split; simp [h, roption.mem_eq, eq_comm]
end

end orelse_pure

namespace o_minimal

variables {R : Type*} {S : struc R}
variables {X : Type*} [definable_sheaf S X]
variables {Y : Type*} [definable_sheaf S Y]

instance roption.definable_sheaf : definable_sheaf S (roption X) :=
{ definable := λ K f,
    ∃ H : def_set S (pfun.dom f),
    definable S (pfun.as_subtype f),
  definable_precomp := λ L K φ f ⟨H, h⟩,
    ⟨φ.is_definable.preimage H,
     h.comp (definable_subtype.map (Def.definable_iff_def_fun.mpr φ.is_definable) (λ _, id))⟩,
  definable_cover := λ K f 𝓛 hf, begin
    have : def_set S (pfun.dom f) := Def.set_subcanonical 𝓛 _ (λ i, (hf i).fst),
    refine ⟨this, _⟩,
    letI : definable_rep S (pfun.dom f) :=
      subtype.definable_rep (definable_iff_def_set.mpr this),
    let 𝓛' : cover S (pfun.dom f) :=
      (cover_of_Def 𝓛).pullback subtype.val definable.subtype.val,
    refine definable_cover (pfun.as_subtype f) 𝓛' _,
    -- TODO: messy proof
    intro i,
    let ψ : (𝓛'.map i).obj → {l | (𝓛.map i).to_fun l ∈ pfun.dom f} :=
      λ l', ⟨l'.1.2, begin
        rcases l' with ⟨⟨⟨a, b⟩, c⟩, rfl : a = map_to.to_fun _ c⟩,
        exact b
      end⟩,
    have : (𝓛'.map i).to_fun = subtype.map (𝓛.map i) (λ _, id) ∘ ψ,
    { ext1 ⟨⟨⟨a, b⟩, c⟩, rfl : a = map_to.to_fun _ c⟩, refl },
    rw this,
    refine (hf i).snd.comp _,
    apply definable_of_subtype_val,
    exact definable.snd.comp definable.subtype.val
  end }

instance pfun.definable_sheaf : definable_sheaf S (X →. Y) :=
show definable_sheaf S (X → roption Y), by apply_instance

-- TODO: definable (∈)? but it needs a separatedness hypothesis on X
/-lemma definable_roption.mem : definable S ((∈) : X → roption X → Prop) :=
begin
end-/

lemma definable_roption.dom : definable S (roption.dom : roption X → Prop) :=
begin
  rw definable_fun,
  intros K φ hφ,
  exact hφ.fst
end

lemma definable_orelse_pure :
  definable S (roption.orelse_pure : roption X → X → X) :=
begin
  rw definable_iff_uncurry,
  rw definable_fun,
  intros K φ hφ,
  rw ←definable_yoneda at ⊢ hφ,
  let s := {k | (φ k).1.dom},
  apply definable_if _ s,
  { exact definable_roption.dom.comp (definable.fst.comp hφ) },
  { suffices : definable S (λ (p : s), (φ p.val).1.get p.property),
    { convert this,
      ext ⟨k, hk⟩,
      change dite _ _ _ = (φ k).fst.get hk,
      -- exact dif_neg hk,   -- bad binder type on `dif_neg`
      split_ifs,
      { refl },
      { refl } },               -- what happened here??
    rw definable_yoneda at hφ,
    exact hφ.1.snd },
  { suffices : definable S (λ (p : sᶜ), (φ p.val).2),
    { convert this,
      ext ⟨k, hk⟩,
      change dite _ _ _ = (φ k).snd,
      -- exact dif_neg hk,   -- bad binder type on `dif_neg`
      split_ifs,
      { exact false.elim (hk h) },
      { refl } },
    exact definable.snd.comp (hφ.comp definable.subtype.val) }
end

lemma definable_roption_map :
  definable S (roption.map : (X → Y) → roption X → roption Y) :=
begin
  rw definable_iff_uncurry,
  rw definable_fun,
  intros K φ hφ,
  refine ⟨hφ.2.fst, _⟩,
  change definable S (λ (p : {k | (φ k).2.dom}), (φ p.1).1 (pfun.as_subtype (prod.snd ∘ φ) p)),
  begin [defin]
    intro p,
    app,
    app, exact definable.fst.definable _,
    app, exact (definable_yoneda.mpr hφ).definable _,
    app, exact definable.subtype.val.definable _,
    var,
    app, exact hφ.2.snd.definable _, var
  end
end

end o_minimal
