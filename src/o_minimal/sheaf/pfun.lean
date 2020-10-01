import data.pfun
import o_minimal.sheaf.covers

section orelse_pure

open_locale classical

noncomputable def roption.orelse_pure {α : Type*} (x : roption α) (y : α) :=
if h : x.dom then x.get h else y

-- TODO: Is this actually useful?
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

-- TODO: move this, and generalize?
lemma definable_eq {Z : Type*} [has_coordinates R Z] [definable_rep S Z] :
  definable S ((=) : Z → Z → Prop) :=
begin
  rw definable_iff_uncurry,
  rw definable_fun,
  intros K φ hφ,
  rw definable_rep.eq at hφ,
  exact def_set_eq (def_fun.fst.comp hφ) (def_fun.snd.comp hφ)
end

-- TODO: generalize to `Z` with definable equality?
lemma definable_roption.mem {Z : Type*} [has_coordinates R Z] [definable_rep S Z] :
  definable S ((∈) : Z → roption Z → Prop) :=
begin
  rw definable_iff_uncurry,
  rw definable_fun,
  intros K φ hφ,
  let K' := {k | (φ k).2.dom},
  have dK' : def_set S {k : ↥K | (φ k).snd.dom} := hφ.2.fst,
  letI : definable_rep S K' :=
    subtype.definable_rep (definable_iff_def_set.mpr dK'),
  have : definable S (λ (k' : {k | (φ k).2.dom}), (φ k'.val).1 = (φ k'.val).2.get k'.property),
  { let ψ₁ : K' → Z := λ k', (φ k'.val).1,
    have dψ₁ : definable S ψ₁ :=
      (definable_yoneda.mpr hφ.1).comp definable.subtype.val,
    let ψ₂ : K' → Z := λ k', (φ k'.val).2.get k'.property,
    have dψ₂ : definable S ψ₂ := hφ.2.snd,
    let ψ : K' → Z × Z := λ k', (ψ₁ k', ψ₂ k'),
    suffices dψ : definable S ψ,
    { have : definable S (λ (p : Z × Z), p.1 = p.2) :=
        definable_iff_uncurry.mp definable_eq,
      exact this.comp dψ },
    -- TODO: lemma
    begin [defin]
      intro k,
      app, app, exact definable.prod_mk.definable _,
      app, exact dψ₁.definable _, var,
      app, exact dψ₂.definable _, var
    end },
  rw definable_iff_def_set at this,
  convert def_fun.image def_fun_subtype_val this,
  { ext k,
    rw set.mem_image,
    conv_lhs { rw set.mem_def },
    simp only [function.uncurry, roption.mem_eq, exists_and_distrib_right,
      function.comp_app, exists_eq_right, subtype.exists,
      subtype.coe_mk, subtype.val_eq_coe],
    apply exists_congr, intro h,
    apply eq_comm },
  -- TODO: avoid this side goal somehow
  { exact dK' }
end

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

instance pfun.definable_sheaf : definable_sheaf S (X →. Y) :=
show definable_sheaf S (X → roption Y), by apply_instance

lemma definable_pfun_of_graph {Z : Type*} [has_coordinates R Z] [definable_rep S Z]
  {f : X →. Z} (df : definable S {p : X × Z | p.2 ∈ f p.1}) : definable S f :=
begin
  rw definable_fun,
  intros K φ hφ,
  rw ←definable_yoneda at hφ,
  have d : def_set S (pfun.dom (f ∘ φ)),
  { suffices : def_set S {k : K | ∃ z : Z, z ∈ f (φ k)},
    { convert this,
      ext k,
      simp [pfun.mem_dom] },
    apply def_set.exists,
    let ψ : K × Z → X × Z := λ p, (φ p.1, p.2),
    have dψ : definable S ψ,
    -- TODO: The tactic mode should be overkill for this
    begin [defin]
      intro p,
      app, app, exact definable.prod_mk.definable _,
      app, exact hφ.definable _,
      app, exact definable.fst.definable _,
      var,
      app, exact definable.snd.definable _,
      var,
    end,
    exact definable_iff_def_set.mp (df.comp dψ) },
  refine ⟨d, _⟩,
  apply definable_of_graph,
  let ψ : pfun.dom (f ∘ φ) × Z → X × Z := λ p, (φ p.1.val, p.2),
  have dψ : definable S ψ,
  begin [defin]                 -- TODO: ... and this
    intro p,
    app, app, exact definable.prod_mk.definable _,
    app, exact hφ.definable _,
    app, exact definable.subtype.val.definable _,
    app, exact definable.fst.definable _,
    var,
    app, exact definable.snd.definable _,
    var,
  end,
  convert df.comp dψ,
  ext ⟨⟨k, h⟩, z⟩,
  change (f (φ k)).get _ = z ↔ z ∈ f (φ k),
  rw [roption.get_eq_iff_eq_some, roption.eq_some_iff]
end

end o_minimal
