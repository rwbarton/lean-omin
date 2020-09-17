import o_minimal.coordinates
import o_minimal.structure

-- Stripped-down version of `o_minimal.definable`
-- without implicit definability hypotheses on the types.

universe u

namespace o_minimal

open_locale finvec

variables {R : Type u} (S : struc R)

variables {X : Type*} [has_coordinates R X]
variables {Y : Type*} [has_coordinates R Y]

def struc.def_coords (s : set X) : Prop :=
S.definable (coords R '' s)

namespace struc.def_coords

variables {S}

lemma diag (dX : S.def_coords (set.univ : set X)) :
  S.def_coords {p : X × X | p.1 = p.2} :=
begin
  unfold struc.def_coords,
  convert S.definable_inter (S.definable_prod_rn dX) S.definable_diag_rn,
  refine set.ext (finvec.rec (λ v w, _)),
  have :
    (∃ (x : X), coords R x = v ∧ coords R x = w) ↔
    v ∈ coordinate_image R X ∧ v = w,
  { split,
    { rintros ⟨x, rfl, rfl⟩, exact ⟨⟨x, rfl⟩, rfl⟩ },
    { rintros ⟨⟨x, rfl⟩, rfl⟩, exact ⟨x, rfl, rfl⟩ } },
  simp,
  dsimp,
  simpa [finvec.append.inj_iff]
end

lemma reindex (dX : S.def_coords (set.univ : set X)) {f : X → Y} (hf : is_reindexing R f)
  {s : set Y} (ds : S.def_coords s) : S.def_coords (f ⁻¹' s) :=
begin
  cases hf with fσ hf,
  unfold struc.def_coords,
  -- The preimage f ⁻¹' s, as a subset of the Rⁿ in which X lives,
  -- is the intersection of X with the preimage of s under the reindexing.
  convert S.definable_inter dX (S.definable_reindex fσ ds),
  ext z,
  suffices : (∃ (x : X), f x ∈ s ∧ coords R x = z) ↔
    z ∈ set.range (@coords R X _) ∧ ∃ (y : Y), y ∈ s ∧ coords R y = z ∘ fσ,
  { simpa },
  -- TODO: funext'd version of `is_reindexing.hf`
  replace hf : ∀ (x : X), coords R x ∘ fσ = coords R (f x) := λ x, funext (λ i, (hf x i)),
  split,
  { rintro ⟨x, hfx, rfl⟩,
    refine ⟨set.mem_range_self _, f x, hfx, (hf x).symm⟩ },
  { rintro ⟨⟨x, rfl⟩, y, hy, H⟩,
    rw hf x at H,
    replace hf := injective_coords _ H,
    subst y,
    exact ⟨x, hy, rfl⟩ }
end

lemma «exists» {s : X → Y → Prop} (ds : S.def_coords {p : X × Y | s p.1 p.2}) :
  S.def_coords {x | ∃ y, s x y} :=
begin
  unfold struc.def_coords at ⊢ ds,
  convert S.definable_proj ds using 1,
  ext x,
  rw [set.image_image],
  simp
end

lemma inter {s t : set X} (ds : S.def_coords s) (dt : S.def_coords t) :
  S.def_coords (s ∩ t) :=
begin
  unfold struc.def_coords,
  convert S.definable_inter ds dt,
  simp [set.image_inter (injective_coords X)]
end

lemma prod_univ (dX : S.def_coords (set.univ : set X)) (dY : S.def_coords (set.univ : set Y)) :
  S.def_coords (set.univ : set (X × Y)) :=
begin
  unfold struc.def_coords,
  convert S.definable_external_prod dX dY,
  refine set.ext (finvec.rec (λ v w, _)),
  simp [finvec.append.inj_iff, finvec.append_mem_prod_iff]
end

end struc.def_coords

end o_minimal
