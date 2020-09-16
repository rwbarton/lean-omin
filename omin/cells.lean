import o_minimal.o_minimal
import data.set.disjointed
import data.setoid.partition

namespace o_minimal

variables {R : Type*} [DUNLO R]
variables (S : struc R) [definable_constants S] [is_definable_le S R]

namespace struc

def cell : Π {n}, set (finvec n R) → Prop
| 0     s := s = set.univ
| (n+1) s := ∃ (s₀ : set (finvec n R)) (h : cell s₀),
                  s = {x | x.init ∈ s₀}
              ∨
              (∃ (f : finvec n R → R) (hf : def_fun S f),
                  s = {x | x.init ∈ s₀ ∧ x (fin.last n) = f x.init}
                ∨ s = {x | x.init ∈ s₀ ∧ x (fin.last n) ∈ set.Ioi (f x.init)}
                ∨ s = {x | x.init ∈ s₀ ∧ x (fin.last n) ∈ set.Iio (f x.init)})
              ∨
              (∃ (f g : finvec n R → R) (hf : def_fun S f) (hg : def_fun S g),
                (∀ x₀ ∈ s₀, f x₀ < g x₀) ∧
                  s = {x | x.init ∈ s₀ ∧ x (fin.last n) ∈ set.Ioo (f x.init) (g x.init)})

lemma init_definable (n : ℕ) :
  def_fun S (finvec.init : finvec (n+1) R → finvec n R) :=
begin
  sorry
end

lemma cell.definable : ∀ {n} (s : set (finvec n R)) (hs : S.cell s), def_set S s
| 0     s hs := by { cases hs, apply def_set_univ }
| (n+1) s hs :=
begin
  obtain ⟨s₀, hs₀, H|H|H⟩ := hs,
  { cases H,
    show def_set S (finvec.init ⁻¹' s₀), sorry },
  sorry,
  sorry,
end

def decomposition : Π {n} (C : set (set (finvec n R))), Prop
| 0     C := C = {set.univ}
| (n+1) C := C.finite ∧ setoid.is_partition C
            ∧ ∀ s ∈ C, S.cell s
            ∧ decomposition ((set.image finvec.init) '' C)

end struc

end o_minimal
