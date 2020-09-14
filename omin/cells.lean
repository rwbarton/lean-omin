import o_minimal.o_minimal
import data.set.disjointed
import data.setoid.partition

namespace o_minimal

local notation R `^` n := fin n → R

variables {R : Type*} [DUNLO R]
variables (S : struc R) [definable_constants S] [is_definable_le S R]

def init {n} : R^(n+1) → R^n := λ x, x ∘ fin.cast_succ

namespace struc

def cell : Π {n}, set (R^n) → Prop
| 0     s := s = set.univ
| (n+1) s := ∃ (s₀ : set (R^n)) (h : cell s₀),
                  s = {x | (init x) ∈ s₀}
              ∨
              (∃ (f : R^n → R) (hf : def_fun S f),
                  s = {x | (init x) ∈ s₀ ∧ x (fin.last n) = f (init x)}
                ∨ s = {x | (init x) ∈ s₀ ∧ x (fin.last n) ∈ set.Ioi (f (init x))}
                ∨ s = {x | (init x) ∈ s₀ ∧ x (fin.last n) ∈ set.Iio (f (init x))})
              ∨
              (∃ (f g : R^n → R) (hf : def_fun S f) (hg : def_fun S g),
                (∀ x₀ ∈ s₀, f x₀ < g x₀) ∧
                  s = {x | (init x) ∈ s₀ ∧ x (fin.last n) ∈ set.Ioo (f (init x)) (g (init x))})

lemma init_definable (n : ℕ) :
  def_fun S (init : R^(n+1) → R^n) :=
begin
  sorry
end

lemma cell.definable : ∀ {n} (s : set (R^n)) (hs : S.cell s), def_set S s
| 0     s hs := by { cases hs, apply def_set_univ }
| (n+1) s hs :=
begin
  obtain ⟨s₀, hs₀, H|H|H⟩ := hs,
  { cases H,
    show def_set S (init ⁻¹' s₀), sorry },
  sorry,
  sorry,
end

def decomposition : Π {n} (C : set (set (R^n))), Prop
| 0     C := C = {set.univ}
| (n+1) C := C.finite ∧ setoid.is_partition C
            ∧ ∀ s ∈ C, S.cell s
            ∧ decomposition ((set.image init) '' C)

end struc

end o_minimal
