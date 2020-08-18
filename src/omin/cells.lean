import omin.ominimal

section omin

local notation R `^` n := fin n → R

variables {R : Type*} [nonempty R] [decidable_linear_order R] [densely_ordered R] [no_bot_order R] [no_top_order R]
variables (S : struc R) [definable_constants S] [definable_lt S]

def init {n} : R^(n+1) → R^n := λ x, x ∘ fin.cast_succ

namespace struc

def cell : Π {n}, set (R^n) → Prop
| 0     s := s.nonempty
| (n+1) s := ∃ (s₀ : set (R^n)) (h : cell s₀),
                  s = {x | (init x) ∈ s₀}
              ∨
              (∃ (f : R^n → R) (hf : S.definable_fun f),
                  s = {x | (init x) ∈ s₀ ∧ x (fin.last n) = f (init x)}
                ∨ s = {x | (init x) ∈ s₀ ∧ x (fin.last n) ∈ set.Ioi (f (init x))}
                ∨ s = {x | (init x) ∈ s₀ ∧ x (fin.last n) ∈ set.Iio (f (init x))})
              ∨
              (∃ (f g : R^n → R) (hf : S.definable_fun f) (hg : S.definable_fun g),
                (∀ x₀ ∈ s₀, f x₀ < g x₀) ∧
                  s = {x | (init x) ∈ s₀ ∧ x (fin.last n) ∈ set.Ioo (f (init x)) (g (init x))})

lemma cell.definable : ∀ {n} (s : set (R^n)) (hs : S.cell s), S.definable s
| 0     s hs := sorry
| (n+1) s hs :=
begin
  obtain ⟨s₀, hs₀, H|H|H⟩ := hs,
  sorry,
  sorry,
  sorry
end

end struc

end omin