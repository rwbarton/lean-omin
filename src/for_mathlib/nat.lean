/-- Recursor for `nat` that uses `n+1` rather than `n.succ` in the inductive step. -/
@[elab_as_eliminator]
def nat.rec_plus_one {C : ℕ → Sort*} (h₁ : C 0) (h₂ : Π (n : ℕ), C n → C (n+1)) : Π n, C n :=
nat.rec h₁ h₂
