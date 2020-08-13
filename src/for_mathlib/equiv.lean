import tactic.equiv_rw
import data.equiv.basic

variables {α β : Sort*}

lemma equiv.exists_congr_left' {p : α → Prop} (f : α ≃ β) :
  (∃x, p x) ↔ (∃y, p (f.symm y)) :=
⟨λ ⟨x, h⟩, ⟨f x, by rwa f.symm_apply_apply⟩, λ ⟨y, h⟩, ⟨f.symm y, h⟩⟩

lemma equiv.exists_congr_left {p : β → Prop} (f : α ≃ β) :
  (∃x, p (f x)) ↔ (∃y, p y) :=
f.symm.exists_congr_left'.symm

