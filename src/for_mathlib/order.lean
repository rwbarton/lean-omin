import order.bounded_lattice

@[elab_as_eliminator]
def with_top.rec_top_coe {α : Type*} {C : with_top α → Sort*} (h₁ : C ⊤) (h₂ : Π (a : α), C a) :
  Π (n : with_top α), C n :=
option.rec h₁ h₂

@[elab_as_eliminator]
def with_bot.rec_bot_coe {α : Type*} {C : with_bot α → Sort*} (h₁ : C ⊥) (h₂ : Π (a : α), C a) :
  Π (n : with_bot α), C n :=
option.rec h₁ h₂
