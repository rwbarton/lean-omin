import .presheaf2

universes v u

namespace o_minimal

variables {R : Type} (S : struc R)

class psh' (X : Type v) :=
(definable : Π {K : Def S}, (K → X) → Sort v)
-- restriction
-- coherence

instance (X : Type) [definable_psh S X] : psh' S X :=
{ definable := λ K f, definable_psh.definable f }

instance Type.psh' : psh' S Type :=
{ definable := λ K X, Π {L : Def S} (z : Hom L K), (Π l, X (z l)) → Prop }
-- plus coherence

instance function.psh' (X : Type) (Y : Type 1) [psh' S X] [psh' S Y] : psh' S (X → Y) :=
{ definable := λ K Φ, Π {L : Def.{0} S} (z : Hom L K) (f : L → X),
  psh'.definable f → psh'.definable (λ l, Φ (z l) (f l)) }
-- plus coherence

instance Pi.psh' (X : Type) [psh' S X] (Y : X → Type) : psh' S (Π (x : X), Y x) :=
sorry

end o_minimal
