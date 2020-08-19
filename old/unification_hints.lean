-- Earlier experiments with bundled definable types and unification hints.

/-
@[unify] def Def_hint {X Y Z : Def S} : unification_hint :=
{ pattern := ↥Z ≟ (↥X × ↥Y),
  constraints := [Z ≟ X.prod Y] }

This unification hint lets us write X × Y in place of X.prod Y
in simple situations but it fails when it would need to be applied recursively:

type mismatch at application
  preimage q
term
  q
has type
  (↥X × ↥Z) × ↥Y → ↥X × ↥Y : Type u
but is expected to have type
  ↥?m_3 → ↥X × ↥Y : Type (max ? u)
state:
R : Type u,
S : struc R,
X Y Z : Def S,
g : ↥Y → ↥Z,
hg : def_fun g,
f : ↥X → ↥Y,
hf : def_fun f,
q : (↥X × ↥Z) × ↥Y → ↥X × ↥Y := λ (p : (↥X × ↥Z) × ↥Y), (p.fst.fst, p.snd),
this : is_reindexing R q
⊢ def_set {x : ↥((X.prod Z).prod Y) | f x.fst.fst = x.snd}

We need to solve ↥?m_3 = (↥X × ↥Z) × ↥Y
but it is not (yet) of the form ↥?m_3 = ↥A × ↥B
because first we need to figure out that
we should solve ↥A = ↥X × ↥Z by taking A = X.prod Z.
-/

/-
@[unify] def Def_hint {α β : Type u} {A B Z : Def.{u} S} : unification_hint :=
{ pattern := ↥Z ≟ (α × β),
  constraints := [↥A ≟ α, ↥B ≟ β, Z ≟ A.prod B] }

This ought to solve the problem above:

  ↥?m_3 ≟ (↥X × ↥Z) × ↥Y
  [↥?A ≟ ↥X × ↥Z, ↥?B ≟ ↥Y, ?m_3 ≟ ?A.prod ?B]
  [↥?A₁ ≟ ↥X, ↥?A₂ = ↥Z, ?A = ?A₁.prod ?A₂, ↥?B ≟ ↥Y, ?m_3 ≟ ?A.prod ?B]
  A₁ = X, A₂ = Z, A = X.prod Z, B = Y, ?m_3 = (X.prod Z).prod Y

For some reason it doesn't work;
maybe the elaborator doesn't want to introduce new metavariables?

How is this handled in Coq?
-/
