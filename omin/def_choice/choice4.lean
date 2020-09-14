import o_minimal.examples.simple
import .choice3
import ..tame
import ..ultra

-- TODO: for lean core library: modify binder type of dif_pos etc.:
-- lemma {u} dif_pos' {c : Prop} {h : decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : dite c t e = t hc := dif_pos hc
-- Avoids the need (unexplained) for `open_locale classical` below.

-- The comments above are obsolete, but this still seems like a good idea.

open o_minimal

variables {R : Type*} [OQM R]
variables {X : set R}

local notation `½` := (1/2 : ℚ)

lemma lt_of_self_add_lt {a b : R} (h : a + a < b + b) : a < b :=
begin
  contrapose! h,
  exact add_le_add h h
end

lemma average_between {a b : R} (hab : a < b) : ½ • (a + b) ∈ set.Ioo a b :=
begin
  split,
  { apply lt_of_self_add_lt,
    rw half_add_half,
    apply add_lt_add_left hab },
  { apply lt_of_self_add_lt,
    rw half_add_half,
    apply add_lt_add_right hab }
end

local attribute [instance] one

lemma one_pos : (0 : R) < 1 :=
classical.some_spec _

lemma chosen_one_mem (nX : X.nonempty) (tX : tame X) :
  (chosen_one X).get nX ∈ X :=
begin
  -- Administrative nonsense; also handle the trivial "has least" case.
  dsimp [chosen_one, roption.map, roption.orelse_pure, function.comp],
  split_ifs with hleast hinf hsup hsup hsup;
    try { dsimp [the_least, the_inf, the_sup] at * },
  { obtain ⟨e, he⟩ := hleast,
    rw get_pfun_of_rel_eq_of_rel he,
    exact he.1 },
  any_goals {
    obtain ⟨a, ha⟩ := hinf,
    simp only [get_pfun_of_rel_eq_of_rel ha] at ⊢ hsup },
  any_goals {
    obtain ⟨b, hb⟩ := hsup,
    rw get_pfun_of_rel_eq_of_rel hb, try { clear hsup } },
  -- Now handle the remaining cases, respectively those yielding
  -- (a+b)/2, b-1, a+1, 0
  -- where a = inf X, b = sup Y, Y = {b | a < b ∧ (a, b) ⊆ X}.
  { have hab : a < b,
    { obtain ⟨b', hb'⟩ := hb.nonempty,
      exact lt_of_lt_of_le hb'.1 (hb.1 hb') },
    have mid : ½ • (a + b) ∈ set.Ioo a b := average_between hab,
    obtain ⟨c, hc, hmc⟩ := (lt_is_lub_iff hb).mp mid.2,
    apply hc.2,
    exact ⟨mid.1, hmc⟩ },
  { let Y := {b | a < b ∧ set.Ioo a b ⊆ X},
    change ¬ ∃ b, is_lub Y b at hsup,
    have nY : Y.nonempty,
    { have := above_inf tX ha (λ H, hleast ⟨a, H, ha.1⟩),
      -- TODO: for_mathlib: ^ is_glb ∧ mem → is_least
      rw mem_above_iff at this,
      obtain ⟨b, hab, hb⟩ := this,
      exact ⟨b, hab, hb⟩ },
    have tY : tame Y,
    { refine tame_of_def simple_struc _,
      apply def_set.and,
      { exact definable_lt def_fun_const def_fun.id },
      { apply def_set.forall,
        apply def_set.imp,
        { apply def_set.and,
          { exact definable_lt def_fun_const def_fun.snd },
          { exact definable_lt def_fun.snd def_fun.fst } },
        { exact def_fun.snd.preimage tX.def_set } } },
    have := mt (exists_tSup tY nY) hsup,
    rw not_bdd_above_iff at this,
    obtain ⟨b, hb₁, hb₂⟩ := this (a + 1),
    apply hb₁.2 ⟨lt_add_of_pos_right _ one_pos, hb₂⟩ },
  { obtain ⟨c, hc₁, hc₂⟩ := (lt_is_lub_iff hb).mp (sub_lt_self b one_pos),
    exact hc₁ hc₂ },
  { let Y := {b | set.Iio b ⊆ X},
    change ¬ ∃ b, is_lub Y b at hsup,
    have nY : Y.nonempty,
    { have := mt (exists_tInf tX nX) hinf,
      exact (contains_Iio_or_bdd_below tX).resolve_right this },
    have tY : tame Y,
    { refine tame_of_def simple_struc _,
      apply def_set.forall,
      apply def_set.imp,
      { exact definable_lt def_fun.snd def_fun.fst },
      { exact def_fun.snd.preimage tX.def_set } },
    have := mt (exists_tSup tY nY) hsup,
    rw not_bdd_above_iff at this,
    obtain ⟨b, hb₁, hb₂⟩ := this 0,
    apply hb₁ hb₂ }
end

