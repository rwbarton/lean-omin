import order.filter.at_top_bot
import o_minimal.o_minimal

-- More facts about tame sets.

open o_minimal

variables {R : Type*} [DUNLO R]

lemma ball_or {α : Type*} (p q r : α → Prop) :
  (∀ a, (p a ∨ q a) → r a) ↔ (∀ a, p a → r a) ∧ (∀ a, q a → r a) :=
⟨λ H, ⟨λ a h, H a (or.inl h), λ a h, H a (or.inr h)⟩,
 λ H a o, o.cases_on (H.1 a) (H.2 a)⟩

lemma exists_tInf {s : set R} (ts : tame s) (ne : s.nonempty) (bdd : bdd_below s) :
  ∃ m, is_glb s m :=
begin
  revert ne bdd,
  refine tame.induction _ _ ts; clear ts s,
  { rintro ⟨_, ⟨⟩⟩ },
  { rintros s i hi IH - bdd,    -- `ne` can never be useful at this point.
    have bdd' : bdd_below s := bdd.mono (by simp),
    induction hi with r a b a b hab; clear i,
    -- We used `induction` because `cases` does too much unfolding.
    -- Unfortunately `induction` does not generate `case` tags.
    -- In two cases, the new set is obviously not bounded below;
    -- dispose of those first.
    -- TODO: Make these two cases lemmas (for `order.bounds`).
    swap 2,                     -- Iii
    { exfalso,
      rcases bdd with ⟨z, hz⟩,
      obtain ⟨y, hy : y < z⟩ := no_bot z,
      exact not_le_of_lt hy (hz (by simp)) },
    swap 3,                     -- Iio
    { exfalso,
      rcases bdd with ⟨z, hz⟩,
      obtain ⟨c, hc : c < b⟩ := no_bot b,
      obtain ⟨y, hy : y < min c z⟩ := no_bot (min c z),
      refine not_le_of_lt (lt_of_lt_of_le hy (min_le_right _ _)) (hz (or.inl _)),
      calc y < min c z : hy
       ...   ≤ c       : min_le_left _ _
       ...   < b       : hc },
    -- In the remaining goals we'll do case analysis on whether
    -- `s` is empty (and thus can be ignored) or nonempty (and thus we can use IH).
    all_goals {
      clear bdd,
      rcases set.eq_empty_or_nonempty s with rfl|ne';
      [ { clear IH bdd', simp only [set.union_empty] },
        { specialize IH ne' bdd', clear ne' bdd', cases IH with l IH }] },
    { exact ⟨_, is_glb_singleton⟩ },
    { exact ⟨_, is_glb.union is_glb_singleton IH⟩ },
    { exact ⟨_, is_glb_Ioi⟩ },
    { exact ⟨_, is_glb.union is_glb_Ioi IH⟩ },
    { exact ⟨_, is_glb_Ioo hab⟩ },
    { exact ⟨_, is_glb.union (is_glb_Ioo hab) IH⟩ } }
end

-- TODO: Make this not a copy&paste of above.
lemma exists_tSup {s : set R} (ts : tame s) (ne : s.nonempty) (bdd : bdd_above s) :
  ∃ m, is_lub s m :=
begin
  revert ne bdd,
  refine tame.induction _ _ ts; clear ts s,
  { rintro ⟨_, ⟨⟩⟩ },
  { rintros s i hi IH - bdd,    -- `ne` can never be useful at this point.
    have bdd' : bdd_above s := bdd.mono (by simp),
    induction hi with r a b a b hab; clear i,
    -- We used `induction` because `cases` does too much unfolding.
    -- Unfortunately `induction` does not generate `case` tags.
    -- In two cases, the new set is obviously not bounded above;
    -- dispose of those first.
    -- TODO: Make these two cases lemmas (for `order.bounds`).
    swap 2,                     -- Iii
    { exfalso,
      rcases bdd with ⟨z, hz⟩,
      obtain ⟨y, hy : y > z⟩ := no_top z,
      exact not_le_of_lt hy (hz (by simp)) },
    swap 2,                     -- Ioi
    { exfalso,
      rcases bdd with ⟨z, hz⟩,
      obtain ⟨c, hc : c > a⟩ := no_top a,
      obtain ⟨y, hy : y > max c z⟩ := no_top (max c z),
      refine not_le_of_lt (lt_of_le_of_lt (le_max_right _ _) hy) (hz (or.inl _)),
      calc y > max c z : hy
       ...   ≥ c       : le_max_left _ _
       ...   > a       : hc },
    -- In the remaining goals we'll do case analysis on whether
    -- `s` is empty (and thus can be ignored) or nonempty (and thus we can use IH).
    all_goals {
      clear bdd,
      rcases set.eq_empty_or_nonempty s with rfl|ne';
      [ { clear IH bdd', simp only [set.union_empty] },
        { specialize IH ne' bdd', clear ne' bdd', cases IH with l IH }] },
    { exact ⟨_, is_lub_singleton⟩ },
    { exact ⟨_, is_lub.union is_lub_singleton IH⟩ },
    { exact ⟨_, is_lub_Iio⟩ },
    { exact ⟨_, is_lub.union is_lub_Iio IH⟩ },
    { exact ⟨_, is_lub_Ioo hab⟩ },
    { exact ⟨_, is_lub.union (is_lub_Ioo hab) IH⟩ } }
end

/-- X ↦ inf X as a partial function. Defined when X is tame, nonempty and bounded below. -/
noncomputable def tInf : set R →. R :=
λ X, { dom := tame X ∧ X.nonempty ∧ bdd_below X, get := λ h, classical.some (exists_tInf h.1 h.2.1 h.2.2) }

/-- X ↦ inf X as a partial function. Defined when X is tame, nonempty and bounded above. -/
noncomputable def tSup : set R →. R :=
λ X, { dom := tame X ∧ X.nonempty ∧ bdd_above X, get := λ h, classical.some (exists_tSup h.1 h.2.1 h.2.2) }
