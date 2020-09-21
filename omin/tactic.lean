import data.list.alist
import .presheaf2

namespace o_minimal

variables {R : Type*} {S : struc R}

structure sect (Γ : Def S) (X : Type*) [definable_psh S X] :=
(to_fun : Γ → X)
(definable : definable_psh.definable to_fun)

infixr ` ⊢ `:10 := sect

def sect.precomp {Γ' Γ : Def S} {X : Type*} [definable_psh S X]
  (σ : Γ ⊢ X) (φ : Hom Γ' Γ) : Γ' ⊢ X :=
{ to_fun := σ.to_fun ∘ φ.to_fun,
  definable := definable_psh.definable_precomp φ σ.definable }

lemma begin_lem {X : Type*} [definable_psh S X] {x : X} :
  definable S x ↔ ∀ (Γ : Def S), definable_psh.definable (λ (γ : Γ), x) :=
sorry

lemma intro_lem₁ {X Y : Type*} [definable_psh S X] [definable_psh S Y]
  (f : X → Y) :
  (∀ (Γ : Def S), definable S (λ (γ : Γ), f)) ↔
  (∀ (Γ : Def S) (x : Γ → X), definable S x → definable S (λ (γ : Γ), f (x γ))) :=
sorry

lemma definable_fun' {Γ : Def S} {X Y : Type*} [definable_psh S X] [definable_psh S Y]
  {f : Γ → X → Y} : definable_psh.definable f ↔
  (∀ (Γ' : Def S) (π : Hom Γ' Γ) (g : Γ' ⊢ X),
   definable_psh.definable (λ γ_1, f (π.to_fun γ_1) (g.to_fun γ_1))) :=
begin
  sorry
end

lemma definable.app_ctx' {Γ : Def S} {X Y : Type*} [definable_psh S X] [definable_psh S Y]
  (f : Γ → X → Y) {hf : definable_psh.definable f} (x : Γ → X) {hx : definable_psh.definable x} :
  definable_psh.definable (λ γ, f γ (x γ)) :=
sorry

lemma definable_const {Γ : Def S} {X : Type*} [definable_psh S X] {x : X} :
  definable S x → definable_psh.definable (λ (_ : Γ), x) :=
sorry

end o_minimal

namespace tactic.interactive

open tactic
open interactive interactive.types

meta def defin_start : tactic unit :=
`[rw o_minimal.begin_lem, intro Γ]

/-- Return the variable representing the definable context. -/
meta def guess_ctx_var : tactic expr :=
do `(o_minimal.definable_psh.definable (λ (_ : ↥%%var), _)) ← target,
   -- trace var,
   return var

/-- Return a list of "definable" variables along with their processed types. -/
meta def guess_defin_vars (ctx_var : expr) : tactic (list (expr × expr)) :=
do l ← local_context,
   -- some kind of moption_map?
   l ← l.mmap (λ var,
     (do `(o_minimal.sect %%ctx_var %%ty) ← infer_type var,
         return $ some (var, ty)) <|> return none),
   let l' := l.filter_map id,
   -- trace l',
   return l'

meta def guess_defin_vars' : tactic (list (expr × expr)) :=
guess_ctx_var >>= guess_defin_vars

/-- Goal should look like
  ⊢ definable_psh.definable (λ γ, λ x, e)
We want to "intro" `x` as a definable variable, and leave
  ⊢ definable_psh.definable (λ γ, e)
as the new goal.

Strategy:
By `definable_fun'` it's enough to check the new goal
for an arbitrary context extension π : Γ' → Γ and section x : Γ' ⊢ α.
However, we also have to move any existing definable variables from Γ to Γ'.
So, we proceed as follows:
* Identify the variables `γ` (`i_var`) and `Γ` (`ctx_var`) in the goal
  `definable_psh.definable (λ (γ : Γ), body)`.
  Here `body` is expected to be a function whose argument `x`
  we want to intro.
* Use `definable_fun'` but then intro only `Γ'` and `π`.
* For each existing definable variable `p`, we add a let binding
  `p' := p.precomp π`.
* Now intro the new variable `x` (`new_var`) as well, and build a new function
  (λ (γ' : Γ'), body' (x.to_fun γ')), by making the following replacements:
  - each old `p` becomes `p'`;
  - `i` becomes `i'`;
  - `Γ` becomes `Γ'`.
  The claim is that the new expression is well-typed and definitionally equal
  (in the context of the let-bound variables `p'`, ...) to the current goal.
  Moreover, it only mentions the new `Γ'` and `p'`.
* Now we cover our tracks:
  - clear the bodies of the let bindings `p'`, so that we can:
  - clear the old definable variables, `π`, and the old `Γ`.

The tactic reuses the same user-visible names for the new `Γ` and `γ`.
This is nice for interactive use, but not so nice for debugging the tactic.
In the latter case, add `name.append_after _ 1` when generating names.
-/
meta def defin_intro (var : parse ident_) : tactic unit :=
let trace : Π {α : Type} [has_to_tactic_format α] (a : α), tactic unit :=
  λ _ _ _, tactic.skip in       -- comment this for debugging
do `(o_minimal.definable_psh.definable %%f) ← target,
   ([i_var], body) ← open_n_lambdas f 1,
   ctx_var ← guess_ctx_var,
   trace i_var,
   trace body,
   `[rw definable_fun'],
   new_ctx_var ← tactic.intro ctx_var.local_pp_name,
   proj_var ← tactic.intro `π,
   defin_vars ← guess_defin_vars ctx_var,
   -- do something to them:
   -- * for each old variable `p`, create a new variable `p'`
   --   which is let-bound to `p.precomp π`
   defin_var_list ← defin_vars.mmap (λ ⟨dvar, dvar_ty⟩, do
     -- "let p' := p.precomp π,"
     new_body ← to_expr ``((%%dvar).precomp %%proj_var),
     new_dvar ← tactic.pose dvar.local_pp_name none new_body,
     return (sigma.mk dvar new_dvar)),
   new_i_type ← to_expr ``(↥%%new_ctx_var),
   new_i_var ← mk_local' i_var.local_pp_name f.binding_info new_i_type,
   -- * replace variables `p` → `p'` in `body`, and also the γ and Γ vars
   let var_map :=
     (defin_var_list.to_alist.insert i_var new_i_var).insert ctx_var new_ctx_var,
   let body' := body.replace (λ e _, do
     -- for "efficiency", first check whether we have a variable at all
     guard (e.is_local_constant),
     -- then, look up the whole expression in our map
     var_map.lookup e),
   -- do the actual intro
   new_var ← tactic.intro var,
   new_var' ← to_expr ``((%%new_var).to_fun %%new_i_var),
   new_f ← tactic.lambdas [new_i_var] (body'.subst new_var'),
   trace new_f,
   new_target ← to_expr
     ``(o_minimal.definable_psh.definable %%new_f),
   tactic.change new_target,
   -- for each defin var:
   -- * forget its let binding (so that we can do the `clear`s below)
   --   (using `clear_value` from mathlib's `tactic.core`)
   -- * clear the original variable
   tactic.clear_value (defin_var_list.map sigma.snd),
   defin_var_list.mmap (λ ⟨dvar, new_dvar⟩, do tactic.clear dvar),
   tactic.clear proj_var,
   tactic.clear ctx_var,
   return ()

/-- Goal should look like
 ⊢ definable_psh.definable (λ γ, f x)
and we want to produce
 ⊢ definable_psh.definable (λ γ, f)
 ⊢ definable_psh.definable (λ γ, x)
This is just `apply definable.app_ctx'`,
but Lean needs help with the unification problem.
-/
meta def defin_app : tactic unit :=
do `(o_minimal.definable_psh.definable %%e) ← target,
   ([i_var], body) ← open_n_lambdas e 1,
   (expr.app f x) ← pure body,
   f' ← tactic.lambdas [i_var] f,
   x' ← tactic.lambdas [i_var] x,
   `[apply o_minimal.definable.app_ctx' %%f' %%x'],
   return ()

/-- Goal should look like
 ⊢ definable_psh.definable (λ γ, p.to_fun γ)
where p : Γ ⊢ α. Just apply `sect.definable`.
-/
meta def defin_var : tactic unit :=
`[apply o_minimal.sect.definable]

end tactic.interactive

-- Now dress it up

meta def defin := tactic

meta instance : monad defin :=
show monad tactic, by apply_instance

meta instance : interactive.executor defin :=
{ config_type := unit,
  inhabited := by apply_instance,
  execute_with := λ _ tac, tactic.interactive.defin_start >> tac }

namespace defin

meta def execute (tac : defin unit) : tactic unit :=
tactic.interactive.defin_start >> tac

meta def step := @tactic.step   -- what does this even do
meta def istep := @tactic.istep -- ditto
meta def solve1 : defin unit → defin unit := tactic.solve1

open tactic

-- Tactic state display borrows liberally from
-- https://github.com/unitb/temporal-logic
-- file temporal_logic.tactic

/-- Replace any occurrences of `p.to_fun γ` with simply `p`.
This is rather crude, but these aren't expected to appear
outside the execution of a defin tactic. (More sophisticated
would be to process only those variables which are sections
over the context variable that appears in the goal.)
The resulting expression is intended to be used for display purposes. -/
meta def shorten (E : expr) : expr :=
E.replace $ λ e _, match e with
  | `(o_minimal.sect.to_fun %%p _) := some p
  | _ := none
end

meta structure hyp_data : Type :=
(crisp : bool)
(var : expr)
(ty : expr)
(val : option expr)

/-- Return information about a local hypothesis `l`. -/
meta def get_hyp_data (l : expr) : defin hyp_data :=
do ty ← infer_type l,
   val ← try_core (shorten <$> local_def_value l),
   match ty with
   | `(o_minimal.sect %%Γ %%ty') := return ⟨ff, l, shorten ty', val⟩
   | _ := return ⟨tt, l, shorten ty, val⟩
   end

meta def decl_to_fmt (s : tactic_state) (crisp : bool) (vs : list expr)
  (ty : expr) (val : option expr) : format :=
let vs' := format.join $ (vs.map s.format_expr).intersperse " ",
    t := s.format_expr ty,
    sep := if crisp then "::" else ":" in
match val with
| (some val) := format! "{vs'} {sep} {t} := {s.format_expr val}"
| none := format! "{vs'} {sep} {t}"
end

meta def goal_to_fmt (g : expr) : defin (thunk format) :=
do set_goals [g],
   s ← read,
   `(o_minimal.definable_psh.definable (λ (_ : ↥%%Γ), %%body)) ← target
     | pure (λ _, to_fmt s),
   lc ← local_context,
   ctx_var ← tactic.interactive.guess_ctx_var,
   dat ← (lc.filter (λ l, l ≠ ctx_var)).mmap get_hyp_data,
   return $ λ _, format.intercalate format.line
     [format.intercalate ("," ++ format.line) $ dat.map $ λ d,
        decl_to_fmt s d.crisp [d.var] d.ty d.val,
      format! "⊢ {s.format_expr (shorten body)} def"]

meta def save_info (p : pos) : defin unit :=
do gs ← get_goals,
   fmt ← gs.mmap goal_to_fmt,
   set_goals gs,
   tactic.save_info_thunk p (λ _,
     let header := if fmt.length > 1 then format! "{fmt.length} goals\n" else "",
         eval : thunk format → format := λ f, f () in
     if fmt.empty
       then "no goals"
       else format.join ((fmt.map eval).intersperse (format.line ++ format.line)))

namespace interactive

meta def swap := tactic.interactive.swap
meta def exact := tactic.interactive.exact
meta def solve1 : defin unit → defin unit := tactic.interactive.solve1

meta def intro := tactic.interactive.defin_intro
meta def app := tactic.interactive.defin_app
meta def var := tactic.interactive.defin_var

meta def trace_state : defin unit :=
do s ← read,
   trace s.to_format

end interactive

end defin

namespace o_minimal

variables {R : Type*} {S : struc R}

local infixr ` ⊢ `:10 := sect

example : definable S (λ p q, (q ∧ p) ∧ q) :=
begin
  defin_start,
  defin_intro p,
  defin_intro q,
  defin_app,
  swap,
  { defin_var },
  defin_app,
  { exact definable_const definable_and },
  defin_app,
  { defin_app,
    { exact definable_const definable_and },
    defin_var },
  { defin_var },
end

example : definable S (λ p q, (q ∧ p) ∧ q) :=
begin [defin]
  intro p,
  intro q,
  app,
  swap,
  { var },
  app,
  { exact definable_const definable_and },
  app,
  { app,
    { exact definable_const definable_and },
    var },
  { var },
end

#exit

-- stuff after this uses pi type instances, which we don't need yet

variables {Y : Type*} [definable_psh S Y] (y : Y)

--set_option trace.class_instances true
example : definable S (λ (X : set Y) (h : nonempty X), true) :=
begin
  defin_start, rw ←definable_yoneda, -- TODO: combine these

  -- "intro X",
  rw definable_fun', intros Γ' π p,
  -- now we need to pull back any variables mentioning Γ
  -- to use Γ' -- there aren't any yet ✓
  -- since that's done, we can dispose of the old context
  clear π Γ,
  rename Γ' → Γ,

  -- "intro x",
  rw definable_fun', intros Γ' π, -- don't intro q just yet
  -- this time we need to deal with p
  have : ∀ d, p.to_fun (π.to_fun d) = (p.precomp π).to_fun d := λ d, rfl,
  simp only [this],
  generalize H : (p.precomp π) = p', clear this H p, rename p' → p,
  -- okay, now it's safe to intro q
  intro q,
  -- dispose of old context again
  clear π Γ,
  rename Γ' → Γ,

  -- we're done with intros!
end

end o_minimal
