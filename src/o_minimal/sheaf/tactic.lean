import data.list.alist
import o_minimal.sheaf.basic

/-
Tactics for proving goals of the form
  ⊢ definable S e
notably including the case where `e` is a function.

First we implement some ordinary `tactic.interactive` tactics
with names of the form `defin_foo`.
Then we wrap them in a special `defin` tactic mode.
-/

namespace tactic

namespace o_minimal

/-- Return the local constant (hopefully) representing the definable context. -/
meta def guess_ctx_ty : tactic expr :=
do `(o_minimal.definable_sheaf.definable (λ (_ : ↥%%var), _)) ← target,
   return var

/-- Return a list of the "definable" variables in the local context. -/
meta def guess_defin_vars (ctx_ty : expr) : tactic (list expr) :=
do l ← local_context,
   -- some kind of moption_map?
   l ← l.mmap (λ var,
     (do `(o_minimal.definable_sheaf.sect %%ctx_ty %%ty) ← infer_type var,
         return $ some var) <|> return none),
   return (l.filter_map id)

end o_minimal

namespace interactive
setup_tactic_parser

open tactic.o_minimal

/- TODO:
* more Lean-like argument parsing, e.g., `intros p q`
* probably `app` should automatically try calling `var`, say
* what to do about constants? need database of some kind
* more tactics?
-/

meta def defin_start : tactic unit :=
`[refine o_minimal.definable.mk (λ Γ, _)]

/-- Goal should look like
  ⊢ definable_sheaf.definable (λ i, λ x, e)
We want to "intro" `x` as a definable variable, and leave
  ⊢ definable_sheaf.definable (λ i, e)
as the new goal.

Strategy:
By `definable_fun_iff` it's enough to check the new goal
for an arbitrary context extension `π : Γ' ⟶ Γ` and section `x : sect Γ' α`.
However, we also have to move any existing definable variables from `Γ` to `Γ'`.
So, we proceed as follows:
* Identify the variables `i` (`i_var`) and `Γ` (`ctx_var`) in the goal
  `definable_sheaf.definable (λ (i : Γ), body)`.
  Here `body` is expected to be a function whose argument `x`
  we want to intro.
* Use `definable_fun_iff` but then intro only `Γ'` and `π`.
* For each existing definable variable `p`, we add a let binding
  `p' := p.precomp π`.
* Now intro the new variable `x` (`new_var`) as well, and build a new function
  `λ (i' : Γ'), body' (x.to_fun γ')`, by making the following replacements:
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
do `(o_minimal.definable_sheaf.definable %%f) ← target,
   ([i_var], body) ← open_n_lambdas f 1,
   -- `body` might not be a lambda yet, e.g., `function.curry`.
   -- Reduce it to whnf in hopes of making it a lambda.
   -- This won't do anything if it was a lambda already.
   -- It might not always succeed, e.g., in the case of `and`.
   body ← whnf body,
   ctx_var ← guess_ctx_ty,
   trace i_var,
   trace body,
   `[refine o_minimal.definable_sheaf.definable_fun_iff.mpr _],
   new_ctx_var ← tactic.intro ctx_var.local_pp_name,
   proj_var ← tactic.intro `π,
   defin_vars ← guess_defin_vars ctx_var,
   -- do something to them:
   -- * for each old variable `p`, create a new variable `p'`
   --   which is let-bound to `p.precomp π`
   defin_var_list ← defin_vars.mmap (λ dvar, do
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
   new_target ← to_expr ``(o_minimal.definable_sheaf.definable %%new_f),
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
 ⊢ definable_sheaf.definable (λ i, f x)
and we want to produce
 ⊢ definable_sheaf.definable (λ i, f)
 ⊢ definable_sheaf.definable (λ i, x)
This is just `apply definable_sheaf.definable_app`,
but Lean needs help with the unification problem.
-/
meta def defin_app : tactic unit :=
do `(o_minimal.definable_sheaf.definable %%e) ← target,
   ([i_var], body) ← open_n_lambdas e 1,
   (expr.app f x) ← pure body,
   f' ← tactic.lambdas [i_var] f,
   x' ← tactic.lambdas [i_var] x,
   `[refine o_minimal.definable_sheaf.definable_app %%f' %%x'],
   return ()

/-- Goal should look like
 ⊢ definable_sheaf.definable (λ i, p.to_fun i)
where p : Γ ⊢ α. Just apply `sect.definable`.
-/
meta def defin_var : tactic unit :=
`[refine o_minimal.definable_sheaf.sect.definable _]

end interactive

end tactic

meta def defin := tactic

meta instance : monad defin :=
show monad tactic, by apply_instance

meta instance : interactive.executor defin :=
{ config_type := unit,
  inhabited := by apply_instance,
  execute_with := λ _ tac, tactic.interactive.defin_start >> tac }

namespace defin

-- TODO:
-- * tactic display not quite done (need `compact`)

meta def step := @tactic.step
meta def istep := @tactic.istep
meta def solve1 : defin unit → defin unit := tactic.solve1

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
  | `(o_minimal.definable_sheaf.sect.to_fun %%p _) := some p
  | _ := none
end

section display

open tactic

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
   | `(o_minimal.definable_sheaf.sect %%Γ %%ty') := return ⟨ff, l, shorten ty', val⟩
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
   `(o_minimal.definable_sheaf.definable (λ (_ : ↥%%Γ), %%body)) ← target
     | pure (λ _, to_fmt s),
   lc ← local_context,
   ctx_var ← tactic.o_minimal.guess_ctx_ty,
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

end display

namespace interactive

meta def swap := tactic.interactive.swap
meta def exact := tactic.interactive.exact
meta def solve1 : defin unit → defin unit := tactic.interactive.solve1

meta def intro := tactic.interactive.defin_intro
meta def app := tactic.interactive.defin_app
meta def var := tactic.interactive.defin_var

/-- Display the actual, underlying tactic state. -/
meta def trace_state : defin unit :=
do s ← tactic.read,
   tactic.trace s.to_format

end interactive

end defin

namespace o_minimal

variables {R : Type*} [S : struc R]
variables {X Y Z : Type*} [definable_sheaf S X] [definable_sheaf S Y] [definable_sheaf S Z]

example : definable S (@function.curry X Y Z) :=
begin [defin]
  intro f,
  intro x,
  intro y,
  app,
  { var },
  { exact ⟨x.definable, y.definable⟩ }
end

end o_minimal
