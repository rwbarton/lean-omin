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

namespace o_minimal

variables {R : Type*} [S : struc R]
variables {X Y : Type*} [definable_sheaf S X] [definable_sheaf S Y]

example : definable S (λ (f : X → X) (x : X), f (f x)) :=
begin
  defin_start,
  defin_intro f,
  defin_intro x,
  defin_app,
  { defin_var },
  { defin_app,
    { defin_var },
    { defin_var } }
end

lemma definable.prod_mk : definable S (@prod.mk X Y) :=
begin
  defin_start,
  defin_intro x,
  defin_intro y,
  exact ⟨x.definable, y.definable⟩
end

example : definable S (λ (x : X), (x, x)) :=
begin
  defin_start,
  defin_intro x,
  defin_app,
  defin_app,
  apply definable.prod_mk.definable,
  defin_var,
  defin_var
end

end o_minimal
