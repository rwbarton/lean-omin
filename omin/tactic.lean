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
--   trace var,
   return var

/-- Return a list of "definable" variables along with their processed types. -/
meta def guess_defin_vars (ctx_var : expr) : tactic (list (expr × expr)) :=
do l ← local_context,
   -- some kind of moption_map?
   l ← l.mmap (λ var,
     (do `(o_minimal.sect %%ctx_var %%ty) ← infer_type var,
         return $ some (var, ty)) <|> return none),
   let l' := l.filter_map id,
   trace l',
   return l'

meta def guess_defin_vars' : tactic (list (expr × expr)) :=
guess_ctx_var >>= guess_defin_vars

meta def defin_intro (var : parse ident_) : tactic unit :=
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
   -- * replace variables `p` → `p'` in `body`, and also the i var
   new_i_type ← to_expr ``(↥%%new_ctx_var),
   new_i_var ← mk_local' i_var.local_pp_name f.binding_info new_i_type,
   let var_map := (defin_var_list.to_alist.insert i_var new_i_var).insert ctx_var new_ctx_var,
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

end tactic.interactive

namespace o_minimal

variables {R : Type*} {S : struc R}

local infixr ` ⊢ `:10 := sect

--set_option pp.all true
example : definable S (λ p q, (q ∧ p) ∧ q) :=
begin
  defin_start,

  --guess_ctx_var,
  --guess_defin_vars',

  -- "intro p",
/-
  rw definable_fun', intros Γ' π p,
  -- now we need to pull back any variables mentioning Γ
  -- to use Γ' -- there aren't any yet ✓
  -- since that's done, we can dispose of the old context
  clear π Γ,
-/
  defin_intro p,

  -- "intro q",
/-
  rw definable_fun', intros Γ_1_1 π, -- don't intro q just yet
  -- this time we need to deal with p
  let p_1 := p.precomp π,
  intro q,
  change (definable_psh.definable (λ γ_1, (q.to_fun γ_1 ∧ p_1.to_fun γ_1) ∧ q.to_fun γ_1)),
  -- dispose of old context again
  clear_value p_1,
  clear p π Γ_1,
  rename Γ' → Γ,
-/
  defin_intro q,

  -- we're done with intros!

  -- "app",
  -- Lean apparently needs help with this higher-order unification problem
  apply definable.app_ctx' (λ d, (∧) (q.to_fun d ∧ p.to_fun d)) q.to_fun,

  -- let's take care of the variable intro
  swap,
  { exact q.definable },

  -- now another app
  apply definable.app_ctx' (λ d, (∧)) (λ d, (q.to_fun d ∧ p.to_fun d)),

  -- a constant! look up the lemma somehow
  { exact definable_const definable_and },

  -- now the same game continues
  apply definable.app_ctx' (λ d, (∧) (q.to_fun d)) p.to_fun,
  { apply definable.app_ctx' (λ d, (∧)) q.to_fun,
    { exact definable_const definable_and },
    { exact q.definable } },
  { exact p.definable }

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
