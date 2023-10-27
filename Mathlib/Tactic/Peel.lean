/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic.Basic

/-!
# The `peel` tactic

`peel h with idents*` tries to apply `forall_imp` (or `Exists.imp`, or `Filter.Eventually.mp`,
`Filter.Frequently.mp` and `Filter.eventually_of_forall`) with the argument `h` and uses `idents*`
to introduce variables with the supplied names.

Alternatively, one can provide a numeric argument as in `peel 4 h` which will peel 4 quantifiers off
the expressions automatically name the introduced variables.

In addition, the user may supply a term `e` via `... using e` in order to close the goal
immediately. In particular, `peel h using e` is equivalent to `peel h; exact e`. The `using` syntax
may be paired with any of the other features of `peel`.
-/

namespace Mathlib.Tactic.Peel
open Lean Expr Meta Elab Tactic

/--
Peels matching quantifiers off of a given term and the goal and introduces the relevant variables.

Given `p q : ℕ → Prop`, `h : ∀ x, p x`, and a goal `⊢ : ∀ x, q x`, the tactic `peel h with h' x`
will introduce `x : ℕ`, `h' : p x` into the context and the new goal will be `⊢ q x`. This works
with `∃`, as well as `∀ᶠ` and `∃ᶠ`, and it can even be applied to a sequence of quantifiers. Note
that this is a logically weaker setup, so using this tactic is not always feasible.

For a more complex example, given a hypothesis and a goal:
```
h : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, 1 / (n + 1 : ℝ) < ε
⊢ ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, 1 / (n + 1 : ℝ) ≤ ε
```
(which differ only in `<`/`≤`), applying `peel h with h_peel ε hε N n hn` will yield a tactic state:
```
h : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, 1 / (n + 1 : ℝ) < ε
ε : ℝ
hε : 0 < ε
N n : ℕ
hn : N ≤ n
h_peel : 1 / (n + 1 : ℝ) < ε
⊢ 1 / (n + 1 : ℝ) ≤ ε
```
and the goal can be closed with `exact h_peel.le`.
Note that in this example, `h` and the goal are logically equivalent statements, but `peel`
*cannot* be immediately applied to show that the goal implies `h`.

`peel` can take an optional numeric argument prior to the supplied hypothesis; in which case it will
autoname the introduced variables, but they may be inaccessible. However, in this case the user must
still introduce a single name such as `with h_peel` for the new hypothesis.

In addition, `peel` supports goals of the form `(∀ x, p x) ↔ ∀ x, q x`, or likewise for any
other quantifier. In this case, there is no hypothesis or term to supply, but otherwise the syntax
is the same. So for such goals, the syntax is `peel 1` or `peel with x`, and after which the
resulting goal is `p x ↔ q x`. The `congr!` tactic can also be applied to goals of this form using
`congr! 1 with x`. While `congr!` applies congruence lemmas in general, `peel` can be relied upon
to only apply to outermost quantifiers.

Finally, the user may supply a term `e` via `... using e` in order to close the goal
immediately. In particular, `peel h using e` is equivalent to `peel h; exact e`. The `using` syntax
may be paired with any of the other features of `peel`.

This tactic works by repeatedly applying `forall_imp`, `Exists.imp`, `Filter.Eventually.mp`,
`Filter.Frequently.mp`, and `Filter.eventually_of_forall` and introducing the variables as these
are applied.
-/
syntax (name := peel) "peel" (num)? (ppSpace colGt term)? (withArgs)? (usingArg)? : tactic

private lemma and_imp_left_of_imp_imp {p q r : Prop} (h : r → p → q) : r ∧ p → r ∧ q := by tauto

private theorem eventually_imp {α : Type*} {p q : α → Prop} {f : Filter α}
    (hq : ∀ (x : α), p x → q x) (hp : ∀ᶠ (x : α) in f, p x) : ∀ᶠ (x : α) in f, q x :=
  Filter.Eventually.mp hp (Filter.eventually_of_forall hq)

private theorem frequently_imp {α : Type*} {p q : α → Prop} {f : Filter α}
    (hq : ∀ (x : α), p x → q x) (hp : ∃ᶠ (x : α) in f, p x) : ∃ᶠ (x : α) in f, q x :=
  Filter.Frequently.mp hp (Filter.eventually_of_forall hq)

/-- The list of constants that are regarded as being quantifiers. -/
def quantifiers : List Name :=
  [``Exists, ``And, ``Filter.Eventually, ``Filter.Frequently]

/-- If `unfold` is false then do `whnfR`, otherwise unfold everything that's not a quantifier,
according to the `quantifiers` list. -/
def whnfQuantifier (p : Expr) (unfold : Bool) : MetaM Expr := do
  if unfold then
    whnfHeadPred p fun e =>
      if let .const n .. := e.getAppFn then
        return !(n ∈ quantifiers)
      else
        return false
  else
    whnfR p

/-- Throws an error saying `ty` and `target` could not be matched up. -/
def throwPeelError {α : Type} (ty target : Expr) : MetaM α :=
  throwError "Tactic 'peel' could not match quantifiers in{indentD ty}\nand{indentD target}"

/-- If `f` is a lambda then use its binding name to generate a new hygienic name,
and otherwise choose a new hygienic name. -/
def mkFreshBinderName (f : Expr) : MetaM Name :=
  if let .lam n .. := f then
    mkFreshUserName n
  else
    mkFreshUserName `a

/-- Applies a "peel theorem" with two main arguments, where the first is the new goal
and the second can be filled in using `e`. Then it intros two variables with the
provided names.

If, for example, `goal : ∃ y : α, q y` and `thm := Exists.imp`, the metavariable returned has
type `q x` where `x : α` has been introduced into the context. -/
def applyPeelThm (thm : Name) (goal : MVarId)
    (e : Expr) (ty target : Expr) (n : Name) (n' : Name) :
    MetaM (FVarId × List MVarId) := do
  let new_goal :: ge :: _ ← goal.applyConst thm <|> throwPeelError ty target
    | throwError "peel: internal error"
  ge.assignIfDefeq e <|> throwPeelError ty target
  let (fvars, new_goal) ← new_goal.introN 2 [n, n']
  return (fvars[1]!, [new_goal])

/-- This is the core to the `peel` tactic.

It tries to match `e` and `goal` as quantified statements (using `∀` and the quantifiers in
the `quantifiers` list), then applies "peel theorems" using `applyPeelThm`.

We treat `∧` as a quantifier for sake of dealing with
quantified statements like `∃ δ > (0 : ℝ), q δ`,
which is notation for `∃ δ, δ > (0 : ℝ) ∧ q δ`. -/
def peelCore (goal : MVarId) (e : Expr) (n? : Option Name) (n' : Name) (unfold : Bool) :
    MetaM (FVarId × List MVarId) := goal.withContext do
  let ty ← whnfQuantifier (← inferType e) unfold
  let target ← whnfQuantifier (← goal.getType) unfold
  if ty.isForall && target.isForall then
    applyPeelThm ``forall_imp goal e ty target (← n?.getDM (mkFreshUserName target.bindingName!)) n'
  else if ty.getAppFn.isConst
            && ty.getAppNumArgs == target.getAppNumArgs
            && ty.getAppFn == target.getAppFn then
    match target.getAppFnArgs with
    | (``Exists, #[_, p]) =>
      applyPeelThm ``Exists.imp goal e ty target (← n?.getDM (mkFreshBinderName p)) n'
    | (``And, #[_, _]) =>
      applyPeelThm ``and_imp_left_of_imp_imp goal e ty target (← n?.getDM (mkFreshUserName `p)) n'
    | (``Filter.Eventually, #[_, p, _]) =>
      applyPeelThm ``eventually_imp goal e ty target (← n?.getDM (mkFreshBinderName p)) n'
    | (``Filter.Frequently, #[_, p, _]) =>
      applyPeelThm ``frequently_imp goal e ty target (← n?.getDM (mkFreshBinderName p)) n'
    | _ => throwPeelError ty target
  else
    throwPeelError ty target

/-- Given a list `l` of names, this peels `num` quantifiers off of the expression `e` and
the main goal and introduces variables with the provided names until the list of names is exhausted.
Note: the name `n?` (with default `this`) is used for the name of the expression `e` with
quantifiers peeled. -/
def peelArgs (e : Expr) (num : Nat) (l : List Name) (n? : Option Name) (unfold : Bool := true) :
    TacticM Unit := do
  match num with
    | 0 => return
    | num + 1 =>
      let fvarId ← liftMetaTacticAux (peelCore · e l.head? (n?.getD `this) unfold)
      peelArgs (.fvar fvarId) num l.tail n?
      unless num == 0 do
        if let some mvarId ← observing? do (← getMainGoal).clear fvarId then
          replaceMainGoal [mvarId]

/-- Similar to `peelArgs` but peels arbitrarily many quantifiers. Returns whether or not
any quantifiers were peeled. -/
partial def peelUnbounded (e : Expr) (n? : Option Name) (unfold : Bool := false) :
    TacticM Bool := do
  let fvarId? ← observing? <| liftMetaTacticAux (peelCore · e none (n?.getD `this) unfold)
  if let some fvarId := fvarId? then
    let peeled ← peelUnbounded (.fvar fvarId) n?
    if peeled then
      if let some mvarId ← observing? do (← getMainGoal).clear fvarId then
        replaceMainGoal [mvarId]
    return true
  else
    return false

private lemma Filter.frequently_congr {α : Type*} {f : Filter α} {p : α → Prop} {q : α → Prop}
    (h : ∀ᶠ (x : α) in f, p x ↔ q x) : (∃ᶠ (x : α) in f, p x) ↔ ∃ᶠ (x : α) in f, q x := by
  constructor
  all_goals refine (Filter.Frequently.mp · (h.mono fun _ => ?_))
  exacts [Iff.mp, Iff.mpr]

/-- Peel off a single quantifier from an `↔`. -/
def peelIffAux : TacticM Unit := do
  evalTactic (← `(tactic| focus
    first | apply forall_congr'
          | apply exists_congr
          | apply Filter.eventually_congr
          | apply Filter.frequently_congr
          | fail "failed to apply a quantifier congruence lemma."
    try apply Filter.eventually_of_forall))

/-- Peel off quantifiers from an `↔` and assign the names given in `l` to the introduced
variables. -/
def peelArgsIff (l : List Name) : TacticM Unit := withMainContext do
  match l with
    | [] => pure ()
    | h :: hs =>
      peelIffAux
      let goal ← getMainGoal
      let (_, new_goal) ← goal.intro h
      replaceMainGoal [new_goal]
      peelArgsIff hs

elab_rules : tactic
  | `(tactic| peel $n:num $e:term) => withMainContext do
    peelArgs (← elabTerm e none) n.getNat [] none
  | `(tactic| peel $e:term) => withMainContext do
    let e ← elabTerm e none
    unless ← peelUnbounded e none do
      throwPeelError (← inferType e) (← getMainTarget)
  | `(tactic| peel $e:term $h:withArgs) => withMainContext do
    let hs := ((← getWithArgs h).map Syntax.getId).toList
    let e ← elabTerm e none
    let l := hs.tail
    if l.isEmpty then
      unless ← peelUnbounded e hs.head? do
        throwPeelError (← inferType e) (← getMainTarget)
    else
      peelArgs e l.length l hs.head?
  | `(tactic| peel $n:num) =>
    peelArgsIff <| .replicate n.getNat `_
  | `(tactic| peel $h:withArgs) => withMainContext do
    peelArgsIff ((← getWithArgs h).map Syntax.getId).toList

macro_rules
  | `(tactic| peel $[$n:num]? $[$e:term]? $[$h:withArgs]? using $u:term) =>
    `(tactic| peel $[$n:num]? $[$e:term]? $[$h:withArgs]?; exact $u)
