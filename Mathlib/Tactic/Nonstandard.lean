/-
Copyright (c) 2024 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Lean.Elab.Tactic
import Lean.Elab.Term
import Lean.Util.Trace
import Mathlib.Order.Filter.Germ.Star
import Lean.Meta.Tactic.Simp.Main

initialize Lean.registerTraceClass `Tactic.transfer
set_option linter.missingDocs true
/-!
# The `transfer` Tactic for Nonstandard Analysis

This file defines the `transfer` tactic, which automates the transfer principle in
Nonstandard Analysis.
It simplifies expressions involving `Hyper.lift`, `Hyper.liftPred`, `Hyper.std`, etc., allowing
users to move between standard and nonstandard formulations easily.
-/

open Lean Meta Elab Tactic Term Hyper

namespace Mathlib.Tactic.Nonstandard



/--
Finds the index type `ι` in a `Hyper ι α` type within the given expression.
-/
def findIndexType (e : Expr) : Option Expr :=
  if let some t := e.find? (·.isAppOfArity ``Hyper 3) then
    some (t.getAppArgs[0]!)
  else if let some t := e.find? (·.isAppOfArity ``Filter.Germ 2) then
    some (t.getAppArgs[0]!)
  else if let some t := e.find? (·.isAppOfArity ``Filter.hyperfilter 2) then
    some (t.getAppArgs[0]!)
  else
    none

/--
The `transfer` tactic simplifies expressions using the transfer principle.
It uses a set of simp lemmas that relate standard and nonstandard operations.
It supports optional simp arguments and location.
It automatically infers the index type `ι` to correctly instantiate quantifier transfer lemmas.
It supports directional transfer:
- `transfer` or `transfer +upward`: Transfers standard quantifiers to nonstandard ones
  (forward rewrite).
- `transfer +downward`: Transfers nonstandard quantifiers to standard ones (backward rewrite).
-/
syntax transferDir := "+" &"upward" <|> "+" &"downward"

syntax "transfer" (ppSpace transferDir)? ("[" Lean.Parser.Tactic.simpLemma,* "]")?
  (ppSpace Lean.Parser.Tactic.location)? : tactic

/-- Checks if a domain is a Hyper type. -/
def isHyperDomain (dom : Expr) : MetaM Bool := do
  let dom ← whnfR dom
  return dom.isAppOf ``Hyper || dom.isAppOf ``Filter.Germ

elab_rules : tactic
  | `(tactic| transfer $[$dir]? $[ [ $args,* ] ]? $[$loc]?) => do
    let locVal := (loc.map expandLocation).getD (Location.targets #[] true)
    let isDownward := dir.map (fun d => d.raw[1].getId.toString == "downward") |>.getD false

    -- Helper to infer index type from a list of expressions
    let inferFromExprs (exprs : List Expr) : MetaM (Option Expr) := do
      for e in exprs do
        if let some ι := findIndexType e then
          return some ι
      return none

    -- Collect expressions to search for ι
    let mut exprsToSearch : List Expr := []

    -- Add initial target
    let initialTarget ← getMainTarget
    exprsToSearch := exprsToSearch ++ [initialTarget]

    -- Add lctx types (BEFORE revert)
    let lctx ← getLCtx
    for ldecl in lctx do
      if !ldecl.isImplementationDetail then
        try
          exprsToSearch := exprsToSearch ++ [← whnf ldecl.type]
        catch _ =>
          pure ()


    -- Auto-revert    -- Check auto-revert
    let lctx ← getLCtx
    let mut fvarsToRevert : Array FVarId := #[]
    for ldecl in lctx do
      if ldecl.isImplementationDetail then continue
      let isHyp ← (try isHyperDomain ldecl.type catch _ => pure false)
      if isHyp then
        fvarsToRevert := fvarsToRevert.push ldecl.fvarId

    if !fvarsToRevert.isEmpty then
      -- Construct syntax for revert
      let fvarsStx : Array (TSyntax `ident) ← fvarsToRevert.mapM fun fvarId => do
        let ldecl ← fvarId.getDecl
        return mkIdent ldecl.userName
      try
        evalTactic (← `(tactic| revert $fvarsStx*))
      catch _ => pure ()

    -- Add new target (after revert)
    let newTarget ← getMainTarget
    exprsToSearch := exprsToSearch ++ [newTarget]

    -- If target is forall/exists, check domain (on new target)
    if newTarget.isForall then
      try
        exprsToSearch := exprsToSearch ++ [← whnf newTarget.bindingDomain!]
      catch _ =>
        pure ()
    else if newTarget.isAppOfArity ``Exists 2 then
      try
        exprsToSearch := exprsToSearch ++ [← whnf newTarget.getAppArgs[0]!]
      catch _ =>
        pure ()

    match locVal with
    | Location.targets hyps _ =>
      for hStx in hyps do
        if let some ldecl := (← getLCtx).findFromUserName? hStx.getId then
          exprsToSearch := exprsToSearch ++ [ldecl.type]
        else
          logInfo m!"[transfer] Could not find hypothesis {hStx.getId}"
    | Location.wildcard =>
      -- We already collected lctx types before revert.
      -- But if revert happened, lctx is smaller.
      -- So we don't need to collect again.
      pure ()

    -- Infer ι
    let ι? ← inferFromExprs exprsToSearch

    if let some ι := ι? then
      logInfo m!"[transfer] Found index type: {ι}"
    else
      logInfo m!"[transfer] Could not find index type in {exprsToSearch}"

    -- Construct syntax for user args and directional quantifier lemmas (if any)
    let userArgs :=
      match args with
      | some a => a.getElems
      | none => #[]

    -- Lemmas that always reduce complexity (e.g. eliminate std/liftPred on standard args)
    let reductionLemmasBase : List Name := [
      ``Hyper.liftPred_std,
      ``Hyper.liftRel_std,
      ``Hyper.lift_std,
      ``Hyper.lift₂_std,
      ``Hyper.lift_ofSeq,
      ``Hyper.lift₂_ofSeq,
      ``Hyper.std_inj,
      -- ``Hyper.std_le, -- Moved to structuralLemmas
      -- ``Hyper.std_lt, -- Moved to structuralLemmas
      ``Hyper.liftPred_ofSeq,
      ``Hyper.liftRel_ofSeq,
      ``Hyper.liftRel_const_coe,
      ``Hyper.ofSeq_le_ofSeq,
      ``Hyper.ofSeq_lt_ofSeq,
      ``Hyper.std_lt_ofSeq,
      ``Hyper.add_eq_lift₂,
      ``Hyper.eq_iff_liftRel_eq,
      ``Hyper.liftRel_lift_left,
      ``Hyper.liftRel_std_right,
      ``Hyper.lift_lift₂_diagonal,
      ``Hyper.lift_comp,
      ``Hyper.liftPred_lift,
      ``Hyper.lift₂_std_left,
      ``Hyper.lift₂_std_right,
      ``Hyper.liftRel_lift_right,
      ``Hyper.mul_eq_lift₂,
      ``Hyper.sub_eq_lift₂,
      ``Hyper.neg_eq_lift,
      ``Hyper.zero_eq_std,
      ``Hyper.one_eq_std,
      ``Hyper.ofSeq_eq_zero,
      ``Hyper.le_iff_liftRel_le,
      ``Hyper.lt_iff_liftRel_lt,
      ``Hyper.eq_iff_liftRel_eq,
      ``Hyper.star_subset,
      ``Hyper.star_disjoint,
      ``Hyper.liftRel_std,
      ``Hyper.liftRel_std_left,
      ``Hyper.liftRel_std_right,
      ``Hyper.liftRel_lift_left,
      ``Hyper.liftRel_lift_right,
      ``Hyper.liftPred_lift
    ]

    let reductionLemmas := reductionLemmasBase

    -- Lemmas that distribute/commute structure (need reversal for upward transfer)
    let structuralLemmas : List Name := [
      ``Hyper.liftPred_and,
      ``Hyper.liftPred_or,
      ``Hyper.liftPred_not,
      ``Hyper.liftPred_imp,
      ``Hyper.std_zero,
      ``Hyper.std_one,
      ``Hyper.std_add,
      ``Hyper.std_mul,
      ``Hyper.std_neg,
      ``Hyper.std_sub,
      ``Hyper.std_inv,
      ``Hyper.std_div,
      -- Quantifiers
      ``Hyper.forall_std_iff,
      ``Hyper.exists_std_iff,
      -- Sets
      ``Hyper.star_univ,
      ``Hyper.star_empty,
      ``Hyper.star_union,
      ``Hyper.star_inter,
      ``Hyper.star_compl,
      ``Hyper.std_le,
      ``Hyper.std_lt
    ]

    let env ← getEnv
    let mut simpArgs : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]

    -- Add the [transfer] simp set itself
    simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma| transfer))

    -- Add reduction lemmas (always forward)
    for n in reductionLemmas do
      if env.contains n then
        let resolvedName ← resolveGlobalConstNoOverload (mkIdent n)
        let term : TSyntax `term := mkIdent resolvedName
        simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma| $term:term))

    -- Add structural lemmas (direction depends on transfer type)
    for n in structuralLemmas do
      if env.contains n then
        let resolvedName ← resolveGlobalConstNoOverload (mkIdent n)
        let term : TSyntax `term := mkIdent resolvedName
        if isDownward then
          -- Downward: expand structure (forward)
          simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma| $term:term))
        else
          -- Upward: contract structure (backward)
          simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma| ← $term:term))

    -- Add quantifier lemmas with explicit ι if found, otherwise generic
    if let some ι := ι? then
      let ιStx ← PrettyPrinter.delab ι
      if isDownward then
        simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma|
          Hyper.forall_std_iff (ι := $ιStx)))
        simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma|
          Hyper.exists_std_iff (ι := $ιStx)))
      else
        -- Upward direction: handled by preTransfer
        pure ()
    else
      if isDownward then
        simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma|
          Hyper.forall_std_iff))
        simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma|
          Hyper.exists_std_iff))
      else
        -- Upward direction: handled by preTransfer
        pure ()

    -- Add user args
    simpArgs := simpArgs ++ userArgs

    -- Construct syntax for simp args
    let simpArgsStx := simpArgs.map (·)

    -- Run simp
    let simpTactic ← `(tactic|
      simp (config := { failIfUnchanged := false }) only [$simpArgsStx,*] $[$loc]?)

    if isDownward then
      evalTactic simpTactic
    else
      -- Upward: Run simp first (to handle structural lemmas), then custom quantifier rewriting
      evalTactic (← `(tactic|
        simp (config := { failIfUnchanged := false }) only [$simpArgsStx,*] at *))

      if (← getGoals).isEmpty then return

      -- Custom post-processing for quantifiers (upward)
      -- We need to repeatedly apply forall_std_iff / exists_std_iff
      -- We do this by iterating on the goal
      let mut currentGoal ← getMainGoal
      let mut changed := true
      while changed do
        changed := false
        let target ← currentGoal.getType
        let target ← whnf target
        dbg_trace "Target: {target}"
        dbg_trace "Target kind: {target.ctorName}"
        dbg_trace "Target isForall: {target.isForall}"

        if target.isForall && !target.isAppOf ``Filter.Eventually then
          -- Check if domain is Hyper
          if (← (try isHyperDomain target.bindingDomain! catch _ => pure false)) then
             try
               if let some ι := ι? then
                 let ιStx ← PrettyPrinter.delab ι
                 evalTactic (← `(tactic| rw [Hyper.forall_ofSeq_iff (ι := $ιStx)]))
               else
                 evalTactic (← `(tactic| rw [Hyper.forall_ofSeq_iff]))
               changed := true
               currentGoal ← getMainGoal -- update goal
             catch _ => pure ()
          else
             -- Not Hyper, intro and recurse
             let name := target.bindingName!
             liftMetaTactic fun mvarId => do
               let (_, mvarId) ← mvarId.intro name
               return [mvarId]
             evalTactic (← `(tactic| transfer))
             return
        else if target.isAppOfArity ``Exists 2 then
           -- Check domain
           let domain := target.getAppArgs[0]!
           if (← (try isHyperDomain domain catch _ => pure false)) then
             try
               if let some ι := ι? then
                 let ιStx ← PrettyPrinter.delab ι
                 evalTactic (← `(tactic| rw [Hyper.exists_ofSeq_iff (ι := $ιStx)]))
               else
                 evalTactic (← `(tactic| rw [Hyper.exists_ofSeq_iff]))
               changed := true
               evalTactic (← `(tactic| transfer))
               return
             catch _ => pure ()

        if !changed then
           -- Try to look inside?
           -- For now, we only handle top-level quantifiers.
           -- If the quantifier is under `liftRel`, we might need to use `simp` again?
           -- But `simp` should have handled `liftRel`.
           pure ()

      -- Run simp again to reduce ofSeq introduced by quantifiers
      evalTactic (← `(tactic|
        simp (config := { failIfUnchanged := false }) only [$simpArgsStx,*] $[$loc]?))

      if (← getGoals).isEmpty then return

      -- Custom post-processing for quantifiers
      let goal ← getMainGoal
      let tgt ← instantiateMVars (← goal.getType)

      if tgt.isForall then
        let dom := tgt.bindingDomain!
        -- dbg_trace "Checking domain: {dom}"
        let isHyp ← isHyperDomain dom
        if isHyp then
           -- dbg_trace "Domain is Hyper!"
           -- Rewrite (∀ x, liftPred P x) -> (∀ a, P a) using forall_std_iff (backward)
           -- We use Simp.rewrite? to handle unification
           let mut thms : SimpTheorems := {}
           thms ← thms.addConst ``Hyper.forall_std_iff (inv := true)
           let ctx ← Simp.mkContext (config := {}) (simpTheorems := #[thms]) (congrTheorems := {})
           let (res, _) ← (Simp.rewrite? tgt thms.post {} "transfer" (rflOnly := false)).run ctx {}
           if let some res := res then
             replaceMainGoal [← applySimpResultToTarget goal tgt res]
             -- Recursively call transfer on the new goal

             evalTactic (← `(tactic| transfer))
             return

      else if tgt.isAppOfArity ``Exists 2 then
         let dom := tgt.getArg! 0
         let isHyp ← isHyperDomain dom
         if isHyp then
           -- Rewrite (∃ x, liftPred P x) -> (∃ a, P a) using exists_std_iff (backward)
           let mut thms : SimpTheorems := {}
           thms ← thms.addConst ``Hyper.exists_std_iff (inv := true)
           let ctx ← Simp.mkContext (config := {}) (simpTheorems := #[thms]) (congrTheorems := {})
           let (res, _) ← (Simp.rewrite? tgt thms.post {} "transfer" (rflOnly := false)).run ctx {}
           if let some res := res then
             replaceMainGoal [← applySimpResultToTarget goal tgt res]

      -- Final attempt to close goal
      evalTactic (← `(tactic| try apply Filter.eventually_congr))
      evalTactic (← `(tactic| try apply Filter.Eventually.of_forall))
      evalTactic (← `(tactic| try intro))
      if (← getGoals).isEmpty then return
      try evalTactic (← `(tactic| assumption)) catch _ => pure ()

/--
The `saturation` tactic automates the application of saturation principles.
It transforms a goal of the form `∃ x : Hyper ι α, ∀ k : κ, ...` into a
finite satisfiability problem.
Currently supports:
- `countable_saturation`: When `κ = ℕ` and `ι = ℕ`.
-/
syntax "saturation" : tactic

elab_rules : tactic
  | `(tactic| saturation) => do
    let goal ← getMainGoal
    let tgt ← whnf (← instantiateMVars (← goal.getType))

    -- Match goal: ∃ x : Hyper ι α, ∀ k : κ, P k x
    if tgt.isAppOfArity ``Exists 2 then
      let body := tgt.getArg! 1
      -- body is (fun x => ∀ k, P k x)
      if let Expr.lam _ _ (Expr.forallE _ kType _ _) _ := body then
        -- Check if index type is Nat
        if kType.isConstOf ``Nat then
           -- Apply countable_saturation
           evalTactic (← `(tactic| refine countable_saturation ?_))
           return
        else
           -- Try cardinal_saturation
           -- We leave the embedding as a subgoal
           evalTactic (← `(tactic| refine cardinal_saturation ?_ ?_))
           return
      else
        throwError "saturation: goal must be of the form ∃ x, ∀ k, ..."
    else
      throwError "saturation: goal must be of the form ∃ x, ..."

/--
The `overspill` tactic applies the overspill principle.
Given a hypothesis `h : ∀ n : ℕ, ∃ m > n, P m`, it produces
`∃ x : Hyper ℕ ℕ, IsInfinite x ∧ liftPred P x`.
Usage: `overspill h` or `overspill h with x hx`.
-/
syntax "overspill" term ("with" ident ident)? : tactic

elab_rules : tactic
  | `(tactic| overspill $h:term $[with $x:ident $hx:ident]?) => do
    -- Check if hType matches ∀ n, ∃ m > n, P m
    -- For now, we just apply the theorem and let Lean check unification
    evalTactic (← `(tactic| have := exists_infinite_of_forall_exists_gt $h))
    if let (some xId, some hxId) := (x, hx) then
      evalTactic (← `(tactic| obtain ⟨$xId, $hxId⟩ := this))
      evalTactic (← `(tactic| clear this))
    else
      -- If no names provided, keep 'this'
      pure ()

/--
The `underspill` tactic applies the underspill principle.
Given a hypothesis `h : ∀ x : Hyper ℕ ℕ, IsInfinite x → liftPred P x`, it produces
`∃ n : ℕ, ∀ m ≥ n, P m`.
Usage: `underspill h` or `underspill h with n hn`.
-/
syntax "underspill" term ("with" ident ident)? : tactic

elab_rules : tactic
  | `(tactic| underspill $h:term $[with $n:ident $hn:ident]?) => do
    -- Apply theorem
    evalTactic (← `(tactic| have := exists_forall_ge_of_forall_infinite $h))
    if let (some nId, some hnId) := (n, hn) then
      evalTactic (← `(tactic| obtain ⟨$nId, $hnId⟩ := this))
      evalTactic (← `(tactic| clear this))
    else
      pure ()

end Mathlib.Tactic.Nonstandard
