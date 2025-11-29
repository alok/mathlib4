/-
Copyright (c) 2024 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Lean.Elab.Tactic
import Mathlib.Order.Filter.Germ.Star
import Mathlib.Tactic.Basic
import Mathlib.Util.AtLocation
import Lean.Meta.Tactic.Simp.Main
set_option linter.missingDocs true
/-!
# The `transfer` Tactic for Nonstandard Analysis

This file defines the `transfer` tactic, which automates the transfer principle in Nonstandard Analysis.
It simplifies expressions involving `Hyper.lift`, `Hyper.liftPred`, `Hyper.std`, etc., allowing
users to move between standard and nonstandard formulations easily.
-/

open Lean Meta Elab Tactic Hyper

namespace Mathlib.Tactic.Nonstandard

/--
Finds the index type `ι` in a `Hyper ι α` type within the given expression.
-/
def findIndexType (e : Expr) : Option Expr :=
  if let some t := e.find? (·.isAppOfArity ``Hyper 3) then
    some (t.getArg! 0)
  else
    none

/--
The `transfer` tactic simplifies expressions using the transfer principle.
It uses a set of simp lemmas that relate standard and nonstandard operations.
It supports optional simp arguments and location.
It automatically infers the index type `ι` to correctly instantiate quantifier transfer lemmas.
It supports directional transfer:
- `transfer` or `transfer +upward`: Transfers standard quantifiers to nonstandard ones (forward rewrite).
- `transfer +downward`: Transfers nonstandard quantifiers to standard ones (backward rewrite).
-/
syntax transferDir := "+" &"upward" <|> "+" &"downward"

syntax "transfer" (ppSpace transferDir)? ("[" Lean.Parser.Tactic.simpLemma,* "]")?
  (ppSpace Lean.Parser.Tactic.location)? : tactic

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
    -- Always include the target, as it likely contains the Hyper type
    let mut exprsToSearch : List Expr := [(← getMainTarget)]

    match locVal with
    | Location.targets hyps _ =>
      for hStx in hyps do
        if let some ldecl := (← getLCtx).findFromUserName? hStx.getId then
          exprsToSearch := exprsToSearch ++ [ldecl.type]
        else
          logInfo m!"[transfer] Could not find hypothesis {hStx.getId}"
    | Location.wildcard =>
      let lctx ← getLCtx
      for ldecl in lctx do
        if !ldecl.isImplementationDetail then
          exprsToSearch := exprsToSearch ++ [ldecl.type]

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
    let reductionLemmas : List Name := [
      ``Hyper.liftPred_std,
      ``Hyper.liftRel_std,
      ``Hyper.lift_std,
      ``Hyper.lift₂_std,
      ``Hyper.std_inj,
      ``Hyper.std_le,
      ``Hyper.std_lt
    ]

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
      ``Hyper.std_div
    ]

    let mut simpArgs : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]

    -- Add reduction lemmas (always forward)
    for n in reductionLemmas do
      let resolvedName ← resolveGlobalConstNoOverload (mkIdent n)
      let term : TSyntax `term := mkIdent resolvedName
      simpArgs := simpArgs.push (← `(Lean.Parser.Tactic.simpLemma| $term:term))

    -- Add structural lemmas (direction depends on transfer type)
    for n in structuralLemmas do
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
    if isDownward then
      evalTactic (← `(tactic| simp (config := { failIfUnchanged := false }) only [$simpArgsStx,*] $[$loc]?))
    else
      -- Upward: Run simp first (to handle structural lemmas), then custom quantifier rewriting
      evalTactic (← `(tactic| simp (config := { failIfUnchanged := false }) only [$simpArgsStx,*] $[$loc]?))

      if (← getGoals).isEmpty then return

      -- Custom post-processing for quantifiers
      let goal ← getMainGoal
      let tgt ← instantiateMVars (← goal.getType)

      let isHyperDomain (dom : Expr) : Bool :=
        dom.isAppOf ``Hyper

      if tgt.isForall then
        let dom := tgt.bindingDomain!
        if isHyperDomain dom then
           -- Rewrite (∀ x, liftPred P x) -> (∀ a, P a) using forall_std_iff (backward)
           -- We use Simp.rewrite? to handle unification
           let mut thms : SimpTheorems := {}
           thms ← thms.addConst ``Hyper.forall_std_iff (inv := true)
           let ctx ← Simp.mkContext (config := {}) (simpTheorems := #[thms]) (congrTheorems := {})
           let (res, _) ← (Simp.rewrite? tgt thms.post {} "transfer" (rflOnly := false)).run ctx {}
           if let some res := res then
             replaceMainGoal [← applySimpResultToTarget goal tgt res]

      else if tgt.isAppOfArity ``Exists 2 then
         let dom := tgt.getArg! 0
         if isHyperDomain dom then
           -- Rewrite (∃ x, liftPred P x) -> (∃ a, P a) using exists_std_iff (backward)
           let mut thms : SimpTheorems := {}
           thms ← thms.addConst ``Hyper.exists_std_iff (inv := true)
           let ctx ← Simp.mkContext (config := {}) (simpTheorems := #[thms]) (congrTheorems := {})
           let (res, _) ← (Simp.rewrite? tgt thms.post {} "transfer" (rflOnly := false)).run ctx {}
           if let some res := res then
             replaceMainGoal [← applySimpResultToTarget goal tgt res]

end Mathlib.Tactic.Nonstandard
