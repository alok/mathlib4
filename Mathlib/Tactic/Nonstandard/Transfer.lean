/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic.Nonstandard.Complements.FilterProduct
import Mathlib.Data.Real.Hyperreal
import Lean

/*
# Transfer tactic for nonstandard analysis

This file implements a transfer tactic for working with filter germs and hyperreals.
The tactic converts statements about germs to equivalent statements about the underlying types.
*/

open Lean Meta Elab Tactic Lean.Elab.Term
open Filter Germ

-- Register trace class
initialize registerTraceClass `transfer

namespace Mathlib.Tactic.Transfer

/-- Apply the forall lifting rule for the LHS */
def forallRule (l α : Expr) : TacticM Unit := do
  trace[transfer] "forallRule called with l={l}, α={α}"
  -- Check that l has type Filter ι
  let lType ← inferType l
  trace[transfer] "l has type: {lType}"
  guard (lType.isAppOfArity ``Filter 1)
  -- Get the predicate from the LHS
  let tgt ← getMainTarget
  let tgt ← instantiateMVars tgt
  let tgt ← whnf tgt  -- Reduce to weak head normal form
  trace[transfer] "Target: {tgt}"
  trace[transfer] "Is iff? {tgt.isAppOfArity ``Iff 2}"
  trace[transfer] "App function: {tgt.getAppFn}"
  trace[transfer] "Num args: {tgt.getAppNumArgs}"
  if !tgt.isAppOfArity ``Iff 2 then
    throwError "Target is not an iff: {tgt}"
  let lhs := tgt.getArg! 0
  trace[transfer] "LHS: {lhs}"
  -- Extract the predicate p from (∀ x, p x)
  let p ← match lhs with
    | .forallE _ _ body _ => 
      trace[transfer] "Found forall, body: {body}"
      -- Create a lambda from the body
      withLocalDecl `x .default α fun x => do
        let bodyWithVar := body.instantiate #[x]
        trace[transfer] "Body with var: {bodyWithVar}"
        mkLambdaFVars #[x] bodyWithVar
    | _ => throwError "LHS is not a forall"
  trace[transfer] "Extracted predicate: {p}"
  -- Synthesize NeBot instance
  let neBotType ← mkAppM ``Filter.NeBot #[l]
  trace[transfer] "Synthesizing NeBot instance for type: {neBotType}"
  let inst ← synthInstance neBotType
  trace[transfer] "Synthesized instance: {inst}"
  -- Apply the theorem with the correct arguments
  -- The theorem signature is: forall_iff_forall_liftPred {ι α : Type*} {l : Filter ι} [l.NeBot] (p : α → Prop)
  -- The implicit arguments are ι, α, l, and the instance is implicit
  -- Only p needs to be passed explicitly
  let thm ← mkAppOptM ``Filter.Germ.forall_iff_forall_liftPred #[none, none, some l, some inst, some p]
  let goal ← getMainGoal
  trace[transfer] "Applying theorem: {thm}"
  trace[transfer] "Theorem type: {← inferType thm}"
  trace[transfer] "Current target: {← getMainTarget}"
  -- Check if the theorem type exactly matches the goal
  let thmType ← inferType thm
  let target ← getMainTarget
  trace[transfer] "Checking if theorem matches goal exactly"
  trace[transfer] "Theorem type: {thmType}"
  trace[transfer] "Target: {target}"
  
  if ← isDefEq thmType target then
    -- The theorem exactly proves our goal
    trace[transfer] "Theorem exactly matches goal, closing with theorem"
    closeMainGoal `forallRule thm
  else
    -- Try rewriting
    try
      let newGoals ← goal.rewrite target thm
      trace[transfer] "After applying forall rule, new goals: {newGoals.mvarIds}"
      trace[transfer] "Number of new goals: {newGoals.mvarIds.length}"
      replaceMainGoal newGoals.mvarIds
    catch e =>
      trace[transfer] "Rewrite failed with error: {e.toMessageData}"
      throwError "Failed to apply forall rule: {e.toMessageData}\nThm type: {← inferType thm}"

/-- Apply the exists lifting rule for the LHS */
def existsRule (l α : Expr) : TacticM Unit := do
  trace[transfer] "existsRule called with l={l}, α={α}"
  -- Check that l has type Filter ι
  let lType ← inferType l
  trace[transfer] "l has type: {lType}"
  guard (lType.isAppOfArity ``Filter 1)
  -- Get the predicate from the LHS
  let tgt ← getMainTarget
  let tgt ← instantiateMVars tgt
  guard (tgt.isAppOfArity ``Iff 2)
  let lhs := tgt.getArg! 0
  let lhs ← whnf lhs  -- Reduce to weak head normal form
  trace[transfer] "existsRule: LHS = {lhs}"
  trace[transfer] "LHS is app? {lhs.isApp}"
  if lhs.isApp then
    trace[transfer] "LHS fn: {lhs.getAppFn}"
    trace[transfer] "LHS args: {lhs.getAppArgs}"
  -- Extract the predicate p from (∃ x, p x)
  let p ← match lhs with
    | .app (.app (.const ``Exists _) _) (.lam _ _ body _) => 
      -- Create a lambda from the body
      withLocalDecl `x .default α fun x => do
        let bodyWithVar := body.instantiate #[x]
        mkLambdaFVars #[x] bodyWithVar
    | _ => throwError "LHS is not an exists: {lhs}"
  -- Synthesize NeBot instance
  let neBotType ← mkAppM ``Filter.NeBot #[l]
  let inst ← synthInstance neBotType
  -- Apply the theorem with the correct arguments
  -- The theorem signature is: exists_iff_exists_liftPred {ι α : Type*} {l : Filter ι} [l.NeBot] (p : α → Prop)
  let thm ← mkAppOptM ``Filter.Germ.exists_iff_exists_liftPred #[none, none, some l, some inst, some p]
  let goal ← getMainGoal
  trace[transfer] "Applying theorem: {thm}"
  trace[transfer] "Theorem type: {← inferType thm}"
  trace[transfer] "Current target: {← getMainTarget}"
  -- Check if the theorem exactly matches the goal
  let thmType ← inferType thm
  let target ← getMainTarget
  trace[transfer] "Checking if theorem matches goal exactly"
  if ← isDefEq thmType target then
    -- The theorem exactly proves our goal
    trace[transfer] "Theorem exactly matches goal, closing with theorem"
    closeMainGoal `existsRule thm
  else
    -- Try rewriting
    try
      let newGoals ← goal.rewrite target thm
      trace[transfer] "After applying exists rule, new goals: {newGoals.mvarIds}"
      trace[transfer] "Number of new goals: {newGoals.mvarIds.length}"
      replaceMainGoal newGoals.mvarIds
    catch e =>
      trace[transfer] "Rewrite failed with error: {e.toMessageData}"
      throwError "Failed to apply exists rule: {e.toMessageData}\nThm type: {← inferType thm}"

/-- Check if an expression is a coercion `↑a` */
def isCoeConst (e : Expr) : MetaM (Option Expr) := do
  trace[transfer] "isCoeConst checking: {e}"
  
  -- Based on the trace output, the expression has the exact structure:
  -- Filter.Germ.const applied to 4 args
  -- Let's just check if it's an application with the right function
  if e.isApp then
    let f := e.getAppFn  
    if f.isConst && f.constName! == ``Filter.Germ.const then
      -- Get all the arguments
      let args := e.getAppArgs
      if args.size == 4 then
        -- The last argument is what we want
        trace[transfer] "Found Germ.const with 4 args, returning: {args[3]!}"
        return some args[3]!
      else if args.size == 3 then  
        trace[transfer] "Found Germ.const with 3 args, returning: {args[2]!}"
        return some args[2]!
  
  -- If not found directly, check the type and try whnf
  let ty ← inferType e
  trace[transfer] "Type of {e} is {ty}"
  if !ty.isAppOfArity ``Filter.Germ 2 then
    return none
    
  -- Try whnf to reduce coercions
  let e' ← whnf e
  trace[transfer] "After whnf: {e'}"
  
  -- Try again after whnf
  if e'.isApp then
    let f := e'.getAppFn  
    if f.isConst && f.constName! == ``Filter.Germ.const then
      let args := e'.getAppArgs
      if args.size == 4 then
        trace[transfer] "After whnf: Found Germ.const with 4 args, returning: {args[3]!}"
        return some args[3]!
      else if args.size == 3 then  
        trace[transfer] "After whnf: Found Germ.const with 3 args, returning: {args[2]!}"
        return some args[2]!
  
  trace[transfer] "No pattern matched"
  return none

-- Forward declare transferCongr
mutual

/-- Lift quantifiers from the LHS to the RHS */
partial def transferLiftLhs : TacticM Unit := do
  let tgt ← getMainTarget
  let tgt ← instantiateMVars tgt
  
  -- Try to extract LHS and RHS from an iff
  let (lhs, rhs) ← match tgt with
    | .app (.app (.const ``Iff _) lhs) rhs => pure (lhs, rhs)
    | _ => 
      -- Try reducing the target
      let tgt' ← whnf tgt
      match tgt' with
      | .app (.app (.const ``Iff _) lhs) rhs => pure (lhs, rhs)
      | _ => throwError "Target is not an iff: {tgt}, reduced = {tgt'}"
  
  -- For the simple case, we know the pattern:
  -- LHS: (∀ x, p x)
  -- RHS: ∀ (x : (↑l).Germ α), Germ.LiftPred p x
  -- OR
  -- RHS: ∀ (x : (↑l).Germ α), ↑a ≤ x  (or other relations)
  
  match rhs with
  | .forallE _ ty body _ =>
    -- The type ty should be (↑l).Germ α
    
    -- First, check if the body is a LiftPred application
    let bodyFn := body.getAppFn
    if let some name := bodyFn.constName? then
      if name == ``Germ.LiftPred || name == ``Filter.Germ.LiftPred || name == ``LiftPred then
        -- Handle LiftPred case
        let args := body.getAppArgs
        if args.size >= 2 && args[args.size - 1]! == .bvar 0 then
          let p := args[args.size - 2]!
          
          -- Get the filter from the context
          let ctx ← getLCtx
          let mut filterVar : Option Expr := none
          
          for decl in ctx do
            if !decl.isImplementationDetail then
              let declType ← instantiateMVars decl.type
              if declType.isAppOfArity ``Ultrafilter 1 then
                filterVar := some (mkFVar decl.fvarId)
                break
          
          match filterVar with
          | some l =>
            -- Extract α from the predicate p
            let pType ← inferType p
            match pType with
            | .forallE _ α _ _ =>
              let filterL ← mkAppM ``Ultrafilter.toFilter #[l]
              trace[transfer] "Calling forallRule with l={filterL}, α={α}"
              forallRule filterL α
            | _ => throwError "Could not extract type from predicate: {pType}"
          | none => throwError "Could not find ultrafilter in context"
        else
          throwError "RHS body does not match pattern: LiftPred <?> (.bvar 0)"
        return
    
    -- If not LiftPred, check if it's a logical connective of LiftPreds
    -- Pattern: LiftPred p x ∧ LiftPred q x, etc.
    trace[transfer] "Body is not LiftPred, checking for logical connective pattern"
    trace[transfer] "Body: {body}"
    
    -- Check if body is a logical connective
    if body.isAppOfArity ``And 2 then
      -- Body is: LiftPred p x ∧ LiftPred q x
      let arg1 := body.getArg! 0
      let arg2 := body.getArg! 1
      
      -- Check both args are LiftPred applications with .bvar 0
      trace[transfer] "And arg1: {arg1}, isApp: {arg1.isApp}"
      trace[transfer] "And arg2: {arg2}, isApp: {arg2.isApp}"
      if arg1.isApp then
        trace[transfer] "arg1 fn: {arg1.getAppFn}, args: {arg1.getAppArgs}"
      if arg2.isApp then
        trace[transfer] "arg2 fn: {arg2.getAppFn}, args: {arg2.getAppArgs}"
      
      -- LiftPred when fully applied has 5 args: [ι, α, filter, predicate, element]
      -- Check if both are LiftPred applications
      let isLiftPred1 := arg1.isAppOfArity ``Filter.Germ.LiftPred 5 || 
                         arg1.isAppOfArity ``Germ.LiftPred 5 ||
                         arg1.isAppOfArity ``LiftPred 5
      let isLiftPred2 := arg2.isAppOfArity ``Filter.Germ.LiftPred 5 || 
                         arg2.isAppOfArity ``Germ.LiftPred 5 ||
                         arg2.isAppOfArity ``LiftPred 5
      
      if isLiftPred1 && isLiftPred2 && 
         arg1.getArg! 4 == .bvar 0 && arg2.getArg! 4 == .bvar 0 then
        let p := arg1.getArg! 3
        let q := arg2.getArg! 3
        
        -- Get the filter from context
        let ctx ← getLCtx
        let mut filterVar : Option Expr := none
        
        for decl in ctx do
          if !decl.isImplementationDetail then
            let declType ← instantiateMVars decl.type
            if declType.isAppOfArity ``Ultrafilter 1 then
              filterVar := some (mkFVar decl.fvarId)
              break
        
        match filterVar with
        | some l =>
          let filterL ← mkAppM ``Ultrafilter.toFilter #[l]
          let inst ← synthInstance (← mkAppM ``Filter.NeBot #[filterL])
          let thm ← mkAppOptM ``Filter.Germ.and_iff_and_liftPred 
            #[none, none, some filterL, some inst, some p, some q]
          
          let thmType ← inferType thm
          let target ← getMainTarget
          trace[transfer] "Applying and rule"
          trace[transfer] "Theorem type: {thmType}"
          trace[transfer] "Target: {target}"
          
          if ← isDefEq thmType target then
            closeMainGoal `forallAndRule thm
          else
            let goal ← getMainGoal
            let newGoals ← goal.rewrite target thm
            replaceMainGoal newGoals.mvarIds
        | none => throwError "Could not find ultrafilter in context"
      else
        throwError "And body does not match pattern: LiftPred p x ∧ LiftPred q x"
      return
    else if body.isAppOfArity ``Not 1 then
      -- Body is: ¬LiftPred p x
      let arg := body.getArg! 0
      
      -- Check arg is LiftPred application with .bvar 0
      let isLiftPred := arg.isAppOfArity ``Filter.Germ.LiftPred 5 || 
                        arg.isAppOfArity ``Germ.LiftPred 5 ||
                        arg.isAppOfArity ``LiftPred 5
      if isLiftPred && arg.getArg! 4 == .bvar 0 then
        let p := arg.getArg! 3
        
        -- Get the filter from context
        let ctx ← getLCtx
        let mut filterVar : Option Expr := none
        
        for decl in ctx do
          if !decl.isImplementationDetail then
            let declType ← instantiateMVars decl.type
            if declType.isAppOfArity ``Ultrafilter 1 then
              filterVar := some (mkFVar decl.fvarId)
              break
        
        match filterVar with
        | some l =>
          let filterL ← mkAppM ``Ultrafilter.toFilter #[l]
          let inst ← synthInstance (← mkAppM ``Filter.NeBot #[filterL])
          let thm ← mkAppOptM ``Filter.Germ.not_iff_not_liftPred 
            #[none, none, some filterL, some inst, some p]
          
          let thmType ← inferType thm
          let target ← getMainTarget
          trace[transfer] "Applying not rule"
          trace[transfer] "Theorem type: {thmType}"
          trace[transfer] "Target: {target}"
          
          if ← isDefEq thmType target then
            closeMainGoal `forallNotRule thm
          else
            let goal ← getMainGoal
            let newGoals ← goal.rewrite target thm
            replaceMainGoal newGoals.mvarIds
        | none => throwError "Could not find ultrafilter in context"
      else
        throwError "Not body does not match pattern: ¬LiftPred p x"
      return
    else if body.isForall then
      -- Check if it's an implication pattern: LiftPred p x → LiftPred q x
      match body with
      | .forallE _ ty innerBody _ =>
        -- Check if ty is LiftPred p x
        let isLiftPred1 := ty.isAppOfArity ``Filter.Germ.LiftPred 5 || 
                           ty.isAppOfArity ``Germ.LiftPred 5 ||
                           ty.isAppOfArity ``LiftPred 5
        let isLiftPred2 := innerBody.isAppOfArity ``Filter.Germ.LiftPred 5 || 
                           innerBody.isAppOfArity ``Germ.LiftPred 5 ||
                           innerBody.isAppOfArity ``LiftPred 5
        if isLiftPred1 && ty.getArg! 4 == .bvar 0 &&
           isLiftPred2 && innerBody.getArg! 4 == .bvar 1 then  -- Note: .bvar 1 due to new binding
          let p := ty.getArg! 3
          let q := innerBody.getArg! 3
          
          -- Get the filter from context
          let ctx ← getLCtx
          let mut filterVar : Option Expr := none
          
          for decl in ctx do
            if !decl.isImplementationDetail then
              let declType ← instantiateMVars decl.type
              if declType.isAppOfArity ``Ultrafilter 1 then
                filterVar := some (mkFVar decl.fvarId)
                break
          
          match filterVar with
          | some l =>
            let filterL ← mkAppM ``Ultrafilter.toFilter #[l]
            let inst ← synthInstance (← mkAppM ``Filter.NeBot #[filterL])
            let thm ← mkAppOptM ``Filter.Germ.imp_iff_imp_liftPred 
              #[none, none, some filterL, some inst, some p, some q]
            
            let thmType ← inferType thm
            let target ← getMainTarget
            trace[transfer] "Applying imp rule"
            trace[transfer] "Theorem type: {thmType}"
            trace[transfer] "Target: {target}"
            
            if ← isDefEq thmType target then
              closeMainGoal `forallImpRule thm
            else
              let goal ← getMainGoal
              let newGoals ← goal.rewrite target thm
              replaceMainGoal newGoals.mvarIds
          | none => throwError "Could not find ultrafilter in context"
          return  -- Important: return after successfully handling implication
        else
          -- Not an implication pattern, continue to nested forall handling
          trace[transfer] "Not an implication pattern, continuing to nested forall"
      | _ => throwError "Expected forall in implication pattern"
    
    -- If not a logical connective, check if it's an arithmetic operation
    -- Pattern: x + y, x * y, etc.
    trace[transfer] "Body is not a logical connective, checking for arithmetic pattern"
    trace[transfer] "Body: {body}"
    
    -- Check if body contains arithmetic operations
    if body.isAppOfArity ``HAdd.hAdd 6 || body.isAppOfArity ``Add.add 4 then
      -- Pattern: x + y where x and y might be germs
      trace[transfer] "Found addition pattern"
      -- For now, skip complex arithmetic handling
      
    -- If not arithmetic, check if it's a relation with a constant
    -- Pattern: ↑a ≤ x or x ≤ ↑a, etc.
    trace[transfer] "Body is not arithmetic, checking for relation pattern"
    trace[transfer] "Body: {body}"
    
    -- Check if body is a binary relation
    if body.isAppOfArity ``LE.le 4 || body.isAppOfArity ``Eq 3 then
      let args := body.getAppArgs
      let arg1 := args[args.size - 2]!
      let arg2 := args[args.size - 1]!
      
      trace[transfer] "Found relation, arg1: {arg1}, arg2: {arg2}"
      
      -- Check if one argument is .bvar 0 and the other is a constant
      let (constArg, isConstFirst) ← 
        if arg2 == .bvar 0 then
          pure (arg1, true)
        else if arg1 == .bvar 0 then
          pure (arg2, false)
        else
          throwError "Neither argument is bound variable 0"
      
      -- Check if constArg is a coercion
      trace[transfer] "Checking if {constArg} is a constant coercion"
      -- Debug: Let's see the exact structure of constArg
      trace[transfer] "constArg structure: app? = {constArg.isApp}, const? = {constArg.isConst}"
      if constArg.isApp then
        trace[transfer] "constArg function: {constArg.getAppFn}"
        trace[transfer] "constArg num args: {constArg.getAppNumArgs}"
        trace[transfer] "constArg args: {constArg.getAppArgs}"
      
      -- Also try to unfold the const directly
      let constArg' ← whnf constArg
      trace[transfer] "After whnf, constArg' = {constArg'}"
      match ← isCoeConst constArg with
      | some a =>
        trace[transfer] "Found constant coercion: {a}"
        
        -- Get the relation name
        let relName := bodyFn.constName?.get!
        
        -- Get the filter from context
        let ctx ← getLCtx
        let mut filterVar : Option Expr := none
        
        for decl in ctx do
          if !decl.isImplementationDetail then
            let declType ← instantiateMVars decl.type
            if declType.isAppOfArity ``Ultrafilter 1 then
              filterVar := some (mkFVar decl.fvarId)
              break
        
        match filterVar with
        | some l =>
          -- l is an Ultrafilter, but the theorem expects a Filter
          -- In the RHS we have (l : Filter ι).Germ α
          -- Extract the filter from the germ type in the RHS
          trace[transfer] "Found ultrafilter variable: {l}"
          
          -- ty is the type of the forall variable, e.g., (↑l).Germ α  
          trace[transfer] "Type of forall variable (ty): {ty}"
          -- Debug the structure
          if ty.isApp then
            trace[transfer] "ty is app, fn: {ty.getAppFn}, args: {ty.getAppArgs}"
          
          -- Extract the filter from the Germ type
          -- ty should be of the form Germ ι l α where l is the filter
          let filterExpr ← 
            if ty.isApp && ty.getAppFn.isConstOf ``Filter.Germ then
              let args := ty.getAppArgs
              if args.size == 3 then
                -- Germ takes 3 args: ι, filter, and α
                -- The filter is the second argument (index 1)
                pure args[1]!
              else
                throwError "Germ has unexpected number of arguments: {args.size}"
            else
              throwError "Cannot extract filter from type: {ty}"
          
          trace[transfer] "Extracted filter: {filterExpr}"
          let filterType ← inferType filterExpr
          trace[transfer] "Filter type: {filterType}"
          
          -- Apply the appropriate combined theorem directly
          -- The theorem signature is: {ι α} {l : Filter ι} [Preorder α] [l.NeBot] (a : α)
          let thm ← 
              if relName == ``LE.le then
                if isConstFirst then
                  mkAppOptM ``Filter.Germ.forall_le_const_iff_forall_germ_le #[none, none, some filterExpr, none, none, some a]
                else
                  mkAppOptM ``Filter.Germ.forall_const_le_iff_forall_germ_le #[none, none, some filterExpr, none, none, some a]
              else if relName == ``Eq then
                if isConstFirst then
                  mkAppOptM ``Filter.Germ.forall_eq_const_iff_forall_germ_eq #[none, none, some filterExpr, none, some a]
                else
                  mkAppOptM ``Filter.Germ.forall_const_eq_iff_forall_germ_eq #[none, none, some filterExpr, none, some a]
              else
                throwError "Unknown relation: {relName}"
            
            -- Check if the theorem exactly matches the goal
            let thmType ← inferType thm
            let target ← getMainTarget
            trace[transfer] "Applying relation theorem"
            trace[transfer] "Theorem type: {thmType}"
            trace[transfer] "Target: {target}"
            
            if ← isDefEq thmType target then
              -- The theorem exactly proves our goal
              trace[transfer] "Theorem exactly matches goal, closing with theorem"
              closeMainGoal `forallRelationRule thm
            else
              -- Try rewriting
              let goal ← getMainGoal
              let newGoals ← goal.rewrite target thm
              trace[transfer] "After applying relation rule, new goals: {newGoals.mvarIds}"
              replaceMainGoal newGoals.mvarIds
        | none => 
          throwError "Could not find ultrafilter in context"
      | none =>
        throwError "Relation does not involve a constant: {constArg}"
    else if body.isForall then
      -- Nested quantifier case: body is another ∀
      trace[transfer] "Found nested quantifier in RHS, body: {body}"
      -- For nested forall like ∀ x y, x = y
      -- We need to apply forall_forall_eq_iff_forall_forall_eq
      
      -- Check if the innermost body is an equality
      match body with
      | .forallE _ ty2 innerBody _ =>
        -- Check if ty2 is also a Germ type
        if ty2 == ty then  -- Both quantifiers are over the same type
          -- Check if innerBody is x = y where x and y are bound vars
          if innerBody.isAppOfArity ``Eq 3 then
            let args := innerBody.getAppArgs
            if args[1]! == .bvar 1 && args[2]! == .bvar 0 then
              -- Pattern matches ∀ x y, x = y
              -- Get the filter from context
              let ctx ← getLCtx
              let mut filterVar : Option Expr := none
              
              for decl in ctx do
                if !decl.isImplementationDetail then
                  let declType ← instantiateMVars decl.type
                  if declType.isAppOfArity ``Ultrafilter 1 then
                    filterVar := some (mkFVar decl.fvarId)
                    break
              
              match filterVar with
              | some l =>
                -- Extract the filter from the germ type
                let filterExpr ← 
                  if ty.isApp && ty.getAppFn.isConstOf ``Filter.Germ then
                    let args := ty.getAppArgs
                    if args.size == 3 then
                      pure args[1]!
                    else
                      throwError "Germ has unexpected number of arguments: {args.size}"
                  else
                    throwError "Cannot extract filter from type: {ty}"
                
                -- Apply the theorem forall_forall_eq_iff_forall_forall_eq
                -- The theorem has signature: {α : Type*} {ι : Type*} {l : Filter ι} [l.NeBot]
                -- Extract the types from the germ type
                let germArgs := ty.getAppArgs
                let ι := germArgs[0]!  -- First arg is ι
                let α := germArgs[2]!  -- Third arg is α
                trace[transfer] "Germ type args: {germArgs}"
                trace[transfer] "ι = {ι}, α = {α}, filterExpr = {filterExpr}"
                -- The filter expr type should match Filter ι
                let filterExprType ← inferType filterExpr
                trace[transfer] "filterExpr type = {filterExprType}"
                let inst ← synthInstance (← mkAppM ``Filter.NeBot #[filterExpr])
                let thm ← mkAppOptM ``Filter.Germ.forall_forall_eq_iff_forall_forall_eq 
                  #[some ι, some α, some filterExpr, some inst]
                
                -- Check if the theorem exactly matches the goal
                let thmType ← inferType thm
                let target ← getMainTarget
                trace[transfer] "Applying nested forall theorem"
                trace[transfer] "Theorem type: {thmType}"
                trace[transfer] "Target: {target}"
                
                if ← isDefEq thmType target then
                  trace[transfer] "Theorem exactly matches goal, closing with theorem"
                  closeMainGoal `forallForallRule thm
                else
                  -- Try rewriting
                  let goal ← getMainGoal
                  let newGoals ← goal.rewrite target thm
                  trace[transfer] "After applying nested forall rule, new goals: {newGoals.mvarIds}"
                  replaceMainGoal newGoals.mvarIds
              | none => 
                throwError "Could not find ultrafilter in context"
            else
              throwError "Nested forall body is not of the form x = y"
          else if innerBody.isAppOfArity ``Filter.Germ.LiftRel 5 || innerBody.isAppOfArity ``Germ.LiftRel 5 then
            -- Pattern for LiftRel r x y
            let args := innerBody.getAppArgs
            if args[2]! == .bvar 1 && args[3]! == .bvar 0 then
              -- Pattern matches ∀ x y, LiftRel r x y
              let r := args[1]!
              
              -- Get the filter from context
              let ctx ← getLCtx
              let mut filterVar : Option Expr := none
              
              for decl in ctx do
                if !decl.isImplementationDetail then
                  let declType ← instantiateMVars decl.type
                  if declType.isAppOfArity ``Ultrafilter 1 then
                    filterVar := some (mkFVar decl.fvarId)
                    break
              
              match filterVar with
              | some l =>
                -- Extract the filter from the germ type
                let filterExpr ← 
                  if ty.isApp && ty.getAppFn.isConstOf ``Filter.Germ then
                    let args := ty.getAppArgs
                    if args.size == 3 then
                      pure args[1]!
                    else
                      throwError "Germ has unexpected number of arguments: {args.size}"
                  else
                    throwError "Cannot extract filter from type: {ty}"
                
                -- Apply the theorem forall_forall_iff_forall_forall_liftRel
                -- Extract types from r
                let rType ← inferType r
                trace[transfer] "Relation type: {rType}"
                -- r has type α → β → Prop, extract α and β
                match rType with
                | .forallE _ α (.forallE _ β _ _) _ =>
                  -- Extract ι from the filter type
                  let germArgs := ty.getAppArgs
                  let ι := germArgs[0]!
                  let inst ← synthInstance (← mkAppM ``Filter.NeBot #[filterExpr])
                  let thm ← mkAppOptM ``Filter.Germ.forall_forall_iff_forall_forall_liftRel 
                    #[some ι, some α, some β, some filterExpr, some inst, some r]
                  
                  -- Check if the theorem exactly matches the goal
                  let thmType ← inferType thm
                  let target ← getMainTarget
                  trace[transfer] "Applying nested forall LiftRel theorem"
                  trace[transfer] "Theorem type: {thmType}"
                  trace[transfer] "Target: {target}"
                  
                  if ← isDefEq thmType target then
                    trace[transfer] "Theorem exactly matches goal, closing with theorem"
                    closeMainGoal `forallForallLiftRelRule thm
                  else
                    -- Try rewriting
                    let goal ← getMainGoal
                    let newGoals ← goal.rewrite target thm
                    trace[transfer] "After applying nested forall LiftRel rule, new goals: {newGoals.mvarIds}"
                    replaceMainGoal newGoals.mvarIds
                | _ => throwError "Relation does not have expected type: {rType}"
              | none => 
                throwError "Could not find ultrafilter in context"
            else
              throwError "Nested forall body is not of the form LiftRel r x y"
          else
            throwError "Nested forall body is not an equality or LiftRel"
        else
          throwError "Nested forall has different types"
      | _ => throwError "Expected nested forall"
    else
      throwError "RHS body is neither LiftPred, a logical connective, nor a supported relation: {body}"
  | .app (.app (.const ``Exists _) ty) (.lam _ _ body _) =>
    -- Handle exists case similar to forall
    trace[transfer] "RHS is exists with type: {ty}"
    
    -- Check if body is LiftPred
    let bodyFn := body.getAppFn
    if let some name := bodyFn.constName? then
      if name == ``Germ.LiftPred || name == ``Filter.Germ.LiftPred || name == ``LiftPred then
        -- Handle LiftPred case for exists
        let args := body.getAppArgs  
        if args.size >= 2 && args[args.size - 1]! == .bvar 0 then
          let p := args[args.size - 2]!
          
          -- Get the filter from context
          let ctx ← getLCtx
          let mut filterVar : Option Expr := none
          
          for decl in ctx do
            if !decl.isImplementationDetail then
              let declType ← instantiateMVars decl.type
              if declType.isAppOfArity ``Ultrafilter 1 then
                filterVar := some (mkFVar decl.fvarId)
                break
          
          match filterVar with
          | some l =>
            -- Extract α from the predicate p
            let pType ← inferType p
            match pType with
            | .forallE _ α _ _ =>
              let filterL ← mkAppM ``Ultrafilter.toFilter #[l]
              trace[transfer] "Calling existsRule with l={filterL}, α={α}"
              try
                existsRule filterL α
              catch e =>
                trace[transfer] "existsRule failed: {e.toMessageData}"
                throw e
            | _ => throwError "Could not extract type from predicate: {pType}"
          | none => throwError "Could not find ultrafilter in context"
        else
          throwError "RHS body does not match pattern: LiftPred <?> (.bvar 0)"
        return
    
    -- If not LiftPred, check if it's a logical connective
    trace[transfer] "Exists body is not LiftPred, checking for logical connective pattern"
    trace[transfer] "Body: {body}"
    
    -- Check if body is Or
    if body.isAppOfArity ``Or 2 then
      -- Body is: LiftPred p x ∨ LiftPred q x
      let arg1 := body.getArg! 0
      let arg2 := body.getArg! 1
      
      -- Check both args are LiftPred applications with .bvar 0
      let isLiftPred1 := arg1.isAppOfArity ``Filter.Germ.LiftPred 5 || 
                         arg1.isAppOfArity ``Germ.LiftPred 5 ||
                         arg1.isAppOfArity ``LiftPred 5
      let isLiftPred2 := arg2.isAppOfArity ``Filter.Germ.LiftPred 5 || 
                         arg2.isAppOfArity ``Germ.LiftPred 5 ||
                         arg2.isAppOfArity ``LiftPred 5
      
      if isLiftPred1 && isLiftPred2 && 
         arg1.getArg! 4 == .bvar 0 && arg2.getArg! 4 == .bvar 0 then
        let p := arg1.getArg! 3
        let q := arg2.getArg! 3
        
        -- Get the filter from context
        let ctx ← getLCtx
        let mut filterVar : Option Expr := none
        
        for decl in ctx do
          if !decl.isImplementationDetail then
            let declType ← instantiateMVars decl.type
            if declType.isAppOfArity ``Ultrafilter 1 then
              filterVar := some (mkFVar decl.fvarId)
              break
        
        match filterVar with
        | some l =>
          let filterL ← mkAppM ``Ultrafilter.toFilter #[l]
          let inst ← synthInstance (← mkAppM ``Filter.NeBot #[filterL])
          let thm ← mkAppOptM ``Filter.Germ.or_iff_or_liftPred 
            #[none, none, some filterL, some inst, some p, some q]
          
          let thmType ← inferType thm
          let target ← getMainTarget
          trace[transfer] "Applying or rule"
          trace[transfer] "Theorem type: {thmType}"
          trace[transfer] "Target: {target}"
          
          if ← isDefEq thmType target then
            closeMainGoal `existsOrRule thm
          else
            let goal ← getMainGoal
            let newGoals ← goal.rewrite target thm
            replaceMainGoal newGoals.mvarIds
        | none => throwError "Could not find ultrafilter in context"
      else
        throwError "Or body does not match pattern: LiftPred p x ∨ LiftPred q x"
      return
    
    -- If not Or, check if it's a relation with constant
    trace[transfer] "Body is not Or, checking for relation pattern"
    trace[transfer] "Body: {body}"
    
    -- Check if body is a binary relation
    if body.isAppOfArity ``LE.le 4 || body.isAppOfArity ``Eq 3 then
      let args := body.getAppArgs
      let arg1 := args[args.size - 2]!
      let arg2 := args[args.size - 1]!
      
      trace[transfer] "Found relation, arg1: {arg1}, arg2: {arg2}"
      
      -- Check if one argument is .bvar 0 and the other is a constant
      let (constArg, isConstFirst) ← 
        if arg2 == .bvar 0 then
          pure (arg1, true)
        else if arg1 == .bvar 0 then
          pure (arg2, false)
        else
          throwError "Neither argument is bound variable 0"
      
      -- Check if constArg is a coercion
      trace[transfer] "Checking if {constArg} is a constant coercion"
      let constArg' ← whnf constArg
      trace[transfer] "After whnf, constArg' = {constArg'}"
      match ← isCoeConst constArg with
      | some a =>
        trace[transfer] "Found constant coercion: {a}"
        
        -- Get the relation name
        let relName := bodyFn.constName?.get!
        
        -- Get the filter from context
        let ctx ← getLCtx
        let mut filterVar : Option Expr := none
        
        for decl in ctx do
          if !decl.isImplementationDetail then
            let declType ← instantiateMVars decl.type
            if declType.isAppOfArity ``Ultrafilter 1 then
              filterVar := some (mkFVar decl.fvarId)
              break
        
        match filterVar with
        | some l =>
          -- Extract the filter from the germ type in the RHS
          trace[transfer] "Found ultrafilter variable: {l}"
          trace[transfer] "Type of exists variable (ty): {ty}"
          
          let filterExpr ← 
            if ty.isApp && ty.getAppFn.isConstOf ``Filter.Germ then
              let args := ty.getAppArgs
              if args.size == 3 then
                pure args[1]!
              else
                throwError "Germ has unexpected number of arguments: {args.size}"
            else
              throwError "Cannot extract filter from type: {ty}"
          
          trace[transfer] "Extracted filter: {filterExpr}"
          
          -- Apply the appropriate combined theorem directly
          let thm ← 
            if relName == ``LE.le then
              if isConstFirst then
                mkAppOptM ``Filter.Germ.exists_le_const_iff_exists_germ_le #[none, none, some filterExpr, none, none, some a]
              else
                mkAppOptM ``Filter.Germ.exists_const_le_iff_exists_germ_le #[none, none, some filterExpr, none, none, some a]
            else if relName == ``Eq then
              if isConstFirst then
                mkAppOptM ``Filter.Germ.exists_eq_const_iff_exists_germ_eq #[none, none, some filterExpr, none, some a]
              else
                mkAppOptM ``Filter.Germ.exists_const_eq_iff_exists_germ_eq #[none, none, some filterExpr, none, some a]
            else
              throwError "Unknown relation: {relName}"
          
          -- Check if the theorem exactly matches the goal
          let thmType ← inferType thm
          let target ← getMainTarget
          trace[transfer] "Applying exists relation theorem"
          trace[transfer] "Theorem type: {thmType}"
          trace[transfer] "Target: {target}"
          
          if ← isDefEq thmType target then
            trace[transfer] "Theorem exactly matches goal, closing with theorem"
            closeMainGoal `existsRelationRule thm
          else
            -- Try rewriting
            let goal ← getMainGoal
            let newGoals ← goal.rewrite target thm
            trace[transfer] "After applying exists relation rule, new goals: {newGoals.mvarIds}"
            replaceMainGoal newGoals.mvarIds
        | none => 
          throwError "Could not find ultrafilter in context"
      | none =>
        throwError "Relation does not involve a constant: {constArg}"
    else
      throwError "Exists body is neither LiftPred, a logical connective, nor a supported relation: {body}"
  
  -- Handle logical connectives in RHS without quantifiers
  | .app (.app (.const ``And _) _) _ =>
    -- Pattern: LiftPred p x ∧ LiftPred q x
    trace[transfer] "Found And in RHS"
    -- Get the filter from context
    let ctx ← getLCtx
    let mut filterVar : Option Expr := none
    
    for decl in ctx do
      if !decl.isImplementationDetail then
        let declType ← instantiateMVars decl.type
        if declType.isAppOfArity ``Ultrafilter 1 then
          filterVar := some (mkFVar decl.fvarId)
          break
    
    match filterVar with
    | some l =>
      let filterL ← mkAppM ``Ultrafilter.toFilter #[l]
      -- Extract predicates from LHS
      match lhs with
      | .forallE _ _ body _ =>
        -- Extract p and q from (p x ∧ q x)
        if body.isAppOfArity ``And 2 then
          -- Apply and_iff_and_liftPred theorem
          let inst ← synthInstance (← mkAppM ``Filter.NeBot #[filterL])
          -- Need to extract p and q as lambdas
          let filterType ← inferType filterL
          let α := filterType.getArg! 0
          let extractedThm ← withLocalDecl `x .default α fun x => do
            let bodyWithVar := body.instantiate #[x]
            if bodyWithVar.isAppOfArity ``And 2 then
              let p1 := bodyWithVar.getArg! 0
              let p2 := bodyWithVar.getArg! 1
              let p ← mkLambdaFVars #[x] p1
              let q ← mkLambdaFVars #[x] p2
              mkAppOptM ``Filter.Germ.and_iff_and_liftPred 
                #[none, none, some filterL, some inst, some p, some q]
            else
              throwError "Could not extract predicates from And"
          let thmType ← inferType extractedThm
          let target ← getMainTarget
          if ← isDefEq thmType target then
            closeMainGoal `andRule extractedThm
          else
            let goal ← getMainGoal
            let newGoals ← goal.rewrite target extractedThm
            replaceMainGoal newGoals.mvarIds
        else
          throwError "LHS is not forall with And body"
      | _ => throwError "LHS is not a forall for And"
    | none => throwError "Could not find ultrafilter in context"
  
  | .app (.app (.const ``Or _) _) _ =>
    -- Pattern: LiftPred p x ∨ LiftPred q x
    trace[transfer] "Found Or in RHS"
    -- Similar to And case but for exists
    let ctx ← getLCtx
    let mut filterVar : Option Expr := none
    
    for decl in ctx do
      if !decl.isImplementationDetail then
        let declType ← instantiateMVars decl.type
        if declType.isAppOfArity ``Ultrafilter 1 then
          filterVar := some (mkFVar decl.fvarId)
          break
    
    match filterVar with
    | some l =>
      let filterL ← mkAppM ``Ultrafilter.toFilter #[l]
      -- Extract predicates from LHS
      match lhs with
      | .app (.app (.const ``Exists _) _) (.lam _ _ body _) =>
        -- Extract p and q from (p x ∨ q x)
        if body.isAppOfArity ``Or 2 then
          -- Apply or_iff_or_liftPred theorem
          let inst ← synthInstance (← mkAppM ``Filter.NeBot #[filterL])
          -- Need to extract p and q as lambdas
          let filterType ← inferType filterL
          let α := filterType.getArg! 0
          let extractedThm ← withLocalDecl `x .default α fun x => do
            let bodyWithVar := body.instantiate #[x]
            if bodyWithVar.isAppOfArity ``Or 2 then
              let p1 := bodyWithVar.getArg! 0
              let p2 := bodyWithVar.getArg! 1
              let p ← mkLambdaFVars #[x] p1
              let q ← mkLambdaFVars #[x] p2
              mkAppOptM ``Filter.Germ.or_iff_or_liftPred 
                #[none, none, some filterL, some inst, some p, some q]
            else
              throwError "Could not extract predicates from Or"
          let thmType ← inferType extractedThm
          let target ← getMainTarget
          if ← isDefEq thmType target then
            closeMainGoal `orRule extractedThm
          else
            let goal ← getMainGoal
            let newGoals ← goal.rewrite target extractedThm
            replaceMainGoal newGoals.mvarIds
        else
          throwError "LHS is not exists with Or body"
      | _ => throwError "LHS is not an exists for Or"
    | none => throwError "Could not find ultrafilter in context"
    
  | _ => throwError "RHS is not a forall or exists: {rhs}"

/-- Apply congruence rules to decompose the goal */
partial def transferCongr : TacticM Unit := withMainContext do
  let tgt ← getMainTarget
  let tgt ← instantiateMVars tgt
  trace[transfer] "transferCongr called with target: {tgt}"
  -- Match (_ ↔ _)
  if !tgt.isAppOfArity ``Iff 2 then
    trace[transfer] "transferCongr: target is not an iff"
    throwError "transferCongr: target is not an iff"
  let lhs := tgt.getArg! 0
  let rhs := tgt.getArg! 1
  trace[transfer] "transferCongr: lhs = {lhs}, rhs = {rhs}"
  
  -- Match patterns in LHS
  match lhs with
  | .forallE name ty body bi => do
    -- Check if ty is a Prop (for implication)
    let tyType ← inferType ty
    if tyType.isSort && tyType.sortLevel! == Level.zero then
      -- It's an implication
      evalTactic (← `(tactic| refine imp_congr ?_ ?_))
    else
      -- It's a proper forall
      evalTactic (← `(tactic| refine forall_congr' ?_; intro))
  
  | .app (.app (.const ``Exists _) _) _ => do
    evalTactic (← `(tactic| refine exists_congr ?_; intro))
  
  | .app (.app (.const ``And _) _) _ => do
    evalTactic (← `(tactic| refine and_congr ?_ ?_))
  
  | .app (.app (.const ``Or _) _) _ => do
    evalTactic (← `(tactic| refine or_congr ?_ ?_))
  
  | .app (.const ``Not _) _ => do
    evalTactic (← `(tactic| refine not_congr ?_))
  
  | .app (.app (.app (.const ``Eq _) _) _) _ => do
    evalTactic (← `(tactic| refine iff_of_eq (congrArg₂ (· = ·) ?_ ?_)))
  
  | _ => throwError "No known pattern applicable (step 2)"

end -- mutual

/-- Push liftPred inside logical operations */
def transferPushLift : TacticM Unit := withMainContext do
  let tgt ← getMainTarget
  let tgt ← instantiateMVars tgt
  -- Match (Filter.Germ.liftPred _ _ ↔ _)
  guard (tgt.isAppOfArity ``Iff 2)
  let lhs := tgt.getArg! 0
  
  -- Check if LHS is liftPred p x
  guard (lhs.isAppOfArity ``Filter.Germ.LiftPred 2)
  let p := lhs.getArg! 2
  let _ := lhs.getArg! 3
  
  -- Match patterns in p (which should be a lambda)
  match p with
  | .lam _ _ body _ =>
    -- Analyze the body
    match body with
    | .forallE _ _ _ _ => do
      -- Try different forall rules
      try
        let thm ← mkAppM ``Filter.Germ.liftPred_forall_iff_forall_liftPred' #[]
        let goal ← getMainGoal
        let newGoals ← goal.rewrite (← getMainTarget) thm
        replaceMainGoal newGoals.mvarIds
      catch _ =>
        let thm ← mkAppM ``Filter.Germ.liftPred_imp_iff_imp_liftPred #[]
        let goal ← getMainGoal
        let newGoals ← goal.rewrite (← getMainTarget) thm
        replaceMainGoal newGoals.mvarIds
    
    | .app (.const ``Not _) _ => do
      let thm ← mkAppM ``Filter.Germ.liftPred_not_iff_not_liftPred #[]
      let goal ← getMainGoal
      let newGoals ← goal.rewrite (← getMainTarget) thm
      replaceMainGoal newGoals.mvarIds
    
    | .app (.app (.app (.const ``Exists _) _) _) _ => do
      try
        let thm ← mkAppM ``Filter.Germ.liftPred_exists_iff_exists_liftPred' #[]
        let goal ← getMainGoal
        let newGoals ← goal.rewrite (← getMainTarget) thm
        replaceMainGoal newGoals.mvarIds
      catch _ =>
        try
          let thm ← mkAppM ``Filter.Germ.liftPred_exists_prop_iff_and_liftPred #[]
          let goal ← getMainGoal
          let newGoals ← goal.rewrite (← getMainTarget) thm
          replaceMainGoal newGoals.mvarIds
          evalTactic (← `(tactic| rw [exists_prop]))
        catch _ => throwError "Failed to apply exists rules"
    
    | .app (.app (.const ``LT.lt _) _) _ => do
      let thm ← mkAppM ``Filter.Germ.liftPred_lt_iff_lt_map #[]
      let goal ← getMainGoal
      let newGoals ← goal.rewrite (← getMainTarget) thm
      replaceMainGoal newGoals.mvarIds
    
    | .app (.app (.const ``GT.gt _) _) _ => do
      let thm ← mkAppM ``Filter.Germ.liftPred_lt_iff_lt_map #[]
      let goal ← getMainGoal
      let newGoals ← goal.rewrite (← getMainTarget) thm
      replaceMainGoal newGoals.mvarIds
    
    | .app (.app (.app (.const ``Eq _) _) _) _ => do
      let thm ← mkAppM ``Filter.Germ.liftPred_eq_iff_eq_map #[]
      let goal ← getMainGoal
      let newGoals ← goal.rewrite (← getMainTarget) thm
      replaceMainGoal newGoals.mvarIds
    
    | .app (.app (.const ``Ne _) _) _ => do
      let thm ← mkAppM ``Filter.Germ.liftPred_ne_iff_ne_map #[]
      let goal ← getMainGoal
      let newGoals ← goal.rewrite (← getMainTarget) thm
      replaceMainGoal newGoals.mvarIds
    
    | .app (.app (.const ``And _) _) _ => do
      let thm ← mkAppM ``Filter.Germ.liftPred_and_iff_and_liftPred #[]
      let goal ← getMainGoal
      let newGoals ← goal.rewrite (← getMainTarget) thm
      replaceMainGoal newGoals.mvarIds
    
    | .app (.app (.const ``Or _) _) _ => do
      let thm ← mkAppM ``Filter.Germ.liftPred_or_iff_or_liftPred #[]
      let goal ← getMainGoal
      let newGoals ← goal.rewrite (← getMainTarget) thm
      replaceMainGoal newGoals.mvarIds
    
    | _ => throwError "No known pattern applicable (step 3)"
  | _ => throwError "Expected lambda in liftPred"

/-- Apply induction on all germ variables in the context */
def transferInduction : TacticM Unit := do
  let goals ← getGoals
  let mut allNewGoals : List MVarId := []
  
  for goal in goals do
    let newGoals ← goal.withContext do
      let ctx ← getLCtx
      let mut foundGerm := false
      
      for decl in ctx do
        if decl.isImplementationDetail then continue
        let ty ← instantiateMVars decl.type
        let ty ← whnf ty
        -- Check if it's a germ type or Hyperreal
        let isGerm := ty.isAppOfArity ``Filter.Germ 2 || ty.isConstOf ``Hyperreal
        if isGerm && !foundGerm then
          foundGerm := true
          let fvar := mkFVar decl.fvarId
          -- Apply induction principle directly
          let inductThm ← mkAppM ``Filter.Germ.inductionOn #[fvar]
          try
            let newGoals ← goal.apply inductThm
            -- Introduce the new variable from induction
            match newGoals with
            | [g] => 
              let (_, g') ← g.intro `f
              return [g']
            | _ => return newGoals
          catch _ =>
            -- If induction fails, keep the original goal
            return [goal]
      
      if !foundGerm then
        -- No germ variables to induct on, keep the goal
        return [goal]
      else
        return []  -- Should not reach here
    
    allNewGoals := allNewGoals ++ newGoals
  
  replaceMainGoal allNewGoals

/-- Try to close the goal by induction and reflexivity */
def transferClose : TacticM Unit := do
  -- First try if the goal is trivial (e.g., True)
  try
    evalTactic (← `(tactic| trivial))
    return
  catch _ => pure ()
  
  -- Otherwise try induction and reflexivity
  transferInduction
  -- Only try rfl if we still have goals
  let goals ← getGoals
  if !goals.isEmpty then
    evalTactic (← `(tactic| rfl))

/-- One step of the transfer tactic */
def transferStep : TacticM Unit := do
  let tryTransferCongr : TacticM Unit := try transferCongr catch _ => pure ()
  
  trace[transfer] "Starting transferStep"
  try 
    transferClose
    trace[transfer] "transferClose succeeded"
  catch e1 =>
    trace[transfer] "transferClose failed, trying transferCongr"
    try 
      transferCongr
      trace[transfer] "transferCongr succeeded"
    catch e2 =>
      trace[transfer] "transferCongr failed, trying transferPushLift"
      try do
        transferPushLift
        tryTransferCongr
        trace[transfer] "transferPushLift succeeded"
      catch e3 => do
        trace[transfer] "transferPushLift failed, trying transferLiftLhs"
        try
          transferLiftLhs
          -- Only continue if there are still goals
          let goals ← getGoals
          if !goals.isEmpty then
            tryTransferCongr
          trace[transfer] "transferLiftLhs succeeded"
        catch e4 =>
          trace[transfer] "All transfer steps failed"
          -- Check if any of the errors is more informative
          let finalErr := match (e1, e2, e3, e4) with
            | (_, _, _, Exception.error _ msg) => msg
            | (_, _, Exception.error _ msg, _) => msg
            | (_, Exception.error _ msg, _, _) => msg
            | (Exception.error _ msg, _, _, _) => msg
            | _ => MessageData.ofFormat "All transfer steps failed"
          throwError "transfer tactic failed: {finalErr}"

/-- The main transfer tactic */
elab "transfer" : tactic => do
  -- Repeatedly apply transfer steps
  let rec loop : Nat → TacticM Unit
    | 0 => throwError "transfer tactic timeout"
    | n + 1 => do
      let goalsBefore ← getGoals
      trace[transfer] "Loop iteration {100 - n}, goals before: {goalsBefore.length}"
      if goalsBefore.isEmpty then
        trace[transfer] "No goals remaining, success!"
        return ()
      
      try
        transferStep
        -- Check if all goals are solved after the step
        let goalsAfter ← getGoals
        trace[transfer] "Goals after transferStep: {goalsAfter.length}"
        if goalsAfter.isEmpty then
          trace[transfer] "All goals solved!"
          return ()
        else if goalsAfter.length < goalsBefore.length then
          -- Made progress, continue
          trace[transfer] "Made progress, continuing"
          loop n
        else
          -- No progress, but maybe we can continue
          trace[transfer] "No progress in goal count, continuing"
          loop n
      catch e =>
        trace[transfer] "transferStep threw error: {e.toMessageData}"
        -- No more steps to apply, check if goal is solved
        let goals ← getGoals
        if goals.isEmpty then
          trace[transfer] "Goals solved despite error"
          return ()
        else
          -- If we still have goals and no progress, throw error
          throw e
  loop 100

end Mathlib.Tactic.Transfer