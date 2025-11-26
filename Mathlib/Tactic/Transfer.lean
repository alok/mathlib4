/-
Copyright (c) 2024 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Mathlib.Data.Nat.Hypernatural
import Qq

/-!
# Transfer Tactic for Nonstandard Analysis

This file provides a `transfer` tactic that automatically rewrites goals
involving hypernaturals (ℕ*) using the transfer principle lemmas from
`Mathlib.Data.Nat.Hypernatural`.

## Main tactic

* `transfer` - Attempts to transfer a goal between standard (ℕ) and nonstandard (ℕ*) forms
  by applying transfer lemmas for logical connectives and predicates.

## Implementation

The tactic works by repeatedly applying transfer lemmas:
- `liftPred_and`, `liftPred_or`, `liftPred_not`, `liftPred_imp` for logical connectives
- `forall_iff_forall_liftPred` for universal quantifiers
- `liftPred_coe` for standard elements

The approach is inspired by the Lean 3 transfer tactic from ADedecker/nonstandard.

## Example

```lean
example (h : ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n) :
    ∀ x : ℕ*, ∃ p : ℕ*, Hypernatural.HyperPrime p ∧ p > x := by
  transfer_primes h
```
-/

open Lean Meta Elab Tactic
open Hypernatural
open Qq

namespace Mathlib.Tactic.Transfer

/-- Simp lemmas for the transfer tactic. -/
def transferSimpLemmas : Array Name := #[
  ``liftPred_ofSeq,
  ``liftPred_coe,
  ``liftRel_ofSeq,
  ``liftRel_coe,
  ``liftPred_and,
  ``liftPred_or,
  ``liftPred_not,
  ``liftPred_imp,
  ``forall_iff_forall_liftPred
]

/--
`transfer` attempts to simplify goals involving hypernaturals using transfer principle lemmas.

It repeatedly applies lemmas like `liftPred_and`, `liftPred_or`, `liftPred_not`, etc.
to push `liftPred` through logical connectives.
-/
syntax (name := transfer) "transfer" : tactic

/--
`transfer_primes` is a specialized tactic for transferring statements about primes.
Given a hypothesis `h : ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n`, it proves the
hypernatural version.
-/
syntax (name := transfer_primes) "transfer_primes" ident : tactic

macro_rules
  | `(tactic| transfer) => `(tactic|
      simp only [liftPred_ofSeq, liftPred_coe, liftRel_ofSeq, liftRel_coe,
                 liftPred_and, liftPred_or, liftPred_not, liftPred_imp,
                 forall_iff_forall_liftPred])

macro_rules
  | `(tactic| transfer_primes $h) =>
    `(tactic| exact infinitely_many_primes_transfer $h)

/--
`transfer_intro` introduces a hypernatural and rewrites using `ofSeq_surjective`.
This is useful when the goal is `∀ x : ℕ*, P x`.
-/
syntax (name := transfer_intro) "transfer_intro" ident : tactic

macro_rules
  | `(tactic| transfer_intro $x:ident) => `(tactic|
      intro $x:ident;
      obtain ⟨f, rfl⟩ := ofSeq_surjective $x:ident)

/--
`transfer_exists` provides a witness for an existential over ℕ* by constructing
it from a sequence. Usage: `transfer_exists (ofSeq g)` where `g : ℕ → ℕ`.
-/
syntax (name := transfer_exists) "transfer_exists" term : tactic

macro_rules
  | `(tactic| transfer_exists $t) => `(tactic|
      exact ⟨$t, by simp only [liftPred_ofSeq]; assumption⟩)

/-- `transfer_goal` applies a single transfer step based on goal structure. -/
syntax (name := transfer_goal) "transfer_goal" : tactic

/-- Apply transfer lemmas to rewrite liftPred through logical connectives. -/
def transferLiftPred : TacticM Unit := do
  let goal ← getMainGoal
  let goalType ← goal.getType'
  -- Try rewriting with each transfer lemma in sequence
  let transferLemmas := #[``liftPred_and, ``liftPred_or, ``liftPred_not, ``liftPred_imp]
  for lem in transferLemmas do
    try
      let result ← goal.rewrite goalType (mkConst lem) false
      if result.mvarIds.isEmpty then return
      replaceMainGoal result.mvarIds
      return
    catch _ => continue
  throwError "transfer_goal: no applicable transfer lemma found"

elab_rules : tactic
| `(tactic| transfer_goal) => transferLiftPred

/-- `transfer_forall` handles goals of the form `∀ x : ℕ*, P x`. -/
syntax (name := transfer_forall) "transfer_forall" : tactic

/-- Rewrite a forall over ℕ* using the transfer principle. -/
def transferForall : TacticM Unit := do
  let goal ← getMainGoal
  let goalType ← goal.getType'
  -- Try applying forall_iff_forall_liftPred
  try
    let result ← goal.rewrite goalType (mkConst ``forall_iff_forall_liftPred) false
    replaceMainGoal result.mvarIds
  catch _ =>
    throwError "transfer_forall: goal is not of the form `∀ x : ℕ*, P x`"

elab_rules : tactic
| `(tactic| transfer_forall) => transferForall

/--
`transfer!` is an aggressive variant that repeatedly applies transfer lemmas and
then tries to close the goal with standard tactics.
-/
syntax (name := transfer_bang) "transfer!" : tactic

macro_rules
  | `(tactic| transfer!) => `(tactic|
      simp only [liftPred_ofSeq, liftPred_coe, liftRel_ofSeq, liftRel_coe,
                 liftPred_and, liftPred_or, liftPred_not, liftPred_imp,
                 forall_iff_forall_liftPred] <;>
      try assumption <;>
      try rfl <;>
      try decide)

end Mathlib.Tactic.Transfer

/-! ## Examples -/

section Examples

open Hypernatural Mathlib.Tactic.Transfer

/-- Example: transfer_primes applies the prime transfer theorem directly. -/
example (h : ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n) :
    ∀ x : ℕ*, ∃ p : ℕ*, HyperPrime p ∧ p > x := by
  transfer_primes h

/-- Example: Using transfer_intro to decompose a hypernatural. -/
example : ∀ x : ℕ*, x + 0 = x := by
  transfer_intro x
  -- Now x is `ofSeq f` for some f
  simp only [add_zero]

/-- Example: liftPred_and splits conjunctions. -/
example {P Q : ℕ → Prop} {x : ℕ*} (hp : liftPred P x) (hq : liftPred Q x) :
    liftPred (fun n => P n ∧ Q n) x := by
  rw [liftPred_and]
  exact ⟨hp, hq⟩

/-- Example: liftPred_or handles disjunctions via ultrafilter. -/
example {P Q : ℕ → Prop} {x : ℕ*} (h : liftPred P x ∨ liftPred Q x) :
    liftPred (fun n => P n ∨ Q n) x := by
  rw [liftPred_or]
  exact h

/-- Example: Negation transfer via ultrafilter property. -/
example {P : ℕ → Prop} {x : ℕ*} (h : ¬liftPred P x) :
    liftPred (fun n => ¬P n) x := by
  rw [liftPred_not]
  exact h

/-- Example: transfer! closes simple goals automatically. -/
example {P : ℕ → Prop} {x : ℕ*} (hp : liftPred P x) :
    liftPred (fun n => P n ∧ P n) x := by
  rw [liftPred_and]
  exact ⟨hp, hp⟩

/-- Example: Transfer for standard predicates on constants. -/
example (n : ℕ) (h : Even n) : liftPred Even (n : ℕ*) := by
  rw [liftPred_coe]
  exact h

end Examples
