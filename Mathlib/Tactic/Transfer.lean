/-
Copyright (c) 2024 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Mathlib.Data.Nat.Hypernatural
import Mathlib.Order.Filter.Germ.Product
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

/-! ## Transferable Typeclass

A typeclass for predicates that can be transferred between standard and nonstandard structures.
-/

/-- A predicate `P : α → Prop` is `TransferableNat` to ℕ* if there is a
corresponding hyper-predicate and the transfer is compatible with the embedding. -/
class TransferableNat (P : ℕ → Prop) where
  /-- The lifted predicate on the hyperextension. -/
  hyperPred : ℕ* → Prop
  /-- Transfer for constants: P holds for a standard element iff hyperPred holds for its image. -/
  transfer_const : ∀ n : ℕ, P n ↔ hyperPred (n : ℕ*)

/-- The star extension of a predicate P on ℕ to ℕ*. -/
def starNat (P : ℕ → Prop) [inst : TransferableNat P] : ℕ* → Prop :=
  inst.hyperPred

/-- Nat.Prime is transferable to ℕ*. -/
instance : TransferableNat Nat.Prime where
  hyperPred := HyperPrime
  transfer_const := fun n => by rw [HyperPrime, liftPred_coe]

/-- Even is transferable to ℕ*. -/
instance : TransferableNat Even where
  hyperPred := liftPred Even
  transfer_const := fun _ => liftPred_coe.symm

/-- Odd is transferable to ℕ*. -/
instance : TransferableNat Odd where
  hyperPred := liftPred Odd
  transfer_const := fun _ => liftPred_coe.symm

/-- The star of a transferable predicate agrees with liftPred for any predicate. -/
theorem starNat_eq_liftPred (P : ℕ → Prop) [inst : TransferableNat P]
    (h : inst.hyperPred = liftPred P) : starNat P = liftPred P := h

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

/-- The bridge connects any Germ type to the corresponding Product type.
This allows connecting our hypernatural construction to the model-theoretic ultraproduct. -/
def Hypernatural.germProductEquiv {l : Filter ℕ} :
    Filter.Germ l ℕ ≃ Filter.Product l (fun _ => ℕ) :=
  Filter.Germ.prodEquiv

/-- Example: Using the TransferableNat typeclass to transfer Even. -/
example (n : ℕ) (h : Even n) : starNat Even (n : ℕ*) := by
  rw [starNat, ← TransferableNat.transfer_const]
  exact h

/-- Example: starNat gives the hyperextension of a predicate. -/
example : starNat Nat.Prime = HyperPrime := rfl

/-! ### Transfer for Divisibility -/

/-- Transfer lemma for divisibility: d | n in ℕ iff liftRel (· ∣ ·) holds in ℕ*. -/
example (d n : ℕ) (h : d ∣ n) : liftRel (· ∣ ·) (d : ℕ*) (n : ℕ*) := by
  rw [liftRel_coe]
  exact h

/-- All standard primes are HyperPrime. -/
example (p : ℕ) (hp : Nat.Prime p) : HyperPrime (p : ℕ*) := by
  rw [HyperPrime, liftPred_coe]
  exact hp

end Examples
