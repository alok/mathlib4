import Canonical
import Mathlib.Tactic.Nonstandard.Transfer
import Mathlib.Tactic.Nonstandard.Complements.Germ

/-!
# Using Canonical to Search for Transfer Proofs

This demonstrates using canonical as a search mechanism to find proofs
that our transfer tactic can handle.
-/

open Filter Germ

-- Search for simple transfer theorems
example (α ι : Type*) (l : Ultrafilter ι) (p : α → Prop) : 
  (∀ x, p x) ↔ (∀ x : (l : Filter ι).Germ α, LiftPred p x) := by
  canonical [Filter.Germ.forall_iff_forall_liftPred]

-- Search for logical connective transfers
example (α ι : Type*) (l : Ultrafilter ι) (p q : α → Prop) : 
  (∀ x, p x ∧ q x) ↔ (∀ x : (l : Filter ι).Germ α, LiftPred p x ∧ LiftPred q x) := by
  canonical [Filter.Germ.and_iff_and_liftPred]

-- Search for relation transfers
example (α ι : Type*) [Preorder α] (l : Ultrafilter ι) (a : α) : 
  (∀ x, a ≤ x) ↔ (∀ x : (l : Filter ι).Germ α, ↑a ≤ x) := by
  canonical [Filter.Germ.forall_le_const_iff_forall_germ_le]

-- Search for nested quantifier transfers
example (α ι : Type*) (l : Ultrafilter ι) : 
  (∀ x y : α, x = y) ↔ (∀ x y : (l : Filter ι).Germ α, x = y) := by
  canonical [Filter.Germ.forall_forall_eq_iff_forall_forall_eq]

-- Let canonical find a proof strategy for arithmetic
example (α ι : Type*) [Add α] (l : Ultrafilter ι) (f g : l.Germ α) :
  Germ.map (· + ·) (prodEquiv l (f, g)) = f + g := by
  canonical [Filter.Germ.map_add_iff_add_map]

-- Search for exists transfers
example (α ι : Type*) (l : Ultrafilter ι) (p : α → Prop) : 
  (∃ x, p x) ↔ (∃ x : (l : Filter ι).Germ α, LiftPred p x) := by
  canonical [Filter.Germ.exists_iff_exists_liftPred]

-- Complex example: Let canonical find the proof path
example (α ι : Type*) (l : Ultrafilter ι) (p : α → Prop) (h : ∀ x, p x) :
  ∀ x : (l : Filter ι).Germ α, LiftPred p x := by
  canonical [Filter.Germ.forall_iff_forall_liftPred, h]