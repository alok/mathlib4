import Mathlib.Tactic.Nonstandard
import Mathlib.Order.Filter.Germ.Star

open Hyper NonstandardAnalysis

variable {ι : Type*} [Infinite ι] {α : Type*}

/-- Test transfer of universal quantifier -/
example (P : α → Prop) : (∀ a : α, P a) → (∀ x : Hyper ι α, x ⦦★ P) := by
  intro h
  transfer at h
  exact h

/-- Test transfer of existential quantifier -/
example (P : α → Prop) : (∃ a : α, P a) → (∃ x : Hyper ι α, IsStandard x ∧ x ⦦★ P) := by
  intro h
  transfer at h
  exact h

/-- Test transfer of algebraic properties -/
example [AddGroup α] (a b : α) : (★(a + b) : Hyper ι α) = ★a + ★b := by
  transfer

example [Ring α] (a b : α) : (★(a * b) : Hyper ι α) = ★a * ★b := by
  transfer

/-- Test transfer of order properties -/
example [LinearOrder α] (a b : α) : (★a : Hyper ι α) ≤ ★b ↔ a ≤ b := by
  transfer

/-- Test complex logical statement -/
example (P Q : α → Prop) : (∀ a : α, P a → Q a) → (∀ x : Hyper ι α, x ⦦★ P → x ⦦★ Q) := by
  intro h
  transfer
  exact h

/-- Test transfer at location -/
example (P : α → Prop) (h : ∀ a : α, P a) : ∀ x : Hyper ι α, x ⦦★ P := by
  transfer at h
  exact h
