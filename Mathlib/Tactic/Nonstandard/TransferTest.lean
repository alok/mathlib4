/-
Copyright (c) 2024 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Mathlib.Tactic.Nonstandard.Transfer
import Mathlib.Data.Real.Basic

/-!
# Transfer Tactic Tests

This file tests the `transfer` tactic for nonstandard analysis.
-/

open Hyper

-- Use ℕ as the index type for concrete examples
abbrev HReal := Hyper ℕ ℝ

/-! ## Arithmetic transfer -/

-- These are proved by `transfer` alone (reduces to reflexivity)
example (a b : ℝ) : (std (a + b) : HReal) = std a + std b := by transfer

example (a b : ℝ) : (std (a * b) : HReal) = std a * std b := by transfer

example (a : ℝ) : (std (-a) : HReal) = -std a := by transfer

example (a b : ℝ) : (std (a - b) : HReal) = std a - std b := by transfer

/-! ## Order transfer -/

example (a b : ℝ) : (std a : HReal) ≤ std b ↔ a ≤ b := by transfer

example (a b : ℝ) : (std a : HReal) < std b ↔ a < b := by transfer

/-! ## Predicate transfer -/

example (P : ℝ → Prop) (a : ℝ) : liftPred P (std a : HReal) ↔ P a := by transfer

example (R : ℝ → ℝ → Prop) (a b : ℝ) :
    liftRel R (std a : HReal) (std b) ↔ R a b := by transfer

/-! ## Logical connectives -/

example (P Q : ℝ → Prop) (x : HReal) :
    liftPred (fun a => P a ∧ Q a) x ↔ liftPred P x ∧ liftPred Q x := by transfer

example (P Q : ℝ → Prop) (x : HReal) :
    liftPred (fun a => P a ∨ Q a) x ↔ liftPred P x ∨ liftPred Q x := by transfer

example (P : ℝ → Prop) (x : HReal) :
    liftPred (fun a => ¬P a) x ↔ ¬liftPred P x := by transfer

/-! ## Quantifier transfer -/

-- The main transfer theorem: standard quantification ↔ hyperfinite quantification
example (P : ℝ → Prop) : (∀ a : ℝ, P a) ↔ (∀ x : HReal, liftPred P x) := by
  exact Hyper.forall_std_iff P

/-! ## Combined examples -/

-- Transferring a concrete statement
example (a b : ℝ) (h : a ≤ b) : (std a : HReal) ≤ std b := by
  rw [std_le_std]
  exact h

-- This shows how transfer can simplify goals involving std
example (a b : ℝ) : (std a : HReal) + std b = std (a + b) := by
  rw [← std_add]
