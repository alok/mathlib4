import Mathlib.Tactic.Nonstandard.Transfer

open Filter

-- Test the transfer tactic with simple examples
-- set_option trace.transfer false
example (α ι : Type*) [Preorder α] (l : Ultrafilter ι) (a : α) : 
  (∀ x, a ≤ x) ↔ (∀ x : (l : Filter ι).Germ α, ↑a ≤ x) := by
  transfer
-- set_option trace.transfer false

example (α ι : Type*) [Preorder α] (l : Ultrafilter ι) (a : α) : 
  (∀ x y : α, x = y) ↔ (∀ x y : (l : Filter ι).Germ α, x = y) := by
  transfer

open Germ

example (l : ℝ) (u : ℕ → ℝ) :
  (∀ ε > 0, ∃ N ≥ (1 : ℕ), ∀ n ≥ N, |u n - l| < ε) ↔
  (∀ ε > 0, ∃ N ≥ (1 : (hyperfilter ℕ : Filter ℕ).Germ ℕ), ∀ n ≥ N, Germ.map (fun x => |x|) (Germ.map u n - ↑l) < ε) := by
  transfer