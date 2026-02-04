import Mathlib.Order.Filter.Germ.Star
import Mathlib.Tactic.Nonstandard

open Hyper NonstandardAnalysis Filter

/-- Verify countable saturation by proving existence of infinite hypernatural -/
example : ∃ ω : Hyper ℕ ℕ, ∀ n : ℕ, (★n : Hyper ℕ ℕ) < ω := by
  -- We use countable saturation for the family of predicates P_n(x) := x > n
  let P : ℕ → ℕ → Prop := fun n x => x > n
  -- Apply saturation
  saturation
  intro F
  -- For any finite set F, let m = max F. Then m + 1 > n for all n ∈ F.
  let m := F.sup id
  use ★(m + 1)
  intro n hn
  -- Goal is: liftPred (fun x ↦ x > n) (★(m + 1))
  transfer
  apply Nat.lt_succ_of_le
  apply Finset.le_sup hn

  -- The rest of the proof is about extracting the witness, which saturation handles
  -- But wait, saturation leaves the goal `∀ F, ...`.
  -- The original proof did `obtain ⟨ω, hω⟩ := countable_saturation hfin`.
  -- My tactic does `refine countable_saturation ?_`.
  -- So the goal becomes the hypothesis `hfin`.
  -- The user then proves `hfin`.
  -- After that, the original goal `∃ ω, ...` is solved.
  -- So I need to adjust the test to match this flow.

/-- Verify transfer handles `ofSeq` -/
example (f : ℕ → ℕ) : liftPred (fun x => x > 0) (ofSeq f) ↔ ∀ᶠ n in nonstandardUltrafilter ℕ, f n > 0 := by
  transfer
