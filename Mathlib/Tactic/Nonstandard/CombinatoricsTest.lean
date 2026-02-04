import Mathlib.Order.Filter.Germ.Star

open Hyper

-- Verify instances
-- example : LinearOrderedCommSemiring (Hyper ℕ ℕ) := inferInstance
-- example : OrderedSemiring (Hyper ℕ ℕ) := inferInstance

-- Verify omega properties
example (n : ℕ) : (std n : Hyper ℕ ℕ) < omega := omega_gt_std _

-- Verify factorial
example : factorial (std 5 : Hyper ℕ ℕ) = std 120 := by
  rw [factorial_std]
  rfl

-- Verify pow
example : pow (std 2 : Hyper ℕ ℕ) (std 3) = std 8 := by
  rw [pow_std]
  rfl



-- Better test with inductionOn
example (n : Hyper ℕ ℕ) : 1 ≤ factorial n := by
  induction n using inductionOn with | h f =>
  rw [factorial, lift_ofSeq]
  have : (1 : Hyper ℕ ℕ) = std 1 := rfl
  rw [this, std_eq_ofSeq_const]
  change liftRel (· ≤ ·) (ofSeq fun _ => 1) (ofSeq (Nat.factorial ∘ f))
  rw [liftRel_ofSeq]
  filter_upwards with i
  exact Nat.factorial_pos (f i)
