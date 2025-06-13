import Canonical
import Mathlib.Tactic.Nonstandard.HyperfiniteInduction
import Mathlib.Tactic.Nonstandard.Transfer

/*
# Testing Canonical with Nonstandard Analysis

This file demonstrates using the canonical tactic to search for proofs 
in nonstandard analysis.
*/

open Filter Germ Hypernat

-- Example 1: Search for standard hypernaturals
example : ∃ n : Hypernat, n.IsStandard := by
  canonical

-- Example 2: Search for properties of omega
example : ∃ n : Hypernat, n.IsInfinite := by
  canonical [omega_infinite]

-- Example 3: Search for arithmetic properties
example : ∃ n : Hypernat, n + 1 > n := by
  canonical

-- Example 4: Search for transfer theorem applications
example (p : ℕ → Prop) : (∀ n : ℕ, p n) → (∀ n : Hypernat, n.IsStandard → ∃ m : ℕ, n = ↑m ∧ p m) := by
  canonical [Hypernat.transfer]

-- Example 5: Search for internal predicates
example : ∃ p : Hypernat → Prop, IsInternal p := by
  canonical

-- Example 6: Enumerate hypernaturals
example : List Hypernat := by
  canonical (count := 5)

-- Example 7: Search for proofs about standard part
example (n : Hypernat) (h : n.IsStandard) : n.standardPart.isSome := by
  canonical [standardPart_isSome_iff]