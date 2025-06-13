import Mathlib.Tactic.Nonstandard.Transfer

open Filter

set_option trace.transfer true

-- Test nested quantifier with a more reasonable predicate
example (ι : Type*) (l : Ultrafilter ι) (r : ℕ → ℕ → Prop) : 
  (∀ x y, r x y) ↔ (∀ x y : (l : Filter ι).Germ ℕ, Filter.Germ.LiftRel r x y) := by
  transfer

-- Test with equality - this should work for the special case
example (ι : Type*) (l : Ultrafilter ι) : 
  (∀ x y : ℕ, x = y) ↔ (∀ x y : (l : Filter ι).Germ ℕ, x = y) := by
  transfer