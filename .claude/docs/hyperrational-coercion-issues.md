# Hyperrational Coercion Issues

## Summary

During development of the Hyperrational API (inspired by Hyperreal), we encountered persistent type system issues with coercion lemmas that work correctly for Hyperreal and Hypernatural but fail for Hyperrational.

## The Pattern That Works (Hyperreal)

```lean
-- In Hyperreal.lean (WORKS)
@[simp, norm_cast]
theorem coe_eq_coe {x y : ℝ} : (x : ℝ*) = y ↔ x = y :=
  Germ.const_inj
```

## The Pattern That Fails (Hyperrational)

```lean
-- In Hyperrational.lean (FAILS)
@[simp, norm_cast]
theorem coe_eq_coe {x y : ℚ} : (x : ℚ*) = y ↔ x = y :=
  Germ.const_inj  -- Type mismatch error
```

## Error Messages

The typical error encountered:

```
error: Type mismatch
  const_inj
has type
  ↑?m.7 = ↑?m.8 ↔ ?m.7 = ?m.8
but is expected to have type
  ↑x = ↑y ↔ x = y
```

## Attempted Fixes

1. **Variable renaming** (x/y to a/b): No effect
2. **Explicit type annotations**: Still failed
3. **Matching Hyperreal pattern exactly**: Still failed
4. **Different approaches to `const_inj`**: All failed

## Current Status

As of 2025-11-24, Hyperrational.lean has 81 errors, mostly related to coercion lemmas. The file compiles with errors commented out.

## Hypothesis

The issue may be related to how `ℚ` interacts with the Germ/Ultrafilter construction differently than `ℕ` or `ℝ`. Possible factors:
- ℚ's quotient structure (as pairs of integers)
- Different decidability instances
- Interaction with algebraic hierarchy

## Next Steps

1. Investigate why `Germ.const_inj` works for ℝ and ℕ but not ℚ
2. Check if there are missing instances for ℚ in the filter/germ infrastructure
3. Consider whether ℚ* needs a different construction pattern
4. Review Mathlib's treatment of quotients with ultrafilters

## References

- `/Users/alokbeniwal/mathlib4/Mathlib/Data/Rat/Hyperrational.lean`
- `/Users/alokbeniwal/mathlib4/Mathlib/Analysis/Real/Hyperreal.lean`
- `/Users/alokbeniwal/mathlib4/Mathlib/Data/Nat/Hypernatural.lean`
- Mathlib naming conventions: https://leanprover-community.github.io/contribute/naming.html
