# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Build and Development Commands

### Essential Build Commands
- **Download cached build files**: `lake exe cache get` (run this first to avoid slow builds)
- **Build mathlib4**: `lake build`
- **Build specific file**: `lake build Mathlib.Path.To.File` (e.g., `lake build Mathlib.Tactic.Nonstandard.Transfer`)
- **Run all tests**: `lake test`
- **Clean build**: `lake clean` or `rm -rf .lake` (if mysterious issues occur)
- **Update Mathlib.lean after adding files**: `lake exe mk_all`

### Nonstandard Analysis Transfer Tactic Development
This repository contains an in-progress port of the nonstandard analysis transfer tactic from Lean 3 to Lean 4.

**Key files:**
- `Mathlib/Tactic/Nonstandard/Transfer.lean` - Main implementation
- `Mathlib/Tactic/Nonstandard/Complements/Germ.lean` - Transfer theorems for filter germs
- `Mathlib/Tactic/Nonstandard/Test/*.lean` - Test files

**Current status:** Basic forall case working. The tactic successfully applies `Filter.Germ.forall_iff_forall_liftPred` theorem.

### Development Workflow
1. Use `lake build` on specific files for faster iteration
2. Check for missing instances with `inferInstance` when debugging
3. Use `set_option trace.transfer true` to debug the transfer tactic
4. The tactic uses a registered trace class `transfer` for debugging

## Architecture Overview

### Mathlib4 Structure
This is the main mathematics library for Lean 4. Key architectural points:
- Follows strict style guidelines for naming, documentation, and formatting
- Uses Lake as the build system with dependency caching
- Integrates with CI/CD for automated testing and documentation generation

### Transfer Tactic Architecture
The transfer tactic converts statements about germs to equivalent statements about underlying types:

1. **Pattern matching on goal structure**: Identifies `(_ ↔ _)` goals with quantifiers over germ types
2. **Theorem application**: Uses rewriting with transfer theorems like `forall_iff_forall_liftPred`
3. **Expression handling**: 
   - Matches on `Filter.Germ` or `Hyperreal` types
   - Extracts predicates from `LiftPred` applications
   - Handles coercion from `Ultrafilter` to `Filter` via `Ultrafilter.toFilter`

### Key Differences from Standard Lean Development
- Non-forking contribution model: Request write access on Zulip instead of forking
- Heavy use of type class instances, especially `NeBot` for filters
- Expression pattern matching requires careful handling of:
  - Implicit arguments
  - Coercions (e.g., `Ultrafilter` to `Filter`)
  - Namespace resolution (e.g., `Filter.Germ.LiftPred` vs `Germ.LiftPred`)

### Common Issues and Solutions
- **"typeclass instance problem is stuck"**: Usually means `NeBot` instance needed for a filter
- **Pattern matching failures**: Use `whnf` to reduce expressions, check namespace prefixes
- **Theorem application failures**: Verify exact argument order and types match the theorem signature

## Next Steps for Transfer Tactic Development

### Immediate Tasks
1. **Fix the "failed" error message**: The tactic works but exits with "failed" when no goals remain. Need to handle empty goal list gracefully in the main loop.

2. **Support basic relations without LiftPred**:
   - Examples like `(∀ x, a ≤ x) ↔ (∀ x : l.Germ α, ↑a ≤ x)` 
   - Need to handle `≤`, `<`, `=`, `≠` directly without `LiftPred` wrapper
   - These appear in `TransferTest.lean` and currently fail

3. **Handle nested quantifiers**:
   - Example: `(∀ x y : α, x = y) ↔ (∀ x y : l.Germ α, x = y)`
   - Requires extending `transferLiftLhs` to handle multiple forall levels

4. **Support exists quantifier**:
   - Implement `existsRule` similar to `forallRule`
   - Use `Filter.Germ.exists_iff_exists_liftPred` theorem

### Medium-term Tasks
5. **Logical connectives**: Add support for `∧`, `∨`, `¬`, `→` in `transferCongr`

6. **Complex expressions with `Germ.map`**:
   - Handle cases like `Germ.map (fun x => |x|) (Germ.map u n - ↑l) < ε`
   - Need theorems for arithmetic operations on germs

7. **Hyperreal support**: 
   - Currently only handles generic `Filter.Germ`
   - Need specific support for `Hyperreal` type

### Testing Strategy
- Start with simple cases in `SimpleTransferTest.lean`
- Progress to more complex cases in `TransferTest.lean`
- Each new feature should have a corresponding test case

### Code Organization
- Keep the main tactic in `Transfer.lean`
- Add new transfer theorems to `Complements/Germ.lean`
- Consider splitting complex pattern matching into separate functions for maintainability