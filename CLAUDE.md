# CLAUDE.md

## Build Commands
- Build Star.lean: `lake build Mathlib.Order.Filter.Germ.Star`
- Build CombinatoricsTest: `lake build Mathlib.Tactic.Nonstandard.CombinatoricsTest`
- Build All: `lake build`

## Todo List
- [ ] Break out of mathlib into its own repo that uses mathlib as upstream dep
- [ ] Explore `fun_trans` integration
- [ ] Generalize `factorial_std`: Prove that std-ness is preserved under forward image and std functions commute with std part (general principle instead of specific theorems)
