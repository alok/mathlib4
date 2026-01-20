# NSA Ultrapower Design Note (Draft)

## Summary
This note proposes decoupling the NSA core from the specific `hyperfilter` by introducing an
ultrafilter-generic ultrapower. The goal is to make the core API work for arbitrary ultrafilters
and then recover the current `Hyper` as a default instance. This supports specialized ultrafilter
properties (idempotent, minimal, saturated) and clean handling of iterated ultrapowers.

## Goals
- Provide a core type `Ultrapower U alpha` parameterized by an ultrafilter `U`.
- Keep existing `Hyper` as a backward-compatible abbrev using `hyperfilter`.
- Introduce a small set of neutral, accurate names (`ultraConst`, `ultrafilterOf`, `mapPred`, ...).
- Make saturation assumptions explicit via a typeclass, not hard-coded cardinals.
- Clarify the correct notion of iterated ultrapower (curried filter), not implicitly the product
  index ultrafilter.

## Non-goals
- Remove `hyperfilter` immediately. It remains as a default choice.
- Rewrite all existing NSA theorems in one pass.
- Change notation or break the current `Hyper` namespace right away.

## Core API (generic in U)
- Type: `Filter.Ultrapower (U : Ultrafilter iota) (alpha : Type*) := Germ (U : Filter iota) alpha`.
- Constants: `ultraConst : alpha -> Ultrapower U alpha` (alias of `Germ.const`).
- Maps: `map`, `map2`, `mapPred`, `mapRel` (aliases of `Germ.map`, `Germ.map2`, `Germ.LiftPred`,
  `Germ.LiftRel`).
- `ultrafilterOf : Ultrapower U alpha -> Ultrafilter alpha` (map of the representative function).
- `Realizes x F : Prop := F <= ultrafilterOf x`.

## Backward compatibility
- `abbrev Hyper (iota : Type*) [Infinite iota] (alpha : Type*) := Ultrapower (hyperfilter iota) alpha`.
- Keep `Hyper.std`, `Hyper.lift`, etc. as aliases for the new generic names.
- Deprecate old names gradually, but keep for now to avoid churn.

## Saturation as a typeclass
Hide cardinal bookkeeping behind a single class:
```
class Saturated (U : Ultrafilter iota) (kappa : Type*) : Prop :=
  (sat : ...)

abbrev CountablySaturated (U : Ultrafilter iota) : Prop := Saturated U Nat
```
Provide instances from existing `cardinal_saturation` and `countable_saturation`.
Backward directions in NSA theorems should ask for `[Saturated U kappa]` or
`[CountablySaturated U]` rather than explicit `Nonempty (Embedding kappa iota)`.

## Iterated ultrapowers
One level of iteration should be expressed via the curried filter:
```
Ultrapower U (Ultrapower V alpha)
  ~= Germ ((U : Filter iota).curry (V : Filter kappa)) alpha
```
This is the correct abstract equivalence. It does not identify the iterated ultrapower
with `Ultrapower (hyperfilter (Prod iota kappa)) alpha` unless that ultrafilter is explicitly chosen.

## Migration plan
1) Add `Ultrapower` type and basic operations (no refactors).
2) Add `Saturated` classes and instances (no rewrites yet).
3) Add iterated ultrapower equivalence via `Filter.curry`.
4) Gradually port NSA theorems to use `Ultrapower` + saturation classes.
5) Keep `Hyper` as default, but allow other ultrafilters (idempotent, etc.).

## Open questions
- Final naming of `ultraConst` vs `const` vs `std`.
- Whether to keep `Hyper` namespace as main user-facing entry point.
- Where to place the `Ultrapower` file (proposed: `Order/Filter/Germ/Ultrapower`).
- Whether to add scoped notation for the generic star/monad in the new namespace.
