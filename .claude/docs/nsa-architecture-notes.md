# NSA Architecture Notes

## Aristotle Files

The `*_aristotle.lean` files (Hypernatural_aristotle, Hyperrational_aristotle) contain AI-generated lemmas.

**Decision**: These are a useful generation tool, but results should be:
1. Reviewed for quality/correctness
2. Merged into mainline files if valuable
3. Scrapped if not useful (after committing to preserve work)

**Files**:
- `Mathlib/Data/Nat/Hypernatural_aristotle.lean` (~74 KB, 2100+ lemmas)
- `Mathlib/Data/Rat/Hyperrational_aristotle.lean` (~15 KB, 400+ lemmas)

## Unified Hyperstructure Abstraction

### Current Duplication Problem

We have parallel definitions across:
- `Hyper ι α` (general, in `Germ/Star.lean`)
- `Hyperreal` / `ℝ*` (specific, in `Hyperreal.lean`)
- `Hypernatural` / `ℕ*` (specific, in `Hypernatural.lean`)
- etc.

Each defines its own:
- `Infinitesimal` predicate
- `Infinite` predicate
- `st` (standard part function)
- `IsStandard` predicate

### Design Goal

Create a unified typeclass/abstraction that:
1. Works for any `Hyper ι α` where `α` has appropriate structure
2. Specializes cleanly to `ℝ*`, `ℕ*`, `ℚ*`, `ℤ*`
3. Captures the essential NSA operations once

### Standard Part Definition Considerations

Two approaches exist:
1. **Supremum-based** (current `Hyperreal.st`): `st x = sSup {r : ℝ | ↑r ≤ x}`
2. **Generic/algebraic** (current `Hyper.st`): Different construction

Questions to resolve:
- Which is more general?
- Which computes better?
- Can we have one definition that specializes to both?

## Unified Abstraction Design (Deep Think)

### Core Observation

There are two fundamentally different cases:

**Discrete types (ℕ, ℤ):**
- `IsSt x r` means `x = std r` (exact equality)
- Standard part only exists for standard elements
- No infinitesimals (every nonzero difference is infinite)

**Dense/Complete types (ℝ, ℚ, later ℂ):**
- `IsSt x r` means x is infinitely close to std r
- Standard part exists for finite (bounded) elements
- Infinitesimals exist

### Proposed Typeclass Hierarchy

```lean
/-- Basic nonstandard extension structure. -/
class NonstandardExtension (α : Type*) (α* : outParam Type*) where
  /-- Standard embedding -/
  std : α → α*
  /-- Std is injective -/
  std_injective : Function.Injective std

/-- "x is standard to r" predicate -/
class HasIsSt (α : Type*) (α* : Type*) [NonstandardExtension α α*] where
  /-- The "is standard to" relation -/
  IsSt : α* → α → Prop
  /-- Standard elements are standard to themselves -/
  isSt_std : ∀ a, IsSt (NonstandardExtension.std a) a
  /-- At most one standard part -/
  isSt_unique : ∀ x r s, IsSt x r → IsSt x s → r = s

/-- Standard part function (general). -/
class HasStandardPart (α : Type*) (α* : Type*) [NonstandardExtension α α*] [HasIsSt α α*] where
  /-- Predicate for having a standard part -/
  HasSt : α* → Prop
  /-- Every standard element has a standard part -/
  hasSt_std : ∀ a, HasSt (NonstandardExtension.std a)
  /-- Standard part function (noncomputable, uses choice) -/
  st : α* → α
  /-- st is correct when it exists -/
  isSt_st : ∀ x, HasSt x → HasIsSt.IsSt x (st x)

/-- For types with infinitesimals (dense ordered types). -/
class HasInfinitesimals (α : Type*) (α* : Type*) [Zero α]
    [NonstandardExtension α α*] [HasIsSt α α*] where
  /-- x is infinitesimal iff IsSt x 0 -/
  Infinitesimal : α* → Prop := fun x => HasIsSt.IsSt x 0
```

### Standard Part: Two Approaches

1. **Supremum-based** (in `Hyper.st`):
   ```lean
   st x := sSup {r : α | std r ≤ x}
   ```
   - Requires: `ConditionallyCompleteLinearOrder α`
   - Works for: ℝ, ℚ, and even ℕ, ℤ with discrete order
   - For discrete: gives exact value when x is standard
   - For dense: gives standard part of finite elements
   - **This is the more general definition**

2. **Choice-based** (in type-specific files):
   ```lean
   st x := if h : ∃ r, IsSt x r then Classical.choose h else 0
   ```
   - More flexible about what `IsSt` means
   - Falls back to default for elements without standard part

**Recommendation**: Use supremum-based as primary, derive type-specific ones as special cases.

### Unification Strategy

1. Keep `Hyper ι α` as the universal framework in `Star.lean`
2. Define typeclasses for `NonstandardExtension`, `HasIsSt`, etc.
3. Make `ℝ*`, `ℕ*`, etc. instances of these classes
4. Prove that type-specific `st` agrees with general `Hyper.st`
5. Delete duplicate code from specific files, replacing with instances

### For Hypercomplex (ℂ*)

Since ℂ is not ordered, supremum-based `st` won't work directly.
Options:
1. Define `st` component-wise: `st z = (st z.re, st z.im)`
2. Use norm-based characterization
3. Lean into type-specific definition

Best: Component-wise, then prove it matches the IsSt relation.

## TODO

- [ ] Audit aristotle files for useful lemmas
- [ ] Implement `NonstandardExtension` typeclass
- [ ] Make hyperstructures instances
- [ ] Unify standard part definitions
- [ ] Add `Hypercomplex` (`ℂ*`)
