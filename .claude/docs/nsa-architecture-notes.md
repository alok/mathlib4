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

### Standard Part: The Most General Definition

**The topological definition is most general** (already exists in codebase!):

```lean
-- halo x = all hyperelements "infinitely close" to x (NonstandardAnalysis.lean:93)
def halo (x : α) [TopologicalSpace α] : Set (Hyper ι α) :=
  ⋂ U ∈ 𝓝 x, {y | liftPred (· ∈ U) y}

-- IsSt defined via halo membership
def IsSt (y : Hyper ι α) (x : α) : Prop := y ∈ halo x
-- Equivalently: IsNearStandard in Star.lean:1543
```

This works for **any topological space**:
- **ℝ, ℚ** - order topology, halo = infinitesimal neighborhood
- **ℂ** - product topology (automatically handles re/im components!)
- **Normed spaces** - halo = {y | ‖y - std x‖ infinitesimal}
- **Discrete types (ℕ, ℤ)** - discrete topology, halo x = {std x}

**Uniqueness** comes from T2 (Hausdorff) - already proved:
```lean
theorem halo_eq_of_mem_halo [T2Space α] {x y : α} {z : Hyper ι α}
    (hx : z ∈ halo x) (hy : z ∈ halo y) : x = y
```

**Standard part function**:
```lean
-- General: choice-based, requires proof of near-standardness
noncomputable def st (y : Hyper ι α) (h : IsNearStd y) : α := h.choose

-- For ordered complete types: supremum gives explicit construction (avoids choice)
noncomputable def st_ordered (x : Hyper ι α) : α := sSup {r : α | std r ≤ x}
```

**Key insight**:
- The **halo/monad definition is conceptually primary** (works for all topological spaces)
- The **supremum definition is a computational shortcut** for ordered types (avoids choice)
- For ℂ, ℝⁿ, etc., the topological definition automatically gives the right behavior

### Unification Strategy (Revised)

1. **Primary definition**: `IsSt y x := y ∈ halo x` (topological)
2. Keep `Hyper ι α` as universal framework in `Star.lean`
3. For ordered types, prove: `y ∈ halo x ↔ sSup {r | std r ≤ y} = x` (when y finite)
4. Define typeclasses that encode structure, not alternative definitions
5. `Hypercomplex` comes for free via product topology - no special case needed!

## Naming Refactor: IsSt → IsNearStandard

**Problem**: `IsSt` is a confusing name - it sounds like "is standard" but means "has standard part".

**Current state**:
| File | `IsSt` means | Occurrences |
|------|--------------|-------------|
| Hyperreal.lean | ε-δ closeness | 65 |
| Hypernatural.lean | equality `x = std r` | 27 |
| Hyperinteger.lean | equality `x = std r` | 10 |
| Star.lean | `IsNearStandard` (topological) | canonical |

**Target**: Use `IsNearStandard` everywhere (the topological definition from Star.lean).

**Why not just replace?**
- Hyperreal.lean is a `module` file, can't import non-module Star.lean
- 129 total occurrences across 4 files
- Many proofs use the ε-δ definition directly

**Refactor plan**:
1. Add equivalence theorem: `IsSt x r ↔ IsNearStandard x r` (for each type)
2. Deprecate `IsSt` with `@[deprecated]` pointing to `IsNearStandard`
3. Gradually migrate proofs
4. Eventually delete `IsSt` definitions

**Alternative**: Make Star.lean a `module` file, then Hyperreal can import it.

## TODO

- [ ] Audit aristotle files for useful lemmas
- [ ] Implement `NonstandardExtension` typeclass
- [ ] Make hyperstructures instances
- [ ] Unify standard part definitions
- [ ] Add `Hypercomplex` (`ℂ*`)
- [ ] Refactor `IsSt` → `IsNearStandard` (see above)
