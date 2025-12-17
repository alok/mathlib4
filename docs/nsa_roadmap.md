# Nonstandard Analysis Roadmap

## Current State

The `Mathlib/Order/Filter/Germ/Star.lean` file provides:
- `Hyper ι α = Germ (hyperfilter ι) α` - nonstandard extensions via ultraproducts
- `std : α → Hyper ι α` - standard embedding
- `IsInfinitesimal`, `IsFinite`, `IsUnlimited` predicates
- `IsNearStandard`, `st` (standard part) for ordered fields
- `IsInternal` for internal sets
- NSA characterizations of continuity, Cauchy sequences, limits, compactness
- Grind integration via contravariant instances

## Phase 1: Overspill and Underspill

### Mathematical Background

**Overspill Principle**: If an internal property P holds for all standard natural numbers,
then P holds for some unlimited natural number.

Formally: Let P be internal. If `∀ n : ℕ, P(std n)` then `∃ N : Hyper ι ℕ, IsUnlimited N ∧ P(N)`.

**Underspill Principle**: If an internal property P holds for all unlimited natural numbers,
then P holds for some standard natural number.

Formally: Let P be internal. If `∀ N : Hyper ι ℕ, IsUnlimited N → P(N)` then `∃ n : ℕ, P(std n)`.

### Implementation Plan

```lean
-- Key insight: internal sets are characterized by ultrafilter membership
-- If P holds for all std n, then for each n, {i | P_i(n)} ∈ U
-- The intersection over finitely many n is still in U
-- So there exists unlimited N where P holds

theorem overspill {P : Hyper ι ℕ → Prop} (hP : IsInternal {n | P n})
    (hstd : ∀ n : ℕ, P (std n)) : ∃ N : Hyper ι ℕ, IsUnlimited N ∧ P N := by
  -- P internal means P = liftPred Q for some Q : ι → ℕ → Prop
  -- hstd means ∀ n : ℕ, ∀ᶠ i in U, Q i n
  -- Need to find N = ofSeq f where f(i) → ∞ and Q i (f i) holds
  -- Use diagonal argument: f(i) = max {n ≤ i | Q i n}
  sorry

theorem underspill {P : Hyper ι ℕ → Prop} (hP : IsInternal {n | P n})
    (hunlim : ∀ N : Hyper ι ℕ, IsUnlimited N → P N) : ∃ n : ℕ, P (std n) := by
  -- Contrapositive of overspill on ¬P
  sorry
```

### Variants Needed

1. **Overspill for predicates with parameters**: `overspill_param`
2. **Overspill for inequalities**: If `∀ n : ℕ, x < std n` then `x < N` for some unlimited N
3. **Bounded overspill**: P holds for std n with n ≤ k implies P holds for some n > k
4. **Real-valued overspill**: For functions ℕ → ℝ

## Phase 2: Transfer Principle

### Mathematical Background

The transfer principle states that first-order sentences are true in the standard model
iff they are true in the nonstandard model. This is the foundational theorem of NSA.

For us: A first-order property P holds for standard objects iff P* holds for all objects.

### Implementation Strategy

Full transfer requires model theory. We implement **specific transfer schemas**:

```lean
-- Transfer for universal statements over finite types
theorem transfer_forall_fin {P : Fin n → Prop} :
    (∀ i, P i) ↔ (∀ i : Hyper ι (Fin n), liftPred P i) := by
  sorry

-- Transfer for arithmetic
theorem transfer_add (a b : α) [Add α] : std (a + b) = std a + std b := std_add a b
theorem transfer_mul (a b : α) [Mul α] : std (a * b) = std a * std b := std_mul a b
theorem transfer_le (a b : α) [LE α] : a ≤ b ↔ std a ≤ std b := std_le_std

-- Transfer for functions
theorem transfer_fun {f : α → β} (a : α) : std (f a) = lift f (std a) := by
  simp [lift_std]

-- Transfer for predicates (internal version)
theorem transfer_pred {P : α → Prop} (a : α) : P a ↔ liftPred P (std a) := by
  simp [liftPred_std]
```

### Transfer Tactic

```lean
/-- The `transfer` tactic attempts to convert a goal about standard objects
    to an equivalent goal about nonstandard objects, or vice versa. -/
macro "transfer" : tactic => `(tactic|
  simp only [← std_add, ← std_mul, ← std_neg, ← std_le_std, ← std_lt_std,
             lift_std, liftPred_std, liftRel_std])
```

## Phase 3: Standard Forward Image

### Mathematical Background

Standard functions preserve standardness. If `f : α → β` is a "standard" function
(i.e., defined without reference to nonstandard objects) and `a` is standard,
then `f(a)` is standard.

More precisely: `st (lift f x) = f (st x)` when x is near-standard and f is continuous.

### Implementation

```lean
/-- A function is "standard" if it commutes with the standard embedding. -/
def IsStdFun (f : α → β) : Prop := ∀ a, lift f (std a) = std (f a)

-- All "ordinary" functions are standard
theorem isStdFun_id : IsStdFun (id : α → α) := fun a => lift_std id a

theorem isStdFun_const (b : β) : IsStdFun (fun _ : α => b) := fun a => by
  simp [lift, std]

theorem isStdFun_comp {f : β → γ} {g : α → β} (hf : IsStdFun f) (hg : IsStdFun g) :
    IsStdFun (f ∘ g) := fun a => by
  simp [lift_comp, hf, hg]

-- For near-standard elements, st commutes with continuous standard functions
theorem st_lift_of_continuous {f : ℝ → ℝ} (hf : Continuous f) (x : Hyper ℕ ℝ)
    (hx : IsFinite x) : st (lift f x) = f (st x) := by
  -- Use continuity: x ≈ st x implies f(x) ≈ f(st x)
  sorry

-- General principle: std-ness preserved under forward image
theorem IsNearStandard.map {f : α → β} [TopologicalSpace α] [TopologicalSpace β]
    {x : Hyper ι α} {a : α} (hx : IsNearStandard x a) (hf : Continuous f) :
    IsNearStandard (lift f x) (f a) := by
  sorry
```

### Key Theorems

1. `st_add`: `st (x + y) = st x + st y` for finite x, y
2. `st_mul`: `st (x * y) = st x * st y` for finite x, y
3. `st_neg`: `st (-x) = -(st x)`
4. `st_inv`: `st (x⁻¹) = (st x)⁻¹` when st x ≠ 0
5. General: `st (lift f x) = f (st x)` for continuous f and finite x

## Phase 4: Loeb Measure

### Mathematical Background

The Loeb measure construction:
1. Start with a hyperfinite set Ω with internal counting measure μ
2. μ(A) = |A|/|Ω| for internal A ⊆ Ω (hyperreal-valued)
3. Define L(A) = st(μ(A)) for internal A (real-valued)
4. Extend L to the Loeb σ-algebra via Carathéodory

This gives a genuine probability measure from a "finite" (but hyperfinite) construction.

### Prerequisites

1. **Hyperfinite sets**: Sets with hyperfinite cardinality
   ```lean
   def IsHyperfinite (S : Set (Hyper ι α)) : Prop :=
     ∃ n : Hyper ι ℕ, ∃ f : Fin n → S, Function.Bijective f
   ```

2. **Internal counting measure**:
   ```lean
   def internalCount (S : Set (Hyper ι α)) (A : Set (Hyper ι α))
       (hS : IsHyperfinite S) (hA : IsInternal A) : Hyper ι ℝ :=
     card (A ∩ S) / card S
   ```

3. **Loeb outer measure**:
   ```lean
   def loebOuterMeasure (S : Set (Hyper ι α)) (hS : IsHyperfinite S) :
       MeasureTheory.OuterMeasure α :=
     { measureOf := fun A => ⨅ (B : Set (Hyper ι α)) (hB : IsInternal B)
                              (hAB : star A ⊆ B), st (internalCount S B hS hB)
       ... }
   ```

### Implementation Phases

**4a. Hyperfinite Combinatorics**
- Hyperfinite sets and their cardinalities
- Internal functions on hyperfinite sets
- Hyperfinite sums and products

**4b. Internal Measure**
- Internal finitely additive measures
- Properties: monotonicity, finite additivity

**4c. Loeb Construction**
- Standard part of internal measures
- Carathéodory extension
- σ-additivity proof (key difficulty!)

**4d. Applications**
- Hyperfinite random walks → Brownian motion
- Hyperfinite approximations to continuous distributions
- Anderson's construction of Brownian motion

## Dependencies

```
Phase 1 (Overspill/Underspill)
    ↓
Phase 2 (Transfer) ←── uses overspill for some proofs
    ↓
Phase 3 (Std Forward Image) ←── uses transfer
    ↓
Phase 4 (Loeb Measure) ←── uses all of the above
```

## File Organization

```
Mathlib/Order/Filter/Germ/
├── Star.lean          -- Core definitions (current)
├── Overspill.lean     -- Overspill/underspill lemmas
├── Transfer.lean      -- Transfer principle and tactic
└── StandardPart.lean  -- Standard part theory

Mathlib/MeasureTheory/
└── Loeb.lean          -- Loeb measure construction
```

## Success Metrics

1. **Overspill**: Prove 3+ applications (real limits, continuity, compactness)
2. **Transfer**: Working `transfer` tactic for basic arithmetic
3. **Std Image**: `st (lift f x) = f (st x)` for continuous f
4. **Loeb**: Construct Loeb measure, prove σ-additivity, one application
