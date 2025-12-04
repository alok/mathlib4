# NSA Pluggable Framework Plan

## Goal
Make nonstandard analysis "pluggable" so the rest of mathlib can easily use it.

## Key Insight
Mathlib already has `ModelTheory/Ultraproducts.lean` with **Łoś's Theorem**:
```lean
theorem sentence_realize (φ : L.Sentence) :
    (u : Filter α).Product M ⊨ φ ↔ ∀ᶠ a : α in u, M a ⊨ φ
```

Our `Hyper ι α = Germ (hyperfilter ι) α` is essentially `Filter.Product (fun _ => α) (hyperfilter ι)`.

## Phase 1: Connect Hyper to ModelTheory

### Tasks
1. **Show equivalence**: `Hyper ι α ≃ Filter.Product (fun _ : ι => α) (hyperfilter ι)`
2. **Lift structures**: For any `L.Structure α`, construct `L.Structure (Hyper ι α)`
3. **Transfer theorem**: `(Hyper ι α) ⊨ φ ↔ α ⊨ φ` for sentences (immediate from Łoś)

### Files to modify
- `Mathlib/Order/Filter/Germ/Star.lean` - add ModelTheory connection
- New file: `Mathlib/ModelTheory/Hyper.lean`

## Phase 2: transfer Tactic

### Design
```lean
-- User writes:
example (a b : ℝ) : std a + std b = std (a + b) := by transfer

-- Tactic recognizes this as first-order and applies Łoś
```

### Implementation approach
1. Define which Lean propositions are "first-order" (equations, inequalities, quantifiers over standard types)
2. Build `L.Sentence` from the goal
3. Apply `sentence_realize`
4. Simplify using `∀ᶠ ... in hyperfilter` = `True` for sentences about constants

### Challenge: Recognizing first-order formulas
- Equations: `t₁ = t₂` where terms involve `+`, `*`, `<`, etc.
- Quantifiers: `∀ x : α, P x` → `∀ x : Hyper ι α, liftPred P x`
- Need to handle: nested quantifiers, function symbols, relation symbols

## Phase 3: Star Functor (Categorical NSA)

Reference: https://www.mdpi.com/2073-8994/13/9/1573

### Functor structure
```lean
def Star (ι : Type*) [Infinite ι] : Type* → Type* := Hyper ι

-- Functorial action on morphisms
def Star.map {α β : Type*} (f : α → β) : Star ι α → Star ι β := Hyper.lift f

-- Natural transformation: standard embedding
def Star.std : ∀ α, α → Star ι α := @Hyper.std ι _
```

### Properties to prove
- `Star.map id = id`
- `Star.map (g ∘ f) = Star.map g ∘ Star.map f`
- `Star.map f ∘ std = std ∘ f` (naturality)

### Connection to existing categorical infrastructure
- `Mathlib/CategoryTheory/Functor/*`
- Show `Star` is a functor `Type* ⥤ Type*`

## Phase 4: Pluggability

### Option A: Type class approach
```lean
class NatLike (N : Type*) where
  zero : N
  succ : N → N
  -- axioms...

instance : NatLike ℕ := ...
instance : NatLike ℕ* := ...

def ZMod' {N : Type*} [NatLike N] (n : N) : Type* := ...
```

**Pros**: Clean API
**Cons**: Requires rewriting definitions, may not work for complex structures

### Option B: Internal language approach
Work within the internal language of `★(Set)`:
- `★(ℤ/pℤ)` for standard `p`
- Define operations internally

**Pros**: Closest to NSA literature
**Cons**: Requires significant infrastructure

### Option C: Metaprogramming
```lean
-- Generate starred versions automatically
derive_hyper ZMod
-- Creates: HZMod : ℕ* → Type*, with structure inherited from ZMod
```

**Pros**: Flexible, handles complex cases
**Cons**: Magic, hard to reason about

### Recommended: Hybrid approach
1. Use **transfer tactic** for automatic reasoning about existing types
2. Use **Option A** for new definitions where practical
3. Use **Option C** for legacy structures like ZMod

## Phase 5: Integration with Mathlib

### Key structures to "star"
- [ ] `ZMod n` → `★(ZMod n)` or `HZMod N`
- [ ] `Polynomial R` → `HPolynomial (Hyper ι R)`
- [ ] `Matrix n m R` → `HMatrix N M (Hyper ι R)`
- [ ] `MeasureTheory.Measure` → internal measures

### Tests
1. Prove `π` is transcendental using NSA (overflow)
2. Prove Bolzano-Weierstrass using hyperfinite approximation
3. Prove Arzelà-Ascoli using NSA

## Timeline
- Phase 1: 2 weeks (connect to ModelTheory)
- Phase 2: 4 weeks (transfer tactic)
- Phase 3: 2 weeks (categorical structure)
- Phase 4: Ongoing (add structures as needed)
- Phase 5: Ongoing (integration)

## References
1. Mathlib ModelTheory: `Mathlib/ModelTheory/*`
2. Categorical NSA: https://www.mdpi.com/2073-8994/13/9/1573
3. Eightfold Path: Benci, Di Nasso, Forti
4. MathOverflow: https://mathoverflow.net/questions/226169
