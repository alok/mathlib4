# Nonstandard Analysis in Lean 4

This directory contains a clean implementation of Nonstandard Analysis (NSA) in Lean 4, where the ultrafilter construction is completely hidden from users.

## Overview

NSA allows us to work with:
- **Infinitesimals**: Numbers smaller than any positive real
- **Infinite numbers**: Numbers larger than any real  
- **Hyperfinite sets**: "Finite" sets that can have infinitely many elements
- **Transfer principle**: First-order properties transfer between standard and nonstandard worlds

## Key Files

### Core Framework
- `NSA.lean` - High-level interface hiding ultrafilters
- `NSACore.lean` - Implementation details (users shouldn't need this)
- `Tactics.lean` - Custom tactics for natural NSA proofs

### Applications
- `HyperfiniteInductionClean.lean` - Induction up to infinite bounds
- `CompactnessNSA.lean` - Robinson's characterization of compactness
- `CalculusNSA.lean` - Derivatives and integrals via infinitesimals
- `ClassicalTheorems.lean` - Classical theorems with NSA proofs
- `Examples.lean` - Beautiful examples showcasing NSA

### Original Development
- `HyperfiniteInduction.lean` - Original file with ultrafilter details
- `TransferBasic.lean`, `Transfer.lean` - Transfer tactic development

## Key Concepts

### Types
- `ℕ*` - Hypernatural numbers (includes ω)
- `ℝ*` - Hyperreal numbers (includes infinitesimals)

### Predicates
- `Standard x` - x is the image of a standard object
- `Infinite x` - x is larger than all standard values
- `x ≈ y` - x and y are infinitely close
- `Internal P` - P is a valid predicate in the nonstandard world

### Notation
- `*n` - The standard natural n viewed as a hypernatural
- `*r` - The standard real r viewed as a hyperreal  
- `ω` - The canonical infinite hypernatural
- `ε` - A positive infinitesimal (1/ω)
- `st(x)` - Standard part of finite hyperreal x

## Example Usage

```lean
import Mathlib.Tactic.Nonstandard.NSA

open NSA

-- Continuity via infinitesimals
theorem continuous_iff_preserves_nearness {f : ℝ → ℝ} {a : ℝ} :
    ContinuousAt f a ↔ ∀ x : ℝ*, x ≈ *a → *f(st x) ≈ *f(a)

-- Compactness via NSA  
theorem compact_iff_nsa {K : Set ℝ} :
    IsCompact K ↔ ∀ x ∈ *K, x.IsFinite → st(x) ∈ K

-- Derivative as infinitesimal quotient
def derivative (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  st(((*f)(*x + ε) - (*f)(*x)) / ε)

-- Hyperfinite induction works up to ω!
example : ∀ n ≤ ω, n < n + 1 := by
  intro n hn
  hyperfinite_induction ω
  · norm_num  -- base case
  · intro k _ _
    norm_num  -- inductive step
```

## Philosophy

This implementation follows Robinson's vision: infinitesimals should feel natural, not like a technical construction. The ultrapower machinery is completely hidden - users just work with infinitely small and infinitely large numbers as Leibniz intended.

## Status

- ✅ Core framework complete
- ✅ Basic theorems demonstrated
- ✅ Compactness fully developed  
- ✅ Calculus via infinitesimals shown
- 🚧 Many proofs still have `sorry`
- 🚧 Tactics need implementation
- 🚧 More examples needed

## Future Work

1. Complete the `sorry` proofs
2. Implement the tactics properly
3. Add more applications (probability, combinatorics, etc.)
4. Connect to existing Mathlib theorems
5. Develop internal set theory aspects