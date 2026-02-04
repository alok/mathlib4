/-
Copyright (c) 2024 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Mathlib.Order.Filter.Germ.Product
import Mathlib.Order.Filter.Ultrafilter.Nonstandard
import Mathlib.ModelTheory.Ultraproducts

/-!
# Connecting Germ to Model-Theoretic Ultraproducts

This file establishes the connection between `Filter.Germ` (used for hyperstructures)
and the model-theoretic `Filter.Product` construction that supports Łoś's theorem.

## Main results

* `Filter.Germ.sentence_realize_const`: Łoś's theorem for constant families - a sentence
  holds in the ultraproduct iff it holds in the base structure.

## The Bridge

The key insight is that `Germ l β` and `Product l (fun _ => β)` are both quotients
of `α → β` by the same equivalence relation (eventually equal in `l`). The
equivalence `prodEquiv` makes them isomorphic as types.

For model theory, when `[L.Structure β]`, the ultraproduct construction gives
`L.Structure (Product l (fun _ => β))`. For a constant family where all structures
are identical, Łoś's theorem simplifies: a sentence holds in the ultraproduct
iff it holds in the base structure.

This connects our concrete hypernatural/hyperrational constructions to the
full power of model theory.
-/

namespace Filter

namespace Germ

open FirstOrder Language Ultraproduct Ultrafilter

variable {α : Type*} {β : Type*}

/-! ## Łoś's Theorem for Constant Families

For a constant family `M a = β` for all `a`, Łoś's theorem simplifies:
a sentence holds in the ultraproduct iff it holds in the base structure.
-/

section LosTheorem

variable {L : Language} [L.Structure β] [Nonempty β]

/-- **Łoś's Theorem for Constant Families**: For a constant family where every structure
is `β`, a sentence `φ` holds in the ultraproduct iff it holds in `β`.

This is because `∀ᶠ a in u, β ⊨ φ` simplifies to `β ⊨ φ` (the truth value is constant). -/
theorem sentence_realize_const (u : Ultrafilter α) (φ : L.Sentence) :
    (u : Filter α).Product (fun _ : α => β) ⊨ φ ↔ β ⊨ φ := by
  rw [Ultraproduct.sentence_realize]
  constructor
  · intro h
    -- `∀ᶠ a in u, β ⊨ φ` means the set `{a | β ⊨ φ}` is in u
    -- Since the condition is constant, this set is either ∅ or univ
    by_contra hne
    have hempty : {a : α | β ⊨ φ} = ∅ := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact hne
    simp only [hempty, Filter.eventually_iff] at h
    exact Ultrafilter.empty_notMem h
  · intro h
    apply Filter.Eventually.of_forall
    intro _
    exact h

end LosTheorem

/-! ## Applications to Hypernaturals

When specialized to `nonstandardUltrafilter ℕ` and ordered structures, this gives the
transfer principle for first-order order properties.
-/

section Hypernatural

variable [Infinite α] {L : Language} [L.Structure β] [Nonempty β]

/-- The nonstandardUltrafilter ultraproduct of a constant family satisfies the same sentences
as the base structure. -/
theorem hyperproduct_sentence_realize (φ : L.Sentence) :
    (nonstandardUltrafilter α : Filter α).Product (fun _ : α => β) ⊨ φ ↔ β ⊨ φ :=
  sentence_realize_const (nonstandardUltrafilter α) φ

end Hypernatural

end Germ

end Filter
