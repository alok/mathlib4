/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
module

public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.Order.Filter.Curry

/-!
# Curried ultrafilters

This file packages the Fubini-style ultrafilter obtained from two ultrafilters via
`Filter.curry`.
-/

@[expose] public section

namespace Ultrafilter

open Filter

variable {ι κ : Type*} (U : Ultrafilter ι) (V : Ultrafilter κ)

lemma curry_compl_notMem_iff_mem (s : Set (ι × κ)) :
    sᶜ ∉ (Filter.curry (U : Filter ι) (V : Filter κ)) ↔
      s ∈ (Filter.curry (U : Filter ι) (V : Filter κ)) := by
  have hmem_compl :
      sᶜ ∈ (Filter.curry (U : Filter ι) (V : Filter κ)) ↔
        ∀ᶠ i in (U : Filter ι), ∀ᶠ j in (V : Filter κ), (i, j) ∈ sᶜ := by
    simp [Filter.mem_curry_iff]
  have hmem :
      s ∈ (Filter.curry (U : Filter ι) (V : Filter κ)) ↔
        ∀ᶠ i in (U : Filter ι), ∀ᶠ j in (V : Filter κ), (i, j) ∈ s := by
    simp [Filter.mem_curry_iff]
  have hflip :
      (∀ᶠ i in (U : Filter ι), ∀ᶠ j in (V : Filter κ), (i, j) ∈ sᶜ) ↔
        (∀ᶠ i in (U : Filter ι), ¬∀ᶠ j in (V : Filter κ), (i, j) ∈ s) := by
    refine Filter.eventually_congr ?_
    refine Filter.Eventually.of_forall ?_
    intro i
    exact (Ultrafilter.eventually_not (f := V) (p := fun j => (i, j) ∈ s))
  have houter :
      (∀ᶠ i in (U : Filter ι), ¬∀ᶠ j in (V : Filter κ), (i, j) ∈ s) ↔
        ¬∀ᶠ i in (U : Filter ι), ∀ᶠ j in (V : Filter κ), (i, j) ∈ s := by
    exact (Ultrafilter.eventually_not (f := U)
      (p := fun i => ∀ᶠ j in (V : Filter κ), (i, j) ∈ s))
  have hmem' :
      sᶜ ∈ (Filter.curry (U : Filter ι) (V : Filter κ)) ↔
        s ∉ (Filter.curry (U : Filter ι) (V : Filter κ)) :=
    hmem_compl.trans (hflip.trans (houter.trans (not_congr hmem).symm))
  constructor
  · intro hsc
    by_contra hs
    exact hsc (hmem'.2 hs)
  · intro hs hsc
    exact (hmem'.1 hsc) hs

/-- The Fubini (curried) product of two ultrafilters. -/
def curry (U : Ultrafilter ι) (V : Ultrafilter κ) : Ultrafilter (ι × κ) :=
  Ultrafilter.ofComplNotMemIff ((U : Filter ι).curry (V : Filter κ))
    (curry_compl_notMem_iff_mem (U := U) (V := V))

@[simp] theorem coe_curry (U : Ultrafilter ι) (V : Ultrafilter κ) :
    (U.curry V : Filter (ι × κ)) = (U : Filter ι).curry (V : Filter κ) :=
  rfl

end Ultrafilter
