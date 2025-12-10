/-
Copyright (c) 2024 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Mathlib.Order.Filter.Germ.Star
import Mathlib.Order.Filter.Germ.LoebMeasure
import Mathlib.Algebra.Group.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Hyperfinite Groups

This file defines hyperfinite groups and their associated measures.

## Definitions

* `IsHyperfiniteGroup`: A predicate on an internal set `H` stating it forms a group under the ambient operations.
* `normalizedCountingMeasure`: The internal counting measure normalized to Have total mass 1.
-/

namespace Hyper

open scoped NonstandardAnalysis
open MeasureTheory

variable {ι : Type*} [Infinite ι] {α : Type*} [Group α]

/-- A hyperfinite group is an internal subgroup of `*G` that is hyperfinite. -/
structure HyperfiniteGroup (ι : Type*) [Infinite ι] (α : Type*) [Group α] extends Subgroup (Hyper ι α) where
  isInternal : IsInternal carrier
  isHyperfinite : IsHyperfinite carrier

attribute [instance] HyperfiniteGroup.toSubgroup

/-- The normalized counting measure on a hyperfinite group. -/
noncomputable def normalizedCountingMeasure {ι : Type*} [Infinite ι] {α : Type*} [Group α]
    (H : HyperfiniteGroup ι α)
    (A : Set (Hyper ι α)) (hA : IsInternal A) : Hyper ι ℝ :=
  internalCountingMeasure H.carrier H.isHyperfinite A hA

theorem normalizedCountingMeasure_univ {ι : Type*} [Infinite ι] {α : Type*} [Group α]
    (H : HyperfiniteGroup ι α) :
    normalizedCountingMeasure H H.carrier H.isInternal = 1 := by
  dsimp [normalizedCountingMeasure, internalCountingMeasure]
  have h_eq : hyperfiniteSubsetCard H.carrier H.isHyperfinite H.carrier H.isInternal = hyperfiniteCard H.carrier H.isHyperfinite := by
    rw [hyperfiniteSubsetCard]
    simp
  rw [h_eq]
  let num := Hyper.lift (Nat.cast : ℕ → ℝ) (hyperfiniteCard H.carrier H.isHyperfinite)
  change num / num = 1
  -- We need H to be nonempty to avoid 0/0
  have h_ne : num ≠ 0 := by
    dsimp [num]
    intro h_eq
    rw [Filter.Germ.coe_eq] at h_eq
    have h_card : ∀ᶠ i in Filter.hyperfilter ι, 1 ≤ (H.isHyperfinite.choose_spec.1 i).toFinset.card := by
      -- Need to access the fact that 1 \in H
      have h1 : (1 : Hyper ι α) ∈ H.carrier := H.one_mem
      rw [H.isHyperfinite.choose_spec.2] at h1
      rw [Hyper.liftPredSeq_ofSeq] at h1
      filter_upwards [h1] with i hi
      rw [Finset.card_pos]
      exact ⟨1, hi⟩
    filter_upwards [h_eq, h_card] with i hi_eq hi_card
    dsimp at hi_eq
    rw [← Nat.cast_zero (R := ℝ)] at hi_eq
    have hi_eq' : ((H.isHyperfinite.choose_spec.1 i).toFinset.card : ℝ) = 0 := hi_eq
    rw [Nat.cast_eq_zero] at hi_eq'
    linarith
  apply div_self h_ne

/-- A structure representing a hyperfinite approximation of a standard group `G`. -/
structure HyperfiniteApproximation (ι : Type*) [Infinite ι] (G : Type*) [Group G] [TopologicalSpace G]
    extends HyperfiniteGroup ι G where
  approx_std : ∀ g : G, ∃ h ∈ carrier, IsNearStandard h g


end Hyper

section CircleApproximation

open Hyper MeasureTheory

variable {ι : Type*} [Infinite ι]

/-- The circle `S¹` (modeled as `AddCircle T`) has a hyperfinite approximation. -/
theorem exists_approximation_circle (T : ℝ) [hT : Fact (0 < T)] :
    ∃ H : HyperfiniteGroup ι (AddCircle T), HyperfiniteApproximation ι (AddCircle T) := by
  -- We construct the approximation using roots of unity of explicit infinite order.
  sorry

end CircleApproximation
