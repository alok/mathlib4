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

variable {ι : Type*} [Infinite ι] {α : Type*} [AddGroup α]

/-- A hyperfinite group is an internal subgroup of `*G` that is hyperfinite. -/
structure HyperfiniteGroup (ι : Type*) [Infinite ι] (α : Type*) [AddGroup α] extends AddSubgroup (Hyper ι α) where
  isInternal : IsInternal carrier
  isHyperfinite : IsHyperfinite carrier

attribute [instance] HyperfiniteGroup.toAddSubgroup

/-- The normalized counting measure on a hyperfinite group. -/
noncomputable def normalizedCountingMeasure {ι : Type*} [Infinite ι] {α : Type*} [AddGroup α]
    (H : HyperfiniteGroup ι α)
    (A : Set (Hyper ι α)) (hA : IsInternal A) : Hyper ι ℝ :=
  internalCountingMeasure H.carrier H.isHyperfinite A hA

theorem normalizedCountingMeasure_univ {ι : Type*} [Infinite ι] {α : Type*} [AddGroup α]
    (H : HyperfiniteGroup ι α) :
    normalizedCountingMeasure H H.carrier H.isInternal = 1 := by
  dsimp [normalizedCountingMeasure, internalCountingMeasure, hyperfiniteSubsetCard]
  have h_eq : hyperfiniteCard (H.carrier ∩ H.carrier) (IsInternal.inter_isHyperfinite H.isInternal H.isHyperfinite) =
      hyperfiniteCard H.carrier H.isHyperfinite := by
    apply hyperfiniteCard_congr
    simp
  rw [h_eq]
  have h_ne : 0 < hyperfiniteCard H.carrier H.isHyperfinite := by
    rw [hyperfiniteCard_pos_iff_nonempty]
    exact ⟨0, H.zero_mem⟩
  revert h_ne
  induction (hyperfiniteCard H.carrier H.isHyperfinite) using Filter.Germ.inductionOn with | h f =>
  intro h_ne
  simp only [Hyper.lift, Filter.Germ.map_coe]
  apply Filter.Germ.coe_eq.mpr
  rw [Hyper.lt_def] at h_ne
  filter_upwards [h_ne] with i hi
  exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hi))

/-- A structure representing a hyperfinite approximation of a standard group `G`. -/
structure HyperfiniteApproximation {ι : Type*} [Infinite ι] (G : Type*) [AddGroup G] [TopologicalSpace G]
    extends HyperfiniteGroup ι G where
  approx_std : ∀ g : G, ∃ h ∈ carrier, IsNearStandard h g

end Hyper

section CircleApproximation

open Hyper MeasureTheory

variable {ι : Type*} [Infinite ι]

/-- The circle `S¹` (modeled as `AddCircle T`) has a hyperfinite approximation. -/
theorem exists_approximation_circle (T : ℝ) [hT : Fact (0 < T)] :
  obtain ⟨N, hN_inf⟩ : ∃ N : Hyper ι ℕ, N.IsInfinite := exists_Infinite_nat
  induction N using Filter.Germ.inductionOn with | h f =>
  let H_seq : ι → AddSubgroup (AddCircle T) := fun i =>
    AddSubgroup.zmultiples (QuotientAddGroup.mk (T / (f i + 1) : ℝ))
  let H_carrier := liftSetSeq (fun i => (H_seq i : Set (AddCircle T)))
  let H : HyperfiniteGroup ι (AddCircle T) := {
    carrier := H_carrier
    isInternal := ⟨fun i => (H_seq i : Set (AddCircle T)), rfl⟩
    isHyperfinite := ⟨fun i => (H_seq i : Set (AddCircle T)), ⟨fun i => (H_seq i).toSet.toFinite, rfl⟩⟩
    zero_mem' := by
      rw [liftSetSeq_def, liftPredSeq_ofSeq]
      filter_upwards with i; exact (H_seq i).zero_mem
    add_mem' := by
      intro x y hx hy
      induction x using Filter.Germ.inductionOn with | _ gx =>
      induction y using Filter.Germ.inductionOn with | _ gy =>
      rw [liftSetSeq_def, liftPredSeq_ofSeq] at hx hy ⊢
      filter_upwards [hx, hy] with i hxi hyi
      exact (H_seq i).add_mem hxi hyi
    neg_mem' := by
      intro x hx
      induction x using Filter.Germ.inductionOn with | _ gx =>
      rw [liftSetSeq_def, liftPredSeq_ofSeq] at hx ⊢
      filter_upwards [hx] with i hxi
      exact (H_seq i).neg_mem hxi
  }
  use { H with approx_std := by
    intro g
    -- Distance between elements in H_i is T/(f i + 1).
    -- Since f i -> infinity, this distance goes to 0.
    -- Thus we can always find an element h_i in H_i close to g.
    -- Formally, this needs floor(...) but we can just use the property of subgroups.
    sorry }

end CircleApproximation
