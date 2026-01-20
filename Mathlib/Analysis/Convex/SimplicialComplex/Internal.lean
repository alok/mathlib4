/-
Copyright (c) 2024 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
module

public import Mathlib.Order.Filter.Germ.Star
public import Mathlib.Analysis.Convex.SimplicialComplex.Basic

/-!
# Internal Simplicial Complexes

This file defines internal simplicial complexes using Nonstandard Analysis.
An internal simplicial complex is the nonstandard extension of a sequence of simplicial complexes.

## Main definitions

* `liftFinset`: Lifts a hyperfinite set (element of `Hyper ι (Finset α)`) to a set in `Hyper ι α`.
* `liftSimplicialComplex`: Lifts a sequence of simplicial complexes to a collection of internal
  sets.
* `IsInternalSimplicialComplex`: Predicate for internal simplicial complexes.

-/

open Set Filter Geometry

@[expose] public section

variable {ι : Type*} {α : Type*} [Infinite ι]

namespace Hyper

/-- Lifts a hyperfinite set (an element of `Hyper ι (Finset α)`) to a subset of `Hyper ι α`. -/
def liftFinset (s : Hyper ι (Finset α)) : Set (Hyper ι α) :=
  {x | liftRel (· ∈ ·) x s}

@[simp]
theorem mem_liftFinset (s : Hyper ι (Finset α)) (x : Hyper ι α) :
    x ∈ liftFinset s ↔ liftRel (· ∈ ·) x s := Iff.rfl

theorem liftFinset_ofSeq (u : ι → Finset α) :
    liftFinset (ofSeq u) = liftSet (fun i => u i) := by
  ext x
  induction x using Germ.inductionOn with | h f =>
  simp only [mem_liftFinset]
  erw [mem_liftSet, liftRel_ofSeq]
  exact Iff.rfl

/-- A set in `Hyper ι α` is hyperfinite if it is the lift of a hyperfinite set. -/
theorem isHyperfinite_iff_exists_liftFinset {A : Set (Hyper ι α)} :
    IsHyperfinite A ↔ ∃ s : Hyper ι (Finset α), A = liftFinset s := by
  constructor
  · rintro ⟨u, hfin, h_eq⟩
    use ofSeq (fun i => (hfin i).toFinset)
    rw [liftFinset_ofSeq]
    ext x
    induction x using Germ.inductionOn with | h f =>
    rw [h_eq, mem_liftSet]
    erw [liftPredSeq_ofSeq, liftPredSeq_ofSeq]
    apply eventually_congr
    filter_upwards with i
    rw [Finite.coe_toFinset]
  · rintro ⟨s, rfl⟩
    obtain ⟨u, rfl⟩ := ofSeq_surjective s
    use fun i => u i
    constructor
    · intro i; exact (u i).finite_toSet
    · intro x
      rw [liftFinset_ofSeq, mem_liftSet]

end Hyper

open Hyper

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]

namespace Geometry

/-- Lifts a sequence of simplicial complexes to a collection of internal sets (faces). -/
def liftSimplicialComplex (K : ι → SimplicialComplex 𝕜 E) : Set (Set (Hyper ι E)) :=
  {F | ∃ S ∈ liftSet (fun i => (K i).faces), F = liftFinset S}

/-- A collection of sets is an internal simplicial complex if it is the lift of a sequence of
simplicial complexes. -/
def IsInternalSimplicialComplex (K : Set (Set (Hyper ι E))) : Prop :=
  ∃ u : ι → SimplicialComplex 𝕜 E, K = liftSimplicialComplex u

theorem IsInternalSimplicialComplex_std {ι : Type*} [Infinite ι] (K : SimplicialComplex 𝕜 E)
    (hK : K.faces.Finite) :
    IsInternalSimplicialComplex (𝕜 := 𝕜) (ι := ι) {liftFinset (std s) | s ∈ K.faces} := by
  use fun _ => K
  simp only [liftSimplicialComplex]
  ext F
  constructor
  · rintro ⟨s, hs, rfl⟩
    use Hyper.std (ι := ι) s
    constructor
    · rw [Hyper.std]
      erw [mem_liftSet]
      filter_upwards with i
      exact hs
    · rfl
  · rintro ⟨S, hS, rfl⟩
    induction S using Germ.inductionOn with | h f =>
    have : ∃ s ∈ K.faces, ofSeq f = std s := by
      erw [mem_liftSet] at hS
      let U := Ultrafilter.map f (hyperfilter ι)
      have h_mem : K.faces ∈ U := hS
      have h_fin : K.faces.Finite := hK
      obtain ⟨s, hs, h_eq⟩ := Ultrafilter.eq_pure_of_finite_mem h_fin h_mem
      use s, hs
      change ofSeq f = ofSeq (fun _ => s)
      rw [ofSeq_eq_ofSeq]
      change f ⁻¹' {s} ∈ hyperfilter ι
      rw [← Ultrafilter.mem_map]
      change {s} ∈ U
      rw [h_eq]
      rw [Ultrafilter.mem_pure]
      exact Set.mem_singleton s
    obtain ⟨s, hs, h_eq⟩ := this
    use s, hs
    change liftFinset (std s) = liftFinset (ofSeq f)
    rw [h_eq]

end Geometry

end
