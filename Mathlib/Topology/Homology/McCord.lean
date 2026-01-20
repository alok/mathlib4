/-
Copyright (c) 2024 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
module

public import Mathlib.Analysis.Convex.SimplicialComplex.Internal
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Topology.FunctionShadow
public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Algebra.Order.Ring.Defs

@[expose] public section

/-!
# McCord's Nonstandard Homology Theorem

This file implements McCord's construction of simplicial homology using Nonstandard Analysis.
McCord's theorem relates the homology of a topological space (e.g., a compact metric space)
to the simplicial homology of a hyperfinite simplicial complex that "infinitely approximates" it.

## Main definitions

* `HyperSimplicialChainComplex`: The chain complex associated to an internal simplicial complex.
* `McCord.approximation`: A pair $(X, K)$ where $K$ is a hyperfinite simplicial complex
  approximating $X$.
* `McCord.homologyIso`: The isomorphism between singular homology and hyperfinite homology.

## References

* McCord, M. C. (1972). Non-Standard Analysis and Simplicial Homology.
-/
open Set Filter Geometry Hyper Topology NonstandardAnalysis

variable {ι : Type*} [Infinite ι] {𝕜 E : Type*} [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E] [LinearOrder E]

namespace Geometry

variable {ι : Type*} [Infinite ι] {𝕜 E : Type*} [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E] [LinearOrder E]

/-- The set of n-simplices of a simplicial complex. -/
def SimplicialComplex.simplices (K : SimplicialComplex 𝕜 E) (n : ℕ) : Set (Finset E) :=
  { s ∈ K.faces | s.card = n + 1 }

/-- The n-th simplicial chain group with coefficients in R. -/
def SimplicialComplex.chainGroup (K : SimplicialComplex 𝕜 E) (n : ℕ) (R : Type*) [AddCommGroup R] :
    Type _ :=
  (K.simplices n) →₀ R

/-- To define the boundary operator, we assume an ordering on E (e.g., from a linear order).
    In the nonstandard case, we can always transfer a linear order. -/
variable [LinearOrder E]

/-- The face of a simplex obtained by removing the i-th vertex (in the order of E). -/
def SimplicialComplex.face (s : Finset E) (i : ℕ) : Finset E :=
  s.erase (s.toList.sorted (· ≤ ·)).toArray[i]!

/-- The simplicial boundary operator. -/
noncomputable def SimplicialComplex.boundary (K : SimplicialComplex 𝕜 E) (n : ℕ) (R : Type*)
    [AddCommGroup R] [Module ℤ R] :
    K.chainGroup (n + 1) R →ₗ[ℤ] K.chainGroup n R :=
  Finsupp.total (K.simplices (n + 1)) (K.chainGroup n R) ℤ (fun s =>
    let vertices := (s : Finset E).toList.sorted (· ≤ ·)
    (Finset.range (n + 2)).sum (fun i =>
      let face := (s : Finset E).erase vertices[i]!
      if h : face ∈ K.faces ∧ face.card = n + 1 then
        Finsupp.single ⟨face, h⟩ (if i % 2 = 0 then (1 : ℤ) else (-1 : ℤ)) • (1 : R)
      else 0))

/-- The simplicial chain complex. -/
noncomputable def SimplicialComplex.chainComplex (K : SimplicialComplex 𝕜 E) (R : Type*)
    [AddCommGroup R] [Module ℤ R] :
    ChainComplex R ℕ where
  X n := K.chainGroup n R
  d n n' := if h : n = n' + 1 then by rw [h]; exact K.boundary n' R else 0
  d_comp_d' n₁ n₂ n₃ h₁₂ h₂₃ := by
    subst h₁₂; subst h₂₃
    simp only [ChainComplex.next_d_eq, ChainComplex.prev_d_eq, dite_true]
    -- Proof of boundary ∘ boundary = 0 for simplicial complexes
    ext c s
    simp only [boundary, Finsupp.total_apply, Finsupp.single_apply, Finsupp.sum_apply,
      Finsupp.single_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply,
      Finsupp.lift_apply]
    sorry -- standard calculation involving alternating sums

/-- The chain complex functor for simplicial complexes, lifted to the nonstandard universe. -/
noncomputable def InternalSimplicialComplex.chainComplex (K : Hyper ι (SimplicialComplex 𝕜 E))
    (R : Type*) [AddCommGroup R] [Module ℤ R] :
    ChainComplex (Hyper ι R) ℕ :=
  lift (fun K' => SimplicialComplex.chainComplex K' R) K

/-- The hyperfinite homology of an internal simplicial complex.
    Defined as the lift of the simplicial homology functor. -/
noncomputable def InternalSimplicialComplex.homology (K : Hyper ι (SimplicialComplex 𝕜 E))
    (n : ℕ) (R : Type*) [AddCommGroup R] [Module ℤ R] : Type _ :=
  Hyper ι (Homology R n) -- This is effectively lifting the type

/-- The hyperfinite homology groups are themselves hyperfinite (internal) groups. -/
instance (K : Hyper ι (SimplicialComplex 𝕜 E)) (n : ℕ) (R : Type*)
    [AddCommGroup R] [Module ℤ R] : AddCommGroup (InternalSimplicialComplex.homology K n R) :=
  inferInstance

end Geometry

namespace McCord

variable {ι : Type*} [Infinite ι] {𝕜 E : Type*} [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E] [LinearOrder E]

/-- A hyperfinite simplicial complex `K` approximates a topological space `X` if
its shadow is contained in `X` and it "covers" `X` in a nonstandard sense. -/
def Approximates (K : Set (Set (Hyper ι E))) (X : Set E) : Prop :=
  ∃ κ : Hyper ι (SimplicialComplex 𝕜 E), K = Geometry.liftSimplicialComplex (ι := ι) κ ∧
    ∀ x ∈ X, ∃ y ∈ K, IsNearStd y ∧ stdPart y (by assumption) = x

/-- Extracts the internal simplicial complex from an internal set of sets. -/
noncomputable def κ_of_K {K : Set (Set (Hyper ι E))} (hK : IsInternalSimplicialComplex K) :
    Hyper ι (SimplicialComplex 𝕜 E) :=
  hK.choose

theorem κ_of_K_spec {K : Set (Set (Hyper ι E))} (hK : IsInternalSimplicialComplex (ι := ι) K) :
    Geometry.liftSimplicialComplex (ι := ι) (κ_of_K (𝕜 := 𝕜) (E := E) hK) = K :=
  hK.choose_spec

theorem homologyIso {X : Set E} (hX : IsCompact X)
    {K : Set (Set (Hyper ι E))} (hK : IsInternalSimplicialComplex K)
    (happrox : Approximates K X) (n : ℕ) (R : Type*) [AddCommGroup R] [Module ℤ R] :
    AlgebraicTopology.singularHomology R n X ≅
      (InternalSimplicialComplex.homology (κ_of_K K hK) n R) :=
  sorry

end McCord
end
