/-
Copyright (c) 2025 Alok Beniwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Beniwal
-/
import Mathlib.Topology.MetricSpace.GromovHyperbolic

/-!
# Equivalence of Different Formulations

This file proves that different formulations of Gromov hyperbolicity are equivalent.
We show that the formulations in this file match the pasted alternative version.

## Main results

* `gromovProd_eq_GromovProduct`: The Gromov products are identical
* `fourPoint_iff_FourPointCondition`: The four-point conditions are equivalent
* `gromovProdProperty_iff_GromovProductProperty`: The properties are equivalent

-/

noncomputable section

variable {X : Type*} [MetricSpace X]

namespace Pasted

-- Alternative formulation (from the pasted proof)
/-- Gromov product with basepoint as third argument. -/
def gromovProd (x y z : X) : ℝ :=
  (dist z x + dist z y - dist x y) / 2

/-- Four-point condition with constant `δ` (alternative formulation). -/
def FourPoint (δ : ℝ) : Prop :=
  ∀ x y z w : X,
    dist x z + dist y w ≤
      max (dist x y + dist z w) (dist x w + dist y z) + 2 * δ

/-- Gromov-product formulation of δ-hyperbolicity (alternative). -/
def GromovProdProperty (δ : ℝ) : Prop :=
  ∀ x y z w : X,
    gromovProd x z w ≥
      min (gromovProd x y w) (gromovProd y z w) - δ

end Pasted

-- Equivalence proofs

/-- The two Gromov product definitions are identical. -/
theorem gromovProd_eq_GromovProduct (x y w : X) :
    Pasted.gromovProd x y w = GromovProduct x y w := by
  simp only [Pasted.gromovProd, GromovProduct, dist_comm w]

/-- The four-point conditions are equivalent by permuting arguments.
    FourPoint applied to (x,y,z,w) gives the same condition as FourPointCondition
    applied to a permutation. -/
theorem fourPoint_iff_FourPointCondition {δ : ℝ} :
    Pasted.FourPoint (X := X) δ ↔ FourPointCondition (X := X) δ := by
  constructor
  · intro h x y z w
    -- FourPoint says: ∀ a b c d, dist a c + dist b d ≤ max(...) + 2δ
    -- Apply it to (x, z, y, w): dist x y + dist z w ≤ max (dist x z + dist y w) (dist x w + dist z y) + 2δ
    have := h x z y w
    simp only [dist_comm z y] at this
    exact this
  · intro h x y z w
    -- FourPointCondition says: ∀ a b c d, dist a b + dist c d ≤ max(...) + 2δ
    -- Apply it to (x, z, y, w): dist x z + dist y w ≤ max (dist x y + dist z w) (dist x w + dist y z) + 2δ
    calc dist x z + dist y w
        ≤ max (dist x y + dist z w) (dist x w + dist z y) + 2 * δ := h x z y w
      _ = max (dist x y + dist z w) (dist x w + dist y z) + 2 * δ := by rw [dist_comm z y]

/-- The Gromov product properties are equivalent by relabeling variables. -/
theorem gromovProdProperty_iff_GromovProductProperty {δ : ℝ} :
    Pasted.GromovProdProperty (X := X) δ ↔ GromovProductProperty (X := X) δ := by
  simp only [Pasted.GromovProdProperty, GromovProductProperty, gromovProd_eq_GromovProduct]
  constructor
  · intro h x y z w
    -- h gives: ∀ a b c d, (a,c|d) ≥ min((a,b|d), (b,c|d)) - δ
    -- We need: (x,y|w) ≥ min((x,z|w), (z,y|w)) - δ
    -- Apply h to (x, z, y, w): (x,y|w) ≥ min((x,z|w), (z,y|w)) - δ
    exact h x z y w
  · intro h x y z w
    -- h gives: ∀ a b c d, (a,b|d) ≥ min((a,c|d), (c,b|d)) - δ
    -- We need: (x,z|w) ≥ min((x,y|w), (y,z|w)) - δ
    -- Apply h to (x, z, y, w): (x,z|w) ≥ min((x,y|w), (y,z|w)) - δ
    exact h x z y w

/-- The pasted version implies the original version. -/
theorem pasted_implies_original {δ : ℝ}
    (h : Pasted.FourPoint (X := X) δ → Pasted.GromovProdProperty (X := X) δ) :
    FourPointCondition (X := X) δ → GromovProductProperty (X := X) δ := by
  intro h_four
  rw [← gromovProdProperty_iff_GromovProductProperty]
  apply h
  rwa [← fourPoint_iff_FourPointCondition] at h_four

/-- The original version implies the pasted version (for δ ≥ 0). -/
theorem original_implies_pasted {δ : ℝ}
    (h : FourPointCondition (X := X) δ → GromovProductProperty (X := X) δ) :
    Pasted.FourPoint (X := X) δ → Pasted.GromovProdProperty (X := X) δ := by
  intro h_four
  rw [gromovProdProperty_iff_GromovProductProperty]
  apply h
  rwa [fourPoint_iff_FourPointCondition] at h_four
