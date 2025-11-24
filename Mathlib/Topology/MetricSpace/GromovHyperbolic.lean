/-
Copyright (c) 2025 Alok Beniwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Beniwal
-/
import Mathlib.Topology.MetricSpace.Basic

/-!
# Gromov Hyperbolic Spaces

This file defines Gromov hyperbolic metric spaces and proves basic properties.

## Main definitions

* `GromovProduct`: The Gromov product `(x|y)_w` measuring how far x and y fellow-travel when
  viewed from base point w
* `FourPointCondition`: A metric space satisfies the 4-point condition with constant δ if
  the sum of opposite sides of any quadrilateral is bounded
* `GromovProductProperty`: The Gromov product satisfies a triangle-like inequality

## Main results

* `fourPoint_implies_gromovProduct`: The 4-point condition implies the Gromov product property

## References

* [M. Gromov, *Hyperbolic groups*][Gromov1987]
* [É. Ghys, P. de la Harpe, *Sur les groupes hyperboliques d'après Mikhael Gromov*][GhysHarpe1990]

-/

variable {X : Type*} [MetricSpace X]

/-- The Gromov product `(x|y)_w` measures how close x and y are when viewed from w.
Intuitively, it measures the distance from w to the "intersection" of geodesics from w to x
and from w to y. -/
noncomputable def GromovProduct (x y w : X) : ℝ :=
  (dist x w + dist y w - dist x y) / 2

namespace GromovProduct

variable {x y z w : X}

/-- The Gromov product is symmetric in its first two arguments -/
theorem symm : GromovProduct x y w = GromovProduct y x w := by
  simp only [GromovProduct, dist_comm y x, add_comm]

/-- The Gromov product is non-negative -/
theorem nonneg : 0 ≤ GromovProduct x y w := by
  unfold GromovProduct
  have h := dist_triangle x y w
  have h' : dist x y ≤ dist x w + dist y w := by
    calc dist x y
        ≤ dist x w + dist w y := dist_triangle x w y
      _ = dist x w + dist y w := by rw [dist_comm w y]
  apply div_nonneg
  · linarith
  · norm_num

/-- The Gromov product is bounded by the minimum distance from w -/
theorem le_min : GromovProduct x y w ≤ min (dist x w) (dist y w) := by
  unfold GromovProduct
  have h : |dist x w - dist y w| ≤ dist x y := abs_dist_sub_le x y w
  by_cases hxy : dist x w ≤ dist y w
  · simp only [min_eq_left hxy]
    have hab : |dist x w - dist y w| = -(dist x w - dist y w) :=
      abs_of_nonpos (sub_nonpos_of_le hxy)
    have : dist y w - dist x w = -(dist x w - dist y w) := by ring
    linarith
  · push_neg at hxy
    simp only [min_eq_right (le_of_lt hxy)]
    have : |dist x w - dist y w| = dist x w - dist y w := abs_of_pos (sub_pos_of_lt hxy)
    linarith

end GromovProduct

/-- A metric space satisfies the 4-point condition with constant δ if for all quadruples of points,
the sum of opposite sides is bounded. This is equivalent to δ-hyperbolicity. -/
def FourPointCondition (δ : ℝ) : Prop :=
  ∀ x y z w : X, dist x y + dist z w ≤ max (dist x z + dist y w) (dist x w + dist y z) + 2 * δ

/-- A metric space satisfies the Gromov product property with constant δ if the Gromov product
satisfies a certain triangle-like inequality. -/
def GromovProductProperty (δ : ℝ) : Prop :=
  ∀ x y z w : X, GromovProduct x y w ≥ min (GromovProduct x z w) (GromovProduct z y w) - δ

set_option linter.unusedVariables false in
/-- If a metric space satisfies the 4-point condition with constant δ,
then it satisfies the Gromov product property with the same constant δ. -/
theorem fourPoint_implies_gromovProduct {δ : ℝ} (hδ : δ ≥ 0) (h : FourPointCondition (X := X) δ) :
    GromovProductProperty (X := X) δ := by
  intro x y z w
  unfold GromovProduct
  -- We need to show: (dist x w + dist y w - dist x y) / 2 ≥
  --                   min ((dist x w + dist z w - dist x z) / 2)
  --                       ((dist z w + dist y w - dist z y) / 2) - δ

  -- Apply the 4-point condition to quadruple (x, y, z, w)
  have h1 := h x y z w
  -- This gives: dist x y + dist z w ≤ max (dist x z + dist y w) (dist x w + dist y z) + 2 * δ

  by_cases hmax : dist x z + dist y w ≤ dist x w + dist y z
  · -- Case: max is (dist x w + dist y z)
    have : dist x y + dist z w ≤ dist x w + dist y z + 2 * δ := by
      calc dist x y + dist z w
          ≤ max (dist x z + dist y w) (dist x w + dist y z) + 2 * δ := h1
        _ = dist x w + dist y z + 2 * δ := by simp [max_eq_right hmax]

    -- Rearranging: dist x w + dist y w - dist x y ≥ dist z w + dist y w - dist z y - 2 * δ
    have key : dist x w + dist y w - dist x y ≥ dist z w + dist y w - dist z y - 2 * δ := by
      have : dist z y = dist y z := dist_comm z y
      linarith

    -- Divide by 2 and use that (z|y)_w is the minimum
    have : (dist x w + dist y w - dist x y) / 2 ≥ (dist z w + dist y w - dist z y) / 2 - δ := by
      linarith

    calc (dist x w + dist y w - dist x y) / 2
        ≥ (dist z w + dist y w - dist z y) / 2 - δ := this
      _ ≥ min ((dist x w + dist z w - dist x z) / 2) ((dist z w + dist y w - dist z y) / 2) - δ :=
          by linarith [min_le_right ((dist x w + dist z w - dist x z) / 2)
                                    ((dist z w + dist y w - dist z y) / 2)]

  · -- Case: max is (dist x z + dist y w)
    push_neg at hmax
    have : dist x y + dist z w ≤ dist x z + dist y w + 2 * δ := by
      calc dist x y + dist z w
          ≤ max (dist x z + dist y w) (dist x w + dist y z) + 2 * δ := h1
        _ = dist x z + dist y w + 2 * δ := by simp [max_eq_left (le_of_lt hmax)]

    -- Rearranging: dist x w + dist y w - dist x y ≥ dist x w + dist z w - dist x z - 2 * δ
    have key : dist x w + dist y w - dist x y ≥ dist x w + dist z w - dist x z - 2 * δ := by
      linarith

    -- Divide by 2 and use that (x|z)_w is the minimum
    have : (dist x w + dist y w - dist x y) / 2 ≥ (dist x w + dist z w - dist x z) / 2 - δ := by
      linarith

    calc (dist x w + dist y w - dist x y) / 2
        ≥ (dist x w + dist z w - dist x z) / 2 - δ := this
      _ ≥ min ((dist x w + dist z w - dist x z) / 2) ((dist z w + dist y w - dist z y) / 2) - δ :=
          by linarith [min_le_left ((dist x w + dist z w - dist x z) / 2)
                                    ((dist z w + dist y w - dist z y) / 2)]
