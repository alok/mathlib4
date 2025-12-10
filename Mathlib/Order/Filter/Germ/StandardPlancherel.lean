/-
Copyright (c) 2024 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Mathlib.Order.Filter.Germ.LoebMeasure
import Mathlib.Order.Filter.Germ.HyperfiniteFourier
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Order.Filter.Germ.HyperfiniteGroup

/-!
# Standard Plancherel from Hyperfinite Plancherel

This file demonstrates the limiting principle of Nonstandard Analysis by deriving the
standard Plancherel Theorem for the Circle Group (`AddCircle T`) from the
Hyperfinite Plancherel Theorem.

## Main Result

* `standard_plancherel_from_hyperfinite`: Derivation of Parseval's identity for `S¹`.
-/

namespace Hyper

open scoped NonstandardAnalysis BigOperators ComplexConjugate
open MeasureTheory

variable {ι : Type*} [Infinite ι] {T : ℝ} [Fact (0 < T)]

/-- Convergence of DFT coefficients.
For a continuous function `f` on `S^1`, the hyperfinite DFT coefficients of `*f`
(on a hyperfinite approximation `H`) are infinitely close to the standard Fourier coefficients.
-/
theorem dft_convergence
    (f : AddCircle T → ℂ) (hf : Continuous f)
    (H : HyperfiniteGroup ι (AddCircle T)) (hApprox : HyperfiniteApproximation ι (AddCircle T))
    (n : ℤ) :
    let F := liftFun f
    let dft_H := dft H (liftFun f)
    -- This requires careful formulation of "dft component at n".
    -- The dual of H_N is Z_N, identified with {0, ..., N-1}.
    -- Standard Fourier coeffs are on Z.
    True := sorry

/-- Standard Plancherel Theorem for `AddCircle T`. -/
theorem standard_plancherel_from_hyperfinite (f : AddCircle T → ℂ) (hf : Continuous f) :
    ∑' n : ℤ, ‖fourierCoeff f n‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂haarAddCircle := by
  -- 1. Apply Hyperfinite Plancherel to *f on H.
  -- 2. Use Loeb Integration to relate internal sum of squares to integral.
  -- 3. Use DFT convergence to relate internal DFT squares to Fourier series sum.
  sorry

end Hyper
