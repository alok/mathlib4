import Mathlib.Order.Filter.Germ.HyperfiniteGroup
import Mathlib.Algebra.DirectSum.AddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Hyperfinite Fourier Analysis

This file defines the Discrete Fourier Transform (DFT) for hyperfinite groups and proves Plancherel's Theorem.

## Definitions

* `standardDFT`: The standard DFT on a finite abelian group.
* `dft`: The hyperfinite DFT, obtained by transferring the standard DFT.

## Main Results

* `standardPlancherel`: Plancherel's theorem for finite abelian groups.
* `plancherel`: Plancherel's theorem for hyperfinite groups.
-/

open scoped BigOperators
open Complex

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The standard Discrete Fourier Transform on a finite abelian group. -/
noncomputable def standardDFT (f : G → ℂ) (χ : AddChar G ℂ) : ℂ :=
  ∑ x, f x * conj (χ x)

/-- Plancherel's Theorem for finite abelian groups. -/
theorem standardPlancherel (f : G → ℂ) :
    ∑ χ : AddChar G ℂ, normSq (standardDFT f χ) = Fintype.card G * ∑ x, normSq (f x) := by
  simp only [standardDFT, normSq_eq_abs, abs_mul, Complex.abs_sum, map_sum]
  -- We proceed by expanding the LHS sum
  simp_rw [normSq_eq_conj_mul_self, map_sum, Finset.sum_mul_sum]
  -- Rearrange sums
  rw [Finset.sum_comm]
  trans ∑ x : G, ∑ y : G, f x * conj (f y) * ∑ χ : AddChar G ℂ, conj (χ x) * χ y
  · simp_rw [mul_assoc]
    apply Finset.sum_congr rfl fun x _ => ?_
    apply Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_mul]
    apply Finset.sum_congr rfl fun χ _ => ?_
    ring_nf
    rw [map_mul, StarRingEnd_apply, map_mul, StarRingEnd_apply, StarRingEnd_apply, starRingEnd_self_apply]
    simp
  -- Use character orthogonality
  simp_rw [← map_sub, ← map_neg_eq_conj, ← map_add_eq_mul, ← sub_eq_add_neg, AddChar.sum_apply_eq_ite]
  -- The inner sum is |G| if y - x = 0 (i.e., y = x), else 0
  have h_inner : ∀ x y, ∑ χ : AddChar G ℂ, conj (χ x) * χ y = if y = x then (Fintype.card G : ℂ) else 0 := by
    intro x y
    simp_rw [← map_sub, ← map_neg_eq_conj, ← map_add_eq_mul, ← sub_eq_add_neg]
    rw [AddChar.sum_apply_eq_ite (y - x)]
    split_ifs with h
    · simp at h; rw [h, if_pos rfl]
    · simp at h; rw [if_neg]; exact fun c => h c.symm
  simp_rw [h_inner]
  -- Collapse the sums standard way
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl fun x _ => ?_
  rw [normSq_eq_conj_mul_self]
  ring

namespace Hyper

open scoped NonstandardAnalysis

variable {ι : Type*} [Infinite ι] {α : Type*} [AddCommGroup α]

/-- The hyperfinite Discrete Fourier Transform. -/
noncomputable def dft (H : HyperfiniteGroup ι α) (f : Hyper ι (α → ℂ)) :
    Hyper ι (Σ G : Subgroup α, AddChar G ℂ → ℂ) :=
  Hyper.lift₂ (fun (G : Subgroup α) (g : α → ℂ) =>
    letI : Fintype G := Fintype.ofFinite G
    ⟨G, standardDFT (G := G) (fun x => g x)⟩
  ) H.toSubgroup f

-- Helper to extract the DFT result "norm squared sum"
noncomputable def dftNormSqSum (H : HyperfiniteGroup ι α) (f : Hyper ι (α → ℂ)) : Hyper ι ℝ :=
  Hyper.lift₂ (fun (G : Subgroup α) (g : α → ℂ) =>
    letI : Fintype G := Fintype.ofFinite G
    ∑ χ : AddChar G ℂ, normSq (standardDFT (G := G) (fun x => g x) χ)
  ) H.toSubgroup f

noncomputable def functionNormSqSum (H : HyperfiniteGroup ι α) (f : Hyper ι (α → ℂ)) : Hyper ι ℝ :=
  Hyper.lift₂ (fun (G : Subgroup α) (g : α → ℂ) =>
    letI : Fintype G := Fintype.ofFinite G
    ∑ x : G, normSq (g x)
  ) H.toSubgroup f

theorem plancherel (H : HyperfiniteGroup ι α) (f : Hyper ι (α → ℂ)) :
    dftNormSqSum H f = hyperfiniteCard H.carrier H.isHyperfinite * functionNormSqSum H f := by
  apply Hyper.inductionOn₂ H.toSubgroup f
  intro G g
  simp [dftNormSqSum, functionNormSqSum, hyperfiniteCard, Hyper.lift_coe, Hyper.lift₂_coe]
  letI : Fintype G := Fintype.ofFinite G
  letI : DecidableEq G := Classical.decEq G
  -- Coerce standardPlancherel to Hyper
  have h := standardPlancherel (fun x => g x)
  norm_cast at h
  rw [h]
  simp

end Hyper
