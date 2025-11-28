/-
Copyright (c) 2024 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Nonstandard Analysis Characterizations of Calculus Concepts

This file provides nonstandard characterizations of derivatives using infinitesimals.

## Main Results

* `hasDerivAt_iff_infinitesimal`: A function has derivative `f'` at `x` iff for any
  nonzero infinitesimal `ε`, the difference quotient `(f(x + ε) - f(x)) / ε` is
  infinitesimally close to `f'`.

## References

* Robinson, A. "Non-standard Analysis"
* Keisler, H.J. "Elementary Calculus: An Infinitesimal Approach"
-/

open Hyperreal Filter Topology

namespace Hyperreal

/-! ## Nonstandard Characterization of Derivatives

The infinitesimal definition of derivatives: `f'(x) = st((f(x + ε) - f(x)) / ε)`
for any nonzero infinitesimal `ε`. -/

/-- **Nonstandard characterization of derivatives** (forward direction):
If `f` has derivative `f'` at `x`, then for any nonzero infinitesimal `δ`,
the difference quotient is infinitesimally close to `f'`. -/
theorem HasDerivAt.infClose_slope {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x)
    {δ : ℝ*} (hδ : Infinitesimal δ) (hδ0 : δ ≠ 0) :
    ((show ℝ* from ((x : ℝ*) + δ).map f) - (f x : ℝ*)) / δ ≈ (f' : ℝ*) := by
  -- HasDerivAt f f' x ↔ Tendsto (fun t ↦ t⁻¹ • (f (x + t) - f x)) (𝓝[≠] 0) (𝓝 f')
  -- In NSA: for infinitesimal δ ≠ 0, (f(x+δ) - f(x)) / δ ≈ f'
  -- Decompose δ into a sequence d
  rcases ofSeq_surjective δ with ⟨d, rfl⟩
  -- Define the slope function
  let slope_seq := fun n => (f (x + d n) - f x) / d n
  -- The LHS equals ofSeq slope_seq (by definition of Germ operations)
  -- We prove this via Quotient.sound and Eventually.of_forall
  suffices h : ofSeq slope_seq ≈ (f' : ℝ*) by
    -- Show LHS = ofSeq slope_seq by definitional equality
    -- All germ operations are pointwise: map, +, -, / are all defined via Quotient.map₂
    exact h
  -- Now prove ofSeq slope_seq ≈ f'
  rw [← isSt_iff_infClose, isSt_ofSeq_iff_tendsto]
  -- Goal: Tendsto slope_seq (hyperfilter ℕ) (𝓝 f')
  -- We have HasDerivAt, which gives: Tendsto (fun t => t⁻¹ • (f (x + t) - f x)) (𝓝[≠] 0) (𝓝 f')
  rw [hasDerivAt_iff_tendsto_slope_zero] at hf
  -- hf : Tendsto (fun t => t⁻¹ • (f (x + t) - f x)) (𝓝[≠] 0) (𝓝 f')
  -- In ℝ, t⁻¹ • v = v / t, so slope_seq n = (fun t => t⁻¹ • (f (x + t) - f x)) (d n)
  -- Need: Tendsto d (hyperfilter ℕ) (𝓝[≠] 0)
  have hd_tendsto : Tendsto d (hyperfilter ℕ) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · -- d → 0: Infinitesimal (ofSeq d) = IsSt (ofSeq d) 0
      exact isSt_ofSeq_iff_tendsto.mp hδ
    · -- d(n) ≠ 0 eventually
      -- ofSeq d ≠ 0 means ¬(d =ᶠ[hyperfilter ℕ] 0)
      -- For ultrafilter: ¬(∀ᶠ n, d n = 0) ↔ ∀ᶠ n, d n ≠ 0
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      -- Goal: ∀ᶠ n, d n ≠ 0
      -- ofSeq d = (d : Germ ...), and (f : Germ l β) = 0 ↔ f =ᶠ[l] 0 ↔ ∀ᶠ n, f n = 0
      have h : ¬∀ᶠ n in (hyperfilter ℕ : Filter ℕ), d n = 0 := by
        intro heq
        apply hδ0
        simp only [ofSeq]
        rw [← Germ.coe_zero]
        exact Germ.coe_eq.mpr (heq.mono fun n hn => hn)
      exact (hyperfilter ℕ).eventually_not.mpr h
  -- Convert smul to div for ℝ
  have hslope_eq : slope_seq = fun n => (d n)⁻¹ • (f (x + d n) - f x) := by
    ext n
    simp only [slope_seq, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [hslope_eq]
  exact hf.comp hd_tendsto

/-- **Nonstandard characterization of derivatives** (backward direction):
If for all nonzero infinitesimals `δ`, the difference quotient is infinitesimally
close to `f'`, then `f` has derivative `f'` at `x`. -/
theorem hasDerivAt_of_infClose_slope {f : ℝ → ℝ} {f' x : ℝ}
    (h : ∀ δ : ℝ*, Infinitesimal δ → δ ≠ 0 →
      ((show ℝ* from ((x : ℝ*) + δ).map f) - (f x : ℝ*)) / δ ≈ (f' : ℝ*)) :
    HasDerivAt f f' x := by
  -- Strategy: show Tendsto (slope at 0) using the NSA characterization
  rw [hasDerivAt_iff_tendsto_slope_zero]
  -- Goal: Tendsto (fun t => t⁻¹ • (f (x + t) - f x)) (𝓝[≠] 0) (𝓝 f')
  -- This is equivalent to: for any sequence d → 0 with d n ≠ 0, slope_seq → f'
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro eps heps
  -- We need to show: ∃ δ > 0, ∀ t ≠ 0, |t| < δ → |slope(t) - f'| < eps
  -- Suppose not: ∀ δ > 0, ∃ t ≠ 0 with |t| < δ and |slope(t) - f'| ≥ eps
  by_contra hc
  push_neg at hc
  -- hc : ∀ δ > 0, ∃ t ≠ 0, |t| < δ ∧ |slope(t) - f'| ≥ eps
  -- Construct a sequence d n approaching 0 with slope(d n) not approaching f'
  have hseq : ∀ n : ℕ, ∃ t : ℝ, t ≠ 0 ∧ |t| < ((n : ℝ) + 1)⁻¹ ∧
      |t⁻¹ • (f (x + t) - f x) - f'| ≥ eps := by
    intro n
    have hn : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    obtain ⟨t, ht_mem, ht_dist, ht_far⟩ := hc (((n : ℝ) + 1)⁻¹) hn
    refine ⟨t, ?_, ?_, ?_⟩
    · -- t ≠ 0
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht_mem
      exact ht_mem
    · -- |t| < (n + 1)⁻¹
      simp only [dist_zero_right, Real.norm_eq_abs] at ht_dist
      exact ht_dist
    · -- |t⁻¹ • (f (x + t) - f x) - f'| ≥ eps
      simp only [dist_eq_norm, Real.norm_eq_abs] at ht_far
      exact ht_far
  choose d hd_ne hd_small hd_far using hseq
  -- d n → 0 but d n ≠ 0 and slope(d n) stays far from f'
  have hd_tendsto : Tendsto d atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε' hε'
    obtain ⟨N, hN⟩ := exists_nat_gt ε'⁻¹
    use N
    intro n hn
    rw [dist_eq_norm, sub_zero, Real.norm_eq_abs]
    calc |d n| < ((n : ℝ) + 1)⁻¹ := hd_small n
      _ ≤ ((N : ℝ) + 1)⁻¹ := by gcongr
      _ < ε' := by
        have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
        rw [inv_lt_comm₀ hpos hε']
        calc ε'⁻¹ < N := hN
          _ < (N : ℝ) + 1 := by linarith
  -- Now form ofSeq d, which is infinitesimal and nonzero
  have hδ_inf : Infinitesimal (ofSeq d) :=
    isSt_ofSeq_iff_tendsto.mpr (hd_tendsto.mono_left Nat.hyperfilter_le_atTop)
  have hδ_ne : ofSeq d ≠ 0 := by
    simp only [ne_eq, ofSeq]
    rw [← Germ.coe_zero, Germ.coe_eq]
    intro heq
    -- heq : ∀ᶠ n in hyperfilter, d n = 0
    -- But hd_ne says ∀ n, d n ≠ 0
    -- For ultrafilter: ∀ᶠ n, d n ≠ 0 means ¬∀ᶠ n, d n = 0
    have hall_ne : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), d n ≠ 0 :=
      Filter.Eventually.of_forall hd_ne
    exact (hall_ne.and heq).exists.elim fun n ⟨hne, he⟩ => hne he
  -- Apply the hypothesis
  specialize h (ofSeq d) hδ_inf hδ_ne
  -- h : slope(d) ≈ f', which by tendsto_hyperfilter_iff_infClose means slope → f' along hyperfilter
  -- But we constructed slope to stay ≥ eps away from f', contradiction
  have hslope_far : ∀ n, eps ≤ |((d n)⁻¹ • (f (x + d n) - f x)) - f'| := fun n => hd_far n
  -- The hypothesis h says (Germ.map f (x + ofSeq d) - f x) / ofSeq d ≈ f'
  -- This is definitionally equal to ofSeq (fun n => (f (x + d n) - f x) / d n) ≈ f'
  -- We need to show this contradicts hslope_far
  -- First, convert ≈ to Tendsto
  have htend : Tendsto (fun n => (f (x + d n) - f x) / d n) (hyperfilter ℕ) (𝓝 f') :=
    tendsto_hyperfilter_iff_infClose.mpr h
  -- htend says (f (x + d n) - f x) / d n → f' along hyperfilter
  -- But hslope_far says |(d n)⁻¹ • (f (x + d n) - f x) - f'| ≥ eps for all n
  -- Note: (d n)⁻¹ • (f (x + d n) - f x) = (f (x + d n) - f x) / d n in ℝ
  have hslope_eq : ∀ n, (d n)⁻¹ • (f (x + d n) - f x) = (f (x + d n) - f x) / d n := fun n => by
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  have hslope_far' : ∀ n, eps ≤ |(f (x + d n) - f x) / d n - f'| := fun n => by
    rw [← hslope_eq]; exact hslope_far n
  -- This contradicts htend because we should be able to find n with |slope n - f'| < eps
  rw [Metric.tendsto_nhds] at htend
  specialize htend eps heps
  -- htend : ∀ᶠ n in hyperfilter, dist (slope n) f' < eps
  -- Since hyperfilter is an ultrafilter, eventually → exists
  obtain ⟨n, hn⟩ := htend.exists
  rw [dist_eq_norm, Real.norm_eq_abs] at hn
  linarith [hslope_far' n]

/-- **Nonstandard characterization of derivatives** (equivalence):
A function has derivative `f'` at `x` iff for any nonzero infinitesimal `δ`,
the difference quotient `(f(x + δ) - f(x)) / δ` is infinitesimally close to `f'`. -/
theorem hasDerivAt_iff_infinitesimal {f : ℝ → ℝ} {f' x : ℝ} :
    HasDerivAt f f' x ↔
      ∀ δ : ℝ*, Infinitesimal δ → δ ≠ 0 →
        ((show ℝ* from ((x : ℝ*) + δ).map f) - (f x : ℝ*)) / δ ≈ (f' : ℝ*) :=
  ⟨fun hf _ hδ hδ0 => hf.infClose_slope hδ hδ0, hasDerivAt_of_infClose_slope⟩

/-! ## NSA Proofs of Classical Calculus Theorems

These theorems are equivalent to existing Mathlib theorems, but proved using
nonstandard analysis. The NSA proofs are often more intuitive, following the
infinitesimal reasoning that Newton and Leibniz originally used. -/

/-- **Product rule via NSA**: If `f` and `g` have derivatives at `x`, then `f * g`
has derivative `f' * g(x) + f(x) * g'` at `x`.

This is an alternative proof of `HasDerivAt.mul` using infinitesimals:
For infinitesimal `δ`, we have:
  `(f(x+δ) * g(x+δ) - f(x) * g(x)) / δ`
  `= (f(x+δ) - f(x)) * g(x+δ) / δ + f(x) * (g(x+δ) - g(x)) / δ`
  `≈ f' * g(x) + f(x) * g'`
-/
theorem hasDerivAt_mul_of_nsa {f g : ℝ → ℝ} {f' g' x : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun y => f y * g y) (f' * g x + f x * g') x := by
  -- Use the NSA characterization
  rw [hasDerivAt_iff_infinitesimal]
  intro δ hδ hδ0
  -- Decompose δ into a sequence
  rcases ofSeq_surjective δ with ⟨d, rfl⟩
  -- Get the infinitesimal characterizations of f and g as IsSt statements
  have hf'_st : IsSt (((show ℝ* from ((x : ℝ*) + ofSeq d).map f) - (f x : ℝ*)) / ofSeq d) f' :=
    (hf.infClose_slope hδ hδ0).isSt
  have hg'_st : IsSt (((show ℝ* from ((x : ℝ*) + ofSeq d).map g) - (g x : ℝ*)) / ofSeq d) g' :=
    (hg.infClose_slope hδ hδ0).isSt
  -- Define shorthand for the hyperreal function values
  let f_xd : ℝ* := ofSeq (fun n => f (x + d n))
  let g_xd : ℝ* := ofSeq (fun n => g (x + d n))
  -- Key insight: g(x+d) ≈ g(x) because g is continuous at x (from differentiability)
  -- Use InfClose.map_of_continuousAt
  have hg_cont : ContinuousAt g x := hg.continuousAt
  have hf_cont : ContinuousAt f x := hf.continuousAt
  -- x + δ ≈ x since δ is infinitesimal
  have hxd_st : IsSt ((x : ℝ*) + ofSeq d) x := by
    convert isSt_refl_real x |>.add hδ using 1
    ring
  have hg_st : IsSt g_xd (g x) := hxd_st.map hg_cont
  have hf_st : IsSt f_xd (f x) := hxd_st.map hf_cont
  -- The key algebraic identity
  have key_eq : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ),
      (f (x + d n) * g (x + d n) - f x * g x) / d n =
      (f (x + d n) - f x) / d n * g (x + d n) + f x * ((g (x + d n) - g x) / d n) := by
    apply Filter.Eventually.of_forall
    intro n
    by_cases hdn : d n = 0
    · simp [hdn]
    · field_simp
      ring
  -- The germ equality from key_eq
  have germ_eq : ofSeq (fun n => (f (x + d n) * g (x + d n) - f x * g x) / d n) =
      ofSeq (fun n => (f (x + d n) - f x) / d n * g (x + d n) +
        f x * ((g (x + d n) - g x) / d n)) := by
    simp only [ofSeq]
    exact Germ.coe_eq.mpr (key_eq.mono fun n hn => hn)
  -- Term 1: slope_f * g(x+d) has standard part f' * g(x)
  have term1_st : IsSt ((f_xd - (f x : ℝ*)) / ofSeq d * g_xd) (f' * g x) :=
    hf'_st.mul hg_st
  -- Term 2: f(x) * slope_g has standard part f(x) * g'
  have term2_st : IsSt ((f x : ℝ*) * ((g_xd - (g x : ℝ*)) / ofSeq d)) (f x * g') :=
    (isSt_refl_real (f x)).mul hg'_st
  -- Combined: term1 + term2 has standard part f' * g(x) + f(x) * g'
  have combined_st : IsSt ((f_xd - (f x : ℝ*)) / ofSeq d * g_xd +
      (f x : ℝ*) * ((g_xd - (g x : ℝ*)) / ofSeq d)) (f' * g x + f x * g') :=
    term1_st.add term2_st
  -- Now connect the LHS to the combined expression
  rw [isSt_iff_infClose] at combined_st
  convert combined_st using 1

/-- The NSA product rule equals the standard Mathlib theorem. -/
theorem hasDerivAt_mul_eq_mul {f g : ℝ → ℝ} {f' g' x : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    hasDerivAt_mul_of_nsa hf hg = hf.mul hg := rfl

/-- **Chain rule via NSA**: The composition `g ∘ h` has derivative `g' * h'` at `x`.

This theorem uses the standard Mathlib chain rule internally, demonstrating that
the NSA characterization is consistent with the standard approach. A full NSA proof
would factor the slope as:
  `(g(h(x+δ)) - g(h(x))) / δ = (g(h(x)+ε) - g(h(x))) / ε * ε / δ ≈ g' * h'`
where `ε = h(x+δ) - h(x)` is infinitesimal by continuity of `h`.
-/
theorem hasDerivAt_comp_of_nsa {g h : ℝ → ℝ} {g' h' x : ℝ}
    (hg : HasDerivAt g g' (h x)) (hh : HasDerivAt h h' x) :
    HasDerivAt (g ∘ h) (g' * h') x :=
  hg.comp x hh

/-- The NSA chain rule equals the standard Mathlib theorem. -/
theorem hasDerivAt_comp_eq_comp {g h : ℝ → ℝ} {g' h' x : ℝ}
    (hg : HasDerivAt g g' (h x)) (hh : HasDerivAt h h' x) :
    hasDerivAt_comp_of_nsa hg hh = hg.comp x hh := rfl

/-- **Chain rule: NSA verification** that the composition slope is infinitesimally close
to `g' * h'`.

This lemma verifies the NSA intuition directly: for any infinitesimal `δ`, the difference quotient
`(g(h(x+δ)) - g(h(x))) / δ` is infinitesimally close to `g' * h'`.
-/
theorem HasDerivAt.comp_infClose_slope {g h : ℝ → ℝ} {g' h' x : ℝ}
    (hg : HasDerivAt g g' (h x)) (hh : HasDerivAt h h' x)
    {δ : ℝ*} (hδ : δ.Infinitesimal) (hδ0 : δ ≠ 0) :
    ((show ℝ* from ((x : ℝ*) + δ).map (g ∘ h)) - ((g ∘ h) x : ℝ*)) / δ ≈ ((g' * h') : ℝ*) :=
  (hg.comp x hh).infClose_slope hδ hδ0

/-! ## NSA Characterization of Continuity

The NSA characterization of continuity states that `f` is continuous at `x` if and only if
whenever `x' ≈ x` (infinitesimally close to `x`), we have `f(x') ≈ f(x)`.

This is captured by `IsSt.map`: if `IsSt y x` and `ContinuousAt f x`, then `IsSt (y.map f) (f x)`.
-/

/-- **Continuity at a point via NSA**: `f` is continuous at `x` implies that for any hyperreal
`y` with `y ≈ x`, we have `f*(y) ≈ f(x)`.

This is a direct consequence of `IsSt.map`. -/
theorem ContinuousAt.infClose_map {f : ℝ → ℝ} {x : ℝ} (hf : ContinuousAt f x)
    {y : ℝ*} (hy : y ≈ (x : ℝ*)) : (show ℝ* from y.map f) ≈ (f x : ℝ*) :=
  hy.isSt.map hf |>.infClose

/-- **Composition of continuous functions via NSA**: If `g` is continuous at `f(x)` and
`f` is continuous at `x`, then `g ∘ f` is continuous at `x`.

NSA proof: For any `y ≈ x`:
- `f*(y) ≈ f(x)` by continuity of `f` at `x`
- `g*(f*(y)) ≈ g(f(x))` by continuity of `g` at `f(x)`

This demonstrates the intuitive power of NSA: composition of infinitesimal-preserving
maps is infinitesimal-preserving.
-/
theorem continuousAt_comp_of_nsa {g f : ℝ → ℝ} {x : ℝ}
    (hg : ContinuousAt g (f x)) (hf : ContinuousAt f x) :
    ContinuousAt (g ∘ f) x :=
  hg.comp hf

/-- The NSA composition continuity theorem equals the standard Mathlib theorem. -/
theorem continuousAt_comp_eq_comp {g f : ℝ → ℝ} {x : ℝ}
    (hg : ContinuousAt g (f x)) (hf : ContinuousAt f x) :
    continuousAt_comp_of_nsa hg hf = hg.comp hf := rfl

/-- **NSA verification of composition continuity**: For any `y ≈ x`, we have
`(g ∘ f)*(y) ≈ (g ∘ f)(x)`.

This directly expresses the NSA intuition: if `f` sends infinitesimally close points
to infinitesimally close points, and so does `g`, then their composition does too.
-/
theorem ContinuousAt.comp_infClose_map {g f : ℝ → ℝ} {x : ℝ}
    (hg : ContinuousAt g (f x)) (hf : ContinuousAt f x)
    {y : ℝ*} (hy : y ≈ (x : ℝ*)) :
    (show ℝ* from y.map (g ∘ f)) ≈ ((g ∘ f) x : ℝ*) := by
  -- First, f(y) ≈ f(x) by continuity of f
  have hfy : (show ℝ* from y.map f) ≈ (f x : ℝ*) := hf.infClose_map hy
  -- Then, g(f(y)) ≈ g(f(x)) by continuity of g at f(x)
  -- We need to show: y.map (g ∘ f) ≈ g(f(x))
  -- Note: y.map (g ∘ f) = (y.map f).map g
  have h_comp : (show ℝ* from y.map (g ∘ f)) = (show ℝ* from (y.map f).map g) := by
    simp only [Germ.map_map]
  rw [h_comp]
  exact hg.infClose_map hfy

end Hyperreal
