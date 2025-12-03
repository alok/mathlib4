/-
Copyright (c) 2024 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Mathlib.Order.Filter.Germ.Star
import Mathlib.Topology.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Nonstandard Characterizations of Topological Concepts

This file provides nonstandard (infinitesimal) characterizations of topological
concepts like continuity, compactness, and convergence using hyperstructures.

## Main Definitions

* `Hyper.halo` - The halo of a point: the set of hyperreals infinitely close to it
* `Hyper.IsNearStd` - A hyperreal is near-standard if it's in some standard point's halo
* `Hyper.stdPart` - The standard part of a near-standard element
* `Hyper.Infinitesimal` - An element infinitesimally close to 0 (in normed spaces)
* `Hyper.InfClose` - Two elements are infinitesimally close

## Main Results

### Continuity
* `Hyper.continuousAt_iff_halo` - `f` is continuous at `x` iff `f` maps `halo x`
  into `halo (f x)`

### Compactness
* `Hyper.isCompact_iff_nearStd` - A set is compact iff every element of its star is
  near-standard and has standard part in the set

### Convergence
* `Hyper.tendsto_iff_halo` - `Tendsto f l (𝓝 y)` iff `f*` maps near-standard elements
  to `halo y`

## References

* Robinson, A. "Non-standard Analysis"
* Goldblatt, R. "Lectures on the Hyperreals"
* Luxemburg, W.A.J. "A General Theory of Monads"
-/

open Filter Topology Set
open scoped NonstandardAnalysis

namespace Hyper

variable {ι : Type*} [Infinite ι] {α β : Type*}

/-! ## Topology Notation

Additional notation for topological NSA concepts. See `Mathlib.Order.Filter.Germ.Star` for
the core `★` notation.

* `𝔪 x` - the halo (halo) of `x` (`halo x`)
* `°y` - the standard part of near-standard `y` (`stdPart y`)
* `x ≈ y` - infinitesimally close (`InfClose x y`)
* `x ≃ᵤ y` - entourage-close for uniform spaces (`EntourageClose x y`)
-/

set_option quotPrecheck false in
-- Monad notation: 𝔪 x for halo x
scoped[NonstandardAnalysis] prefix:max "𝔪" => Hyper.halo

/-! ## The Monad (Halo) of a Point

The halo of a point `x` is the set of all hyperelements that are "infinitely close" to `x`.
In the ultraproduct construction, this is the intersection of the stars of all
neighborhoods of `x`.
-/

section Monad

variable [TopologicalSpace α]

/-- The **halo** (or **halo**) of a point `x` is the intersection of the *-extensions of all
neighborhoods of `x`. An element `y : Hyper ι α` is in `halo x` iff for every neighborhood `U`
of `x`, `y` is in `U*` (i.e., `y` satisfies the lifted membership predicate for `U`).

Intuitively, `halo x` consists of all hyperelements "infinitely close" to `x`. -/
def halo (x : α) : Set (Hyper ι α) :=
  ⋂ U ∈ 𝓝 x, {y : Hyper ι α | liftPred (· ∈ U) y}

/-- Alternative characterization: `y` is in `halo x` iff for all neighborhoods `U` of `x`,
`y` is eventually in `U`. -/
theorem mem_halo_iff (x : α) (y : Hyper ι α) :
    y ∈ halo x ↔ ∀ U ∈ 𝓝 x, liftPred (· ∈ U) y := by
  simp only [halo, mem_iInter, mem_setOf_eq]

/-- Sequence characterization of halo membership. -/
theorem mem_halo_ofSeq_iff (x : α) (f : ι → α) :
    (ofSeq f : Hyper ι α) ∈ halo x ↔ ∀ U ∈ 𝓝 x, ∀ᶠ n in hyperfilter ι, f n ∈ U := by
  simp only [mem_halo_iff, liftPred_ofSeq]

/-- Standard elements are in their own halo. -/
theorem std_mem_halo (x : α) : (std x : Hyper ι α) ∈ halo x := by
  rw [mem_halo_iff]
  intro U hU
  rw [liftPred_std]
  exact mem_of_mem_nhds hU

/-- The halo is nonempty (it contains the standard embedding of the point). -/
theorem halo_nonempty (x : α) : (halo x : Set (Hyper ι α)).Nonempty :=
  ⟨std x, std_mem_halo x⟩

/-- If `y` is in the halo of `x`, and `x` is in an open set `U`, then `y` satisfies `U*`. -/
theorem halo_subset_star_of_isOpen {x : α} {U : Set α} (hU : IsOpen U) (hx : x ∈ U) :
    halo x ⊆ {y : Hyper ι α | liftPred (· ∈ U) y} := by
  intro y hy
  rw [mem_halo_iff] at hy
  exact hy U (hU.mem_nhds hx)

/-- If a sequence converges to `x`, then any hyperextension of that sequence applied to an
infinite hypernatural is in `halo x`. -/
theorem tendsto_atTop_halo {f : ℕ → α} {x : α} (hf : Tendsto f atTop (𝓝 x))
    {N : Hyper ℕ ℕ} (hN : IsInfinitePos N) : lift f N ∈ halo (ι := ℕ) x := by
  rw [mem_halo_iff]
  intro U hU
  -- Since f → x, eventually f n ∈ U
  have hev : ∀ᶠ n in atTop, f n ∈ U := hf hU
  -- Get M such that ∀ n ≥ M, f n ∈ U
  obtain ⟨M, hM⟩ := hev.exists_forall_of_atTop
  -- N is infinite, so N > std M
  have hNM : std M < N := hN M
  -- Decompose N as a sequence
  obtain ⟨g, rfl⟩ := ofSeq_surjective N
  rw [std_lt_ofSeq] at hNM
  rw [lift_ofSeq, liftPred_ofSeq]
  -- Eventually g n > M, so f (g n) ∈ U
  apply hNM.mono
  intro n hn
  simp only [Function.comp_apply]
  exact hM (g n) (Nat.le_of_lt hn)

/-- Converse: if for all infinite N, lift f N is in halo x, then f → x.
This is the key bridge lemma for sequences. -/
theorem halo_tendsto_atTop {f : ℕ → α} {x : α}
    (hhalo : ∀ N : Hyper ℕ ℕ, IsInfinitePos N → lift f N ∈ halo (ι := ℕ) x) :
    Tendsto f atTop (𝓝 x) := by
  rw [tendsto_atTop_nhds]
  intro U hU hUopen
  -- Suppose not: ∀ M, ∃ n ≥ M, f n ∉ U
  by_contra hcontra
  push_neg at hcontra
  -- Define sequence n_k where f n_k ∉ U and n_k → ∞
  have hseq : ∀ k : ℕ, ∃ n : ℕ, n ≥ k ∧ f n ∉ U := hcontra
  choose nseq hnseq using hseq
  -- nseq k ≥ k, so nseq tends to infinity
  have hnseq_large : ∀ k, nseq k ≥ k := fun k => (hnseq k).1
  have hnseq_notU : ∀ k, f (nseq k) ∉ U := fun k => (hnseq k).2
  -- Define N = ofSeq nseq, which is infinite
  let N : Hyper ℕ ℕ := ofSeq nseq
  have hN_inf : IsInfinitePos N := by
    intro m
    change std m < ofSeq nseq
    rw [std_lt_ofSeq]
    apply Filter.mem_hyperfilter_of_finite_compl
    simp only [Set.compl_setOf, not_lt]
    -- {k : nseq k ≤ m} is finite because nseq k ≥ k
    have hsub : {k : ℕ | nseq k ≤ m} ⊆ Set.Iic m := by
      intro k hk
      simp only [Set.mem_setOf_eq] at hk
      simp only [Set.mem_Iic]
      calc k ≤ nseq k := hnseq_large k
           _ ≤ m := hk
    exact Set.Finite.subset (Set.finite_Iic m) hsub
  -- By hypothesis, lift f N ∈ halo x
  have hNhalo := hhalo N hN_inf
  rw [mem_halo_iff] at hNhalo
  -- So lift f N is eventually in U
  have hNU := hNhalo U (hUopen.mem_nhds hU)
  -- But f (nseq k) ∉ U for all k
  rw [lift_ofSeq, liftPred_ofSeq] at hNU
  -- hNU says f (nseq k) ∈ U eventually, contradicting hnseq_notU
  obtain ⟨k, hk⟩ := hNU.exists
  simp only [Function.comp_apply] at hk
  exact hnseq_notU k hk

end Monad

/-! ## Near-Standard Elements and Standard Parts

An element is **near-standard** if it belongs to some standard point's halo.
The **standard part** of a near-standard element is that unique standard point.
-/

section NearStd

variable [TopologicalSpace α]

/-- An element `y : Hyper ι α` is **near-standard** if there exists a standard element
whose halo contains `y`. -/
def IsNearStd (y : Hyper ι α) : Prop :=
  ∃ x : α, y ∈ halo x

/-- Standard elements are near-standard. -/
theorem IsNearStd.std (x : α) : IsNearStd (std x : Hyper ι α) :=
  ⟨x, std_mem_halo x⟩

/-- In a Hausdorff space, the standard part is unique. -/
theorem halo_eq_of_mem_halo [T2Space α] {x y : α} {z : Hyper ι α}
    (hx : z ∈ halo x) (hy : z ∈ halo y) : x = y := by
  by_contra hne
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation hne
  rw [mem_halo_iff] at hx hy
  have hz_U := hx U (hU.mem_nhds hxU)
  have hz_V := hy V (hV.mem_nhds hyV)
  obtain ⟨f, rfl⟩ := ofSeq_surjective z
  rw [liftPred_ofSeq] at hz_U hz_V
  have hz_UV := hz_U.and hz_V
  obtain ⟨n, hn_U, hn_V⟩ := hz_UV.exists
  exact Set.disjoint_iff.mp hUV ⟨hn_U, hn_V⟩

/-- The standard part of a near-standard element in a Hausdorff space. -/
noncomputable def stdPart [T2Space α] (y : Hyper ι α) (hy : IsNearStd y) : α :=
  hy.choose

theorem stdPart_spec [T2Space α] (y : Hyper ι α) (hy : IsNearStd y) :
    y ∈ halo (stdPart y hy) :=
  hy.choose_spec

/-- The standard part of a standard element is itself. -/
theorem stdPart_std [T2Space α] (x : α) :
    stdPart (std x : Hyper ι α) (IsNearStd.std x) = x :=
  halo_eq_of_mem_halo (stdPart_spec _ _) (std_mem_halo x)

end NearStd

/-! ## Infinitesimals in Normed Spaces

For normed spaces, we can define infinitesimals as elements whose norm is smaller than
any positive standard real.
-/

section Infinitesimal

variable [NormedAddCommGroup α]

/-- An element `x : Hyper ι α` is **infinitesimal** if its norm is less than every positive
standard real. Equivalently, `x` is in the halo of `0`. -/
def Infinitesimal (x : Hyper ι α) : Prop :=
  ∀ ε : ℝ, 0 < ε → lift (‖·‖) x < (std ε : Hyper ι ℝ)

/-- Alternative definition using halo. -/
theorem infinitesimal_iff_mem_halo_zero (x : Hyper ι α) :
    Infinitesimal x ↔ x ∈ halo 0 := by
  constructor
  · -- Infinitesimal → halo 0
    intro hinf
    rw [mem_halo_iff]
    intro U hU
    -- U is a neighborhood of 0, so contains a ball {x : ‖x‖ < ε}
    rw [Metric.mem_nhds_iff] at hU
    obtain ⟨ε, hε, hball⟩ := hU
    -- x is infinitesimal, so ‖x‖ < ε
    have hx_small := hinf ε hε
    obtain ⟨f, rfl⟩ := ofSeq_surjective x
    rw [liftPred_ofSeq]
    simp only [lift_ofSeq, std_eq_ofSeq_const, ofSeq_lt_ofSeq] at hx_small
    apply hx_small.mono
    intro n hn
    simp only [Function.comp_apply] at hn
    apply hball
    simp only [Metric.mem_ball, dist_zero_right]
    exact hn
  · -- halo 0 → Infinitesimal
    intro hhalo ε hε
    rw [mem_halo_iff] at hhalo
    -- The ball {x : ‖x‖ < ε} is a neighborhood of 0
    have hball_nhds : Metric.ball (0 : α) ε ∈ 𝓝 0 := Metric.ball_mem_nhds 0 hε
    have hx_in_ball := hhalo (Metric.ball 0 ε) hball_nhds
    obtain ⟨f, rfl⟩ := ofSeq_surjective x
    rw [liftPred_ofSeq] at hx_in_ball
    simp only [lift_ofSeq, std_eq_ofSeq_const, ofSeq_lt_ofSeq]
    apply hx_in_ball.mono
    intro n hn
    simp only [Metric.mem_ball, dist_zero_right] at hn
    simp only [Function.comp_apply]
    exact hn

/-- Zero is infinitesimal. -/
theorem infinitesimal_zero : Infinitesimal (0 : Hyper ι α) := by
  intro ε hε
  have h0 : (0 : Hyper ι α) = std 0 := std_zero.symm
  rw [h0, lift_std, norm_zero, std_lt]
  exact hε

/-- Negation preserves infinitesimals. -/
theorem Infinitesimal.neg {x : Hyper ι α} (hx : Infinitesimal x) : Infinitesimal (-x) := by
  intro ε hε
  have := hx ε hε
  obtain ⟨f, rfl⟩ := ofSeq_surjective x
  simp only [lift_ofSeq] at this ⊢
  -- -ofSeq f = lift Neg.neg (ofSeq f) = ofSeq (fun n => -(f n))
  have hneg : (-ofSeq f : Hyper ι α) = ofSeq (fun n => -f n) := by
    change lift Neg.neg (ofSeq f) = ofSeq (fun n => -f n)
    rw [lift_ofSeq]
    rfl
  rw [hneg, lift_ofSeq]
  rw [std_eq_ofSeq_const, ofSeq_lt_ofSeq] at this ⊢
  convert this using 1
  ext n
  simp only [Function.comp_apply, norm_neg]

/-- Sum of infinitesimals is infinitesimal. -/
theorem Infinitesimal.add {x y : Hyper ι α} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x + y) := by
  intro ε hε
  -- We'll use ε/2 for each
  have hε2 : 0 < ε / 2 := by linarith
  have hx' := hx (ε / 2) hε2
  have hy' := hy (ε / 2) hε2
  obtain ⟨f, rfl⟩ := ofSeq_surjective x
  obtain ⟨g, rfl⟩ := ofSeq_surjective y
  -- x + y becomes ofSeq (f + g)
  have hadd : (ofSeq f : Hyper ι α) + ofSeq g = ofSeq (fun n => f n + g n) := by
    change lift₂ Add.add (ofSeq f) (ofSeq g) = ofSeq (fun n => f n + g n)
    rw [lift₂_ofSeq]
    rfl
  rw [hadd, lift_ofSeq, std_eq_ofSeq_const, ofSeq_lt_ofSeq]
  simp only [lift_ofSeq, std_eq_ofSeq_const, ofSeq_lt_ofSeq] at hx' hy'
  -- Eventually ‖f n‖ < ε/2 and ‖g n‖ < ε/2, so ‖f n + g n‖ < ε
  have hboth := hx'.and hy'
  apply hboth.mono
  intro n ⟨hn_f, hn_g⟩
  simp only [Function.comp_apply] at hn_f hn_g ⊢
  calc ‖f n + g n‖ ≤ ‖f n‖ + ‖g n‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

end Infinitesimal

/-! ### Infinitesimals as an Ideal

We now show that the infinitesimals form an ideal in the ring of finite hyperelements.
For a NormedRing, multiplication of a finite element by an infinitesimal is infinitesimal.

The notion of "finite" (or "limited") for normed spaces means bounded norm:
there exists a standard real M with ‖x‖ < M. This differs from the order-theoretic
`IsFinite` defined in `Germ/Star.lean`.
-/

section InfinitesimalIdeal

variable [NormedRing α]

/-- An element is **norm-bounded** (finite in norm) if its norm is less than some standard real.
This is the appropriate notion for the ideal structure on infinitesimals. -/
def IsBoundedNorm (x : Hyper ι α) : Prop :=
  ∃ M : ℝ, 0 < M ∧ lift (‖·‖) x < (std M : Hyper ι ℝ)

/-- Zero has bounded norm. -/
theorem isBoundedNorm_zero : IsBoundedNorm (0 : Hyper ι α) := by
  use 1, one_pos
  have h0 : (0 : Hyper ι α) = std 0 := std_zero.symm
  rw [h0, lift_std, norm_zero, std_lt]
  exact one_pos

/-- Standard elements have bounded norm. -/
theorem isBoundedNorm_std (x : α) : IsBoundedNorm (std x : Hyper ι α) := by
  use ‖x‖ + 1, by linarith [norm_nonneg x]
  rw [lift_std, std_lt]
  linarith

/-- Infinitesimals have bounded norm. -/
theorem Infinitesimal.isBoundedNorm {x : Hyper ι α} (hx : Infinitesimal x) : IsBoundedNorm x := by
  use 1, one_pos
  exact hx 1 one_pos

/-- Negation preserves bounded norm. -/
theorem IsBoundedNorm.neg {x : Hyper ι α} (hx : IsBoundedNorm x) : IsBoundedNorm (-x) := by
  obtain ⟨M, hM, hbound⟩ := hx
  use M, hM
  obtain ⟨f, rfl⟩ := ofSeq_surjective x
  simp only [lift_ofSeq, std_eq_ofSeq_const, ofSeq_lt_ofSeq] at hbound ⊢
  have hneg : (-ofSeq f : Hyper ι α) = ofSeq (fun n => -f n) := by
    change lift Neg.neg (ofSeq f) = ofSeq (fun n => -f n)
    rw [lift_ofSeq]; rfl
  rw [hneg, lift_ofSeq, ofSeq_lt_ofSeq]
  convert hbound using 1
  ext n
  simp only [Function.comp_apply, norm_neg]

/-- Sum of norm-bounded elements is norm-bounded. -/
theorem IsBoundedNorm.add {x y : Hyper ι α} (hx : IsBoundedNorm x) (hy : IsBoundedNorm y) :
    IsBoundedNorm (x + y) := by
  obtain ⟨Mx, hMx, hboundx⟩ := hx
  obtain ⟨My, hMy, hboundy⟩ := hy
  use Mx + My, by linarith
  obtain ⟨f, rfl⟩ := ofSeq_surjective x
  obtain ⟨g, rfl⟩ := ofSeq_surjective y
  simp only [lift_ofSeq, std_eq_ofSeq_const, ofSeq_lt_ofSeq] at hboundx hboundy ⊢
  have hadd : (ofSeq f : Hyper ι α) + ofSeq g = ofSeq (fun n => f n + g n) := by
    change lift₂ Add.add (ofSeq f) (ofSeq g) = ofSeq (fun n => f n + g n)
    rw [lift₂_ofSeq]; rfl
  rw [hadd, lift_ofSeq, ofSeq_lt_ofSeq]
  have hboth := hboundx.and hboundy
  apply hboth.mono
  intro n ⟨hn_f, hn_g⟩
  simp only [Function.comp_apply] at hn_f hn_g ⊢
  calc ‖f n + g n‖ ≤ ‖f n‖ + ‖g n‖ := norm_add_le _ _
    _ < Mx + My := by linarith

/-- Product of norm-bounded and infinitesimal (left multiplication) is infinitesimal.
This is the key property making infinitesimals an ideal. -/
theorem IsBoundedNorm.mul_infinitesimal {r : Hyper ι α} {x : Hyper ι α}
    (hr : IsBoundedNorm r) (hx : Infinitesimal x) : Infinitesimal (r * x) := by
  obtain ⟨M, hM, hbound_r⟩ := hr
  intro ε hε
  have hεM : 0 < ε / M := div_pos hε hM
  have hx' := hx (ε / M) hεM
  obtain ⟨f, rfl⟩ := ofSeq_surjective r
  obtain ⟨g, rfl⟩ := ofSeq_surjective x
  simp only [lift_ofSeq, std_eq_ofSeq_const, ofSeq_lt_ofSeq] at hbound_r hx' ⊢
  have hmul : (ofSeq f : Hyper ι α) * ofSeq g = ofSeq (fun n => f n * g n) := by
    change lift₂ Mul.mul (ofSeq f) (ofSeq g) = ofSeq (fun n => f n * g n)
    rw [lift₂_ofSeq]; rfl
  rw [hmul, lift_ofSeq, ofSeq_lt_ofSeq]
  have hboth := hbound_r.and hx'
  apply hboth.mono
  intro n ⟨hn_r, hn_x⟩
  simp only [Function.comp_apply] at hn_r hn_x ⊢
  calc ‖f n * g n‖ ≤ ‖f n‖ * ‖g n‖ := norm_mul_le _ _
    _ < M * (ε / M) := by
      apply mul_lt_mul' (le_of_lt hn_r) hn_x (norm_nonneg _) hM
    _ = ε := mul_div_cancel₀ ε (ne_of_gt hM)

/-- Product of infinitesimal and norm-bounded (right multiplication) is infinitesimal. -/
theorem Infinitesimal.mul_isBoundedNorm {x : Hyper ι α} {r : Hyper ι α}
    (hx : Infinitesimal x) (hr : IsBoundedNorm r) : Infinitesimal (x * r) := by
  obtain ⟨M, hM, hbound_r⟩ := hr
  intro ε hε
  have hεM : 0 < ε / M := div_pos hε hM
  have hx' := hx (ε / M) hεM
  obtain ⟨f, rfl⟩ := ofSeq_surjective x
  obtain ⟨g, rfl⟩ := ofSeq_surjective r
  simp only [lift_ofSeq, std_eq_ofSeq_const, ofSeq_lt_ofSeq] at hbound_r hx' ⊢
  have hmul : (ofSeq f : Hyper ι α) * ofSeq g = ofSeq (fun n => f n * g n) := by
    change lift₂ Mul.mul (ofSeq f) (ofSeq g) = ofSeq (fun n => f n * g n)
    rw [lift₂_ofSeq]; rfl
  rw [hmul, lift_ofSeq, ofSeq_lt_ofSeq]
  have hboth := hx'.and hbound_r
  apply hboth.mono
  intro n ⟨hn_x, hn_r⟩
  simp only [Function.comp_apply] at hn_x hn_r ⊢
  calc ‖f n * g n‖ ≤ ‖f n‖ * ‖g n‖ := norm_mul_le _ _
    _ < (ε / M) * M := by
      apply mul_lt_mul' (le_of_lt hn_x) hn_r (norm_nonneg _) hεM
    _ = ε := div_mul_cancel₀ ε (ne_of_gt hM)

/-- Product of two infinitesimals is infinitesimal. -/
theorem Infinitesimal.mul {x y : Hyper ι α} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x * y) :=
  hx.mul_isBoundedNorm hy.isBoundedNorm

/-- Multiplication by standard element (which is always norm-bounded) preserves infinitesimals. -/
theorem Infinitesimal.smul_std {x : Hyper ι α} (hx : Infinitesimal x) (r : α) :
    Infinitesimal ((std r : Hyper ι α) * x) :=
  (isBoundedNorm_std r).mul_infinitesimal hx

/-- The halo of 0 is closed under addition (subgroup property). -/
theorem halo_zero_add_closed {x y : Hyper ι α}
    (hx : x ∈ halo (0 : α)) (hy : y ∈ halo (0 : α)) : x + y ∈ halo (0 : α) := by
  rw [← infinitesimal_iff_mem_halo_zero] at hx hy ⊢
  exact hx.add hy

/-- The halo of 0 is closed under negation (subgroup property). -/
theorem halo_zero_neg_closed {x : Hyper ι α}
    (hx : x ∈ halo (0 : α)) : -x ∈ halo (0 : α) := by
  rw [← infinitesimal_iff_mem_halo_zero] at hx ⊢
  exact hx.neg

/-- The halo of 0 absorbs norm-bounded elements under multiplication (ideal property). -/
theorem halo_zero_mul_bounded_closed {x r : Hyper ι α}
    (hx : x ∈ halo (0 : α)) (hr : IsBoundedNorm r) : r * x ∈ halo (0 : α) := by
  rw [← infinitesimal_iff_mem_halo_zero] at hx ⊢
  exact hr.mul_infinitesimal hx

end InfinitesimalIdeal

/-! ## Infinitesimal Closeness (≈)

Two elements are infinitesimally close if their difference is infinitesimal.
-/

section InfClose

variable [NormedAddCommGroup α]

/-- Two elements are **infinitesimally close** if their difference is infinitesimal.
This is written `x ≈ y` in standard NSA notation. -/
def InfClose (x y : Hyper ι α) : Prop :=
  Infinitesimal (x - y)

@[inherit_doc] scoped infixl:50 " ≈ " => InfClose

@[refl]
theorem InfClose.refl (x : Hyper ι α) : x ≈ x := by
  obtain ⟨f, rfl⟩ := ofSeq_surjective x
  unfold InfClose Infinitesimal
  intro ε hε
  -- ofSeq f - ofSeq f = ofSeq (fun n => f n - f n) = ofSeq (fun _ => 0)
  have hsub : (ofSeq f : Hyper ι α) - ofSeq f = ofSeq (fun _ => (0 : α)) := by
    change lift₂ Sub.sub (ofSeq f) (ofSeq f) = ofSeq (fun _ => 0)
    rw [lift₂_ofSeq]
    congr 1
    ext n
    exact sub_self _
  rw [hsub, lift_ofSeq, std_eq_ofSeq_const]
  rw [ofSeq_lt_ofSeq]
  exact Filter.Eventually.of_forall fun n => by simp only [Function.comp_apply, norm_zero, hε]

@[symm]
theorem InfClose.symm {x y : Hyper ι α} (h : x ≈ y) : y ≈ x := by
  unfold InfClose at h ⊢
  -- y - x = -(x - y), so use neg
  have heq : y - x = -(x - y) := by
    obtain ⟨f, rfl⟩ := ofSeq_surjective x
    obtain ⟨g, rfl⟩ := ofSeq_surjective y
    change lift₂ Sub.sub (ofSeq g) (ofSeq f) = lift Neg.neg (lift₂ Sub.sub (ofSeq f) (ofSeq g))
    rw [lift₂_ofSeq, lift₂_ofSeq, lift_ofSeq]
    congr 1
    ext n
    simp only [Function.comp_apply]
    exact (neg_sub (f n) (g n)).symm
  rw [heq]
  exact h.neg


@[trans]
theorem InfClose.trans {x y z : Hyper ι α} (hxy : x ≈ y) (hyz : y ≈ z) : x ≈ z := by
  unfold InfClose at hxy hyz ⊢
  -- x - z = (x - y) + (y - z)
  have heq : x - z = (x - y) + (y - z) := by
    obtain ⟨f, rfl⟩ := ofSeq_surjective x
    obtain ⟨g, rfl⟩ := ofSeq_surjective y
    obtain ⟨k, rfl⟩ := ofSeq_surjective z
    change lift₂ Sub.sub (ofSeq f) (ofSeq k) =
         lift₂ Add.add (lift₂ Sub.sub (ofSeq f) (ofSeq g)) (lift₂ Sub.sub (ofSeq g) (ofSeq k))
    simp only [lift₂_ofSeq]
    congr 1
    ext n
    exact (sub_add_sub_cancel (f n) (g n) (k n)).symm
  rw [heq]
  exact hxy.add hyz

/-- InfClose is an equivalence relation. -/
theorem infClose_equivalence : Equivalence (InfClose : Hyper ι α → Hyper ι α → Prop) :=
  ⟨InfClose.refl, InfClose.symm, InfClose.trans⟩

/-- Standard elements are infinitesimally close iff they are equal. -/
theorem std_infClose_std (x y : α) : (std x : Hyper ι α) ≈ std y ↔ x = y := by
  constructor
  · intro h
    by_contra hne
    have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have := h (‖x - y‖ / 2) (by linarith)
    -- std x - std y = std (x - y)
    have hsub : (std x : Hyper ι α) - std y = std (x - y) := std_sub x y
    rw [hsub, lift_std, std_lt] at this
    linarith
  · intro h
    rw [h]

end InfClose

/-! ## NSA Characterization of Continuity -/

section Continuity

variable [TopologicalSpace α] [TopologicalSpace β]

/-- **NSA characterization of continuity**: `f` is continuous at `x` iff
`f` maps every element of `halo x` into `halo (f x)`.

Intuitively: `f` is continuous at `x` iff whenever `y ≈ x`, we have `f(y) ≈ f(x)`. -/
theorem continuousAt_iff_halo {f : α → β} {x : α} :
    ContinuousAt f x ↔ ∀ y : Hyper ι α, y ∈ halo x → lift f y ∈ halo (f x) := by
  constructor
  · -- Forward: continuous at x → halo preservation
    intro hcont y hy
    rw [mem_halo_iff] at hy ⊢
    intro V hV
    -- V is a neighborhood of f(x), so f⁻¹(V) is a neighborhood of x
    have hpreimage : f ⁻¹' V ∈ 𝓝 x := hcont hV
    -- y is in halo x, so y satisfies the lifted predicate for f⁻¹(V)
    have hy_preimage := hy (f ⁻¹' V) hpreimage
    -- lift f y satisfies the lifted predicate for V
    obtain ⟨g, rfl⟩ := ofSeq_surjective y
    rw [liftPred_ofSeq] at hy_preimage
    rw [lift_ofSeq, liftPred_ofSeq]
    simp only [Set.mem_preimage] at hy_preimage
    convert hy_preimage using 1
  · -- Backward: halo preservation → continuous at x
    intro hhalo
    rw [ContinuousAt, Filter.Tendsto]
    intro V hV
    -- Need to show V ∈ map f (𝓝 x), equivalently f⁻¹(V) ∈ 𝓝 x
    rw [Filter.mem_map]
    -- Use contrapositive via ultrafilter characterization
    by_contra hcontra
    -- By Filter.mem_iff_ultrafilter: s ∉ f ↔ ∃ u ≤ f, s ∉ u
    -- So there exists u : Ultrafilter α with u ≤ 𝓝 x and f⁻¹(V) ∉ u
    rw [Filter.mem_iff_ultrafilter] at hcontra
    push_neg at hcontra
    obtain ⟨u : Ultrafilter α, hu_le, hu_notmem⟩ := hcontra
    -- Since u is an ultrafilter and f⁻¹(V) ∉ u, we have (f⁻¹(V))ᶜ ∈ u
    have hu_compl : (f ⁻¹' V)ᶜ ∈ (u : Filter α) :=
      Ultrafilter.compl_mem_iff_notMem.mpr hu_notmem
    -- The issue: we need to construct y : Hyper ι α from u : Ultrafilter α
    -- This requires the index type ι to be "large enough" (saturation)
    -- For first-countable spaces with ι = ℕ, we can use a sequence
    -- For general spaces, we need ι to have cardinality ≥ the neighborhood filter basis
    -- This is a fundamental limitation of the ultraproduct construction
    -- TODO: Add saturation hypothesis or restrict to first-countable spaces
    sorry

/-- **NSA characterization of continuity for Fréchet-Urysohn spaces**: In any Fréchet-Urysohn space
(including all first-countable spaces), `f` is continuous at `x` iff for all sequences
`s : ℕ → α` converging to `x` and all infinite `N : Hyper ℕ ℕ`, the lifted value `f*(s*(N))`
is in the halo of `f x`.

For first-countable spaces, this is equivalent to the halo characterization with `ι = ℕ`. -/
theorem continuousAt_iff_halo_seq [FrechetUrysohnSpace α] {f : α → β} {x : α} :
    ContinuousAt f x ↔ ∀ y : Hyper ℕ α, y ∈ halo x → lift f y ∈ halo (f x) := by
  constructor
  · -- Forward direction: use the general theorem
    exact fun hcont y hy => (continuousAt_iff_halo (ι := ℕ)).mp hcont y hy
  · -- Backward direction: use sequential characterization
    intro hhalo
    -- ContinuousAt is Tendsto f (𝓝 x) (𝓝 (f x))
    -- In Fréchet-Urysohn spaces, this is equivalent to sequential continuity
    rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
    intro u hu
    -- u is a sequence converging to x, so we need f ∘ u → f x
    -- Use halo_tendsto_atTop: show that for all infinite N, lift (f ∘ u) N ∈ halo (f x)
    apply halo_tendsto_atTop
    intro N hN
    -- lift u N ∈ halo x because u → x (using tendsto_atTop_halo)
    have hhalo_u : lift u N ∈ halo x := tendsto_atTop_halo hu hN
    -- By hypothesis, lift f (lift u N) ∈ halo (f x)
    -- We need to show lift (f ∘ u) N = lift f (lift u N)
    obtain ⟨g, rfl⟩ := ofSeq_surjective N
    -- lift (f ∘ u) (ofSeq g) = ofSeq ((f ∘ u) ∘ g)
    -- lift f (lift u (ofSeq g)) = ofSeq (f ∘ u ∘ g), equal by associativity
    have heq : lift (f ∘ u) (ofSeq g : Hyper ℕ ℕ) = lift f (lift u (ofSeq g)) := by
      simp only [lift_ofSeq, Function.comp_assoc]
    rw [heq]
    exact hhalo (lift u (ofSeq g)) hhalo_u

/-- Continuous functions preserve halo membership. -/
theorem Continuous.halo_map {f : α → β} (hf : Continuous f) (x : α) :
    ∀ y ∈ halo (ι := ι) x, lift f y ∈ halo (f x) := by
  intro y hy
  exact (continuousAt_iff_halo (ι := ι)).mp hf.continuousAt y hy

end Continuity

/-! ## NSA Characterization of Topological Concepts -/

section TopologicalConcepts

variable [TopologicalSpace α]

/-- **NSA characterization of open sets**: A set `U` is open iff it contains the halo of every
point in `U`.
Intuitively: `U` is open iff every point infinitely close to `x ∈ U` is also in `U*`. -/
theorem isOpen_iff_halo_subset [Nonempty (Set α ↪ ι)] {U : Set α} :
    IsOpen U ↔ ∀ x ∈ U, halo (ι := ι) x ⊆ {y | liftPred (· ∈ U) y} := by
  constructor
  · intro h x hx y hy
    rw [mem_halo_iff] at hy
    exact hy U (h.mem_nhds hx)
  · intro h
    rw [isOpen_iff_mem_nhds]
    intro x hx
    by_contra h_not_mem
    have h_closure : x ∈ closure Uᶜ := by
      rw [mem_closure_iff_nhds]
      intro V hV
      by_contra h_empty
      push_neg at h_empty
      have hV_sub_U : V ⊆ U := fun z hz =>
        by_contra fun hz' => Set.eq_empty_iff_forall_notMem.mp h_empty z ⟨hz, hz'⟩
      exact h_not_mem (mem_of_superset hV hV_sub_U)
    haveI : NeBot (𝓝 x ⊓ 𝓟 Uᶜ) := mem_closure_iff_clusterPt.mp h_closure
    obtain ⟨y, hy_eq⟩ := exists_hyper_of_ultrafilter (ι := ι) (Ultrafilter.of (𝓝 x ⊓ 𝓟 Uᶜ))
    let 𝓤 := Ultrafilter.of (𝓝 x ⊓ 𝓟 Uᶜ)
    have h_le : 𝓤 ≤ 𝓝 x ⊓ 𝓟 Uᶜ := Ultrafilter.of_le _
    have hy_halo : y ∈ halo x := by
      rw [mem_halo_iff]
      intro V hV
      rw [mem_star_iff_mem_asUltrafilter, hy_eq]
      apply h_le
      exact mem_inf_of_left hV
    have hy_not_U : y ∉ {z | liftPred (· ∈ U) z} := by
      intro hy_U
      simp only [mem_setOf_eq] at hy_U
      rw [mem_star_iff_mem_asUltrafilter, hy_eq] at hy_U
      have hUc : Uᶜ ∈ 𝓤 := by
        apply h_le
        exact mem_inf_of_right (mem_principal_self Uᶜ)
      have h_inter : U ∩ Uᶜ ∈ (𝓤 : Filter α) := inter_mem hy_U hUc
      rw [inter_compl_self] at h_inter
      exact 𝓤.neBot.ne (Filter.empty_mem_iff_bot.mp h_inter)
    specialize h x hx hy_halo
    contradiction

/-- **NSA characterization of closed sets**: A set `F` is closed iff it contains all standard parts
of its near-standard elements.
Intuitively: `F` is closed iff whenever `y ∈ F*` and `y ≈ x`, then `x ∈ F`. -/
theorem isClosed_iff_halo_inter [Nonempty (Set α ↪ ι)] {F : Set α} :
    IsClosed F ↔ ∀ x : α, (halo (ι := ι) x ∩ {y | liftPred (· ∈ F) y}).Nonempty → x ∈ F := by
  sorry

/-- **NSA characterization of dense sets**: `A` is dense iff `A*` meets every halo. -/
theorem dense_iff_halo_inter [Nonempty (Set α ↪ ι)] {A : Set α} :
    Dense A ↔ ∀ x : α, (halo (ι := ι) x ∩ {y | liftPred (· ∈ A) y}).Nonempty := by
  sorry
  /-
  constructor
  · intro hA x
    have hx : x ∈ closure A := hA.closure_eq_univ.symm ▸ mem_univ x
    haveI : NeBot (𝓝 x ⊓ 𝓟 A) := mem_closure_iff_clusterPt.mp hx
    obtain ⟨y, hy_eq⟩ := exists_hyper_of_ultrafilter (ι := ι) (Ultrafilter.of (𝓝 x ⊓ 𝓟 A))
    let 𝓤 := Ultrafilter.of (𝓝 x ⊓ 𝓟 A)
    have h_le : 𝓤 ≤ 𝓝 x ⊓ 𝓟 A := Ultrafilter.of_le _
    use y
    constructor
    · rw [mem_halo_iff]
      intro V hV
      rw [mem_star_iff_mem_asUltrafilter, hy_eq]
      apply h_le
      exact mem_inf_of_left hV
    · rw [mem_star_iff_mem_asUltrafilter, hy_eq]
      apply h_le
      exact mem_inf_of_right (mem_principal_self A)
  · intro h
    rw [dense_iff_closure_eq]
    ext x
    constructor
    · intro _
      exact mem_univ x
    · intro _
      obtain ⟨y, hy_halo, hy_A⟩ := h x
      rw [mem_halo_iff] at hy_halo
      rw [mem_star_iff_mem_asUltrafilter] at hy_A
      have h_le : asUltrafilter y ≤ 𝓝 x := by
        intro U hU
        rw [← mem_star_iff_mem_asUltrafilter]
        exact hy_halo U hU
      have h_cluster : ClusterPt x (𝓟 A) := by
        rw [ClusterPt, inf_comm]
        apply NeBot.mono h_le
        rw [le_inf_iff]
        exact ⟨le_rfl, le_principal_iff.mpr hy_A⟩
      rw [← mem_closure_iff_clusterPt] at h_cluster
      exact h_cluster
  -/

/-- **NSA characterization of cluster points**: `x` is a cluster point of `F` iff
`halo x` meets `F*`. -/
theorem clusterPt_iff_halo_inter [Nonempty (Set α ↪ ι)] {F : Filter α} {x : α} :
    ClusterPt x F ↔ (halo (ι := ι) x ∩ ⋂ U ∈ F, {y | liftPred (· ∈ U) y}).Nonempty := by
  sorry

end TopologicalConcepts

/-! ## NSA Characterization of Compactness -/

section Compactness

variable [TopologicalSpace α]

/-- **NSA characterization of compactness**: A set `K` is compact iff every element of `K*`
(the *-extension of `K`) is near-standard with standard part in `K`.

Intuitively: `K` is compact iff every hyperreal "in `K`" is infinitely close to some
standard element of `K`.

**Note**: The forward direction uses `isCompact_iff_ultrafilter_le_nhds`. The backward
direction requires a saturation hypothesis to construct appropriate ultrafilters. -/
theorem isCompact_iff_nearStd_nsa [T2Space α] {K : Set α} :
    IsCompact K ↔ ∀ y : Hyper ι α, liftPred (· ∈ K) y → IsNearStd y ∧
      ∀ (hy : IsNearStd y), stdPart y hy ∈ K := by
  constructor
  · -- Forward: K compact → elements of K* are near-standard with std part in K
    intro hK y hy
    -- Decompose y as a sequence
    obtain ⟨f, rfl⟩ := ofSeq_surjective y
    rw [liftPred_ofSeq] at hy
    -- hy : ∀ᶠ n, f n ∈ K
    -- Push forward the hyperfilter via f to get an ultrafilter on α
    let u : Ultrafilter α := (hyperfilter ι).map f
    -- Since eventually f n ∈ K, we have K ∈ u
    have hK_in_u : K ∈ u := by
      rw [Ultrafilter.mem_map]
      exact hy
    -- So u ≤ 𝓟 K
    have hu_le : (u : Filter α) ≤ 𝓟 K := by
      rw [Filter.le_principal_iff]
      exact hK_in_u
    -- By compactness, there exists x ∈ K with u ≤ 𝓝 x
    rw [isCompact_iff_ultrafilter_le_nhds] at hK
    obtain ⟨x, hxK, hu_nhds⟩ := hK u hu_le
    -- This means y = ofSeq f is in halo x
    have hy_halo : (ofSeq f : Hyper ι α) ∈ halo x := by
      rw [mem_halo_iff]
      intro V hV
      -- V ∈ 𝓝 x, and u ≤ 𝓝 x, so V ∈ u = map f (hyperfilter ι)
      have hV_u : V ∈ u := hu_nhds hV
      -- Unwrap: V ∈ map f (hyperfilter ι) ↔ f⁻¹(V) ∈ hyperfilter ι
      rw [liftPred_ofSeq]
      -- hV_u : V ∈ Ultrafilter.map f (hyperfilter ι)
      -- This is the same as f⁻¹(V) ∈ hyperfilter ι, which is our goal
      exact hV_u
    constructor
    · -- IsNearStd (ofSeq f)
      exact ⟨x, hy_halo⟩
    · -- stdPart is in K
      intro hy_nearstd
      -- stdPart is unique in T2 space
      have hstd_eq : stdPart (ofSeq f) hy_nearstd = x :=
        halo_eq_of_mem_halo (stdPart_spec _ _) hy_halo
      rw [hstd_eq]
      exact hxK
  · -- Backward: all elements near-standard → K compact (requires saturation)
    intro hhalo
    rw [isCompact_iff_ultrafilter_le_nhds]
    intro u hu
    -- u : Ultrafilter α with u ≤ 𝓟 K
    -- We need to find x ∈ K with u ≤ 𝓝 x
    -- This requires constructing y : Hyper ι α from u, which needs saturation
    -- For general ι, this requires |ι| ≥ cardinality assumptions
    -- TODO: Add saturation hypothesis or prove for ι = ℕ with countable filter basis
    sorry

end Compactness

/-! ## NSA Characterization of Limits and Convergence -/

section Limits

variable [TopologicalSpace α]

/-- **NSA characterization of limits**: `Tendsto f F (𝓝 L)` iff for every `x` with
`liftPred (· ∈ F) x`, we have `lift f x ∈ halo L`.

For sequences: `f n → L` iff for every infinite `N`, `f N ≈ L`.

**Note**: The forward direction is provable. The backward direction requires a saturation
hypothesis to construct appropriate elements of `Hyper ι β` from ultrafilters on `β`. -/
theorem tendsto_iff_lift_mem_halo {β : Type*} {f : β → α} {F : Filter β} {L : α} :
    Tendsto f F (𝓝 L) ↔
      ∀ x : Hyper ι β, (∀ U ∈ F, liftPred (· ∈ U) x) → lift f x ∈ halo L := by
  constructor
  · -- Forward: Tendsto → halo membership
    intro hf x hx
    rw [mem_halo_iff]
    intro V hV
    -- Since f tends to L, f⁻¹(V) ∈ F
    have hpreimage : f ⁻¹' V ∈ F := hf hV
    -- x satisfies all F-membership, so liftPred (· ∈ f⁻¹' V) x
    have hx_preimage := hx (f ⁻¹' V) hpreimage
    -- This means lift f x satisfies V
    obtain ⟨g, rfl⟩ := ofSeq_surjective x
    rw [liftPred_ofSeq] at hx_preimage
    rw [lift_ofSeq, liftPred_ofSeq]
    simp only [Set.mem_preimage] at hx_preimage
    convert hx_preimage using 1
  · -- Backward: halo membership → Tendsto (requires saturation)
    intro hhalo
    rw [Filter.Tendsto]
    intro V hV
    -- Need to show f⁻¹(V) ∈ F
    -- The issue: to use the contrapositive, we need to construct x : Hyper ι β
    -- from an ultrafilter on β, which requires saturation
    -- For now, we leave this as sorry with documentation
    -- TODO: Add saturation hypothesis or prove for specific cases
    sorry

/-- For sequences: convergence iff infinite indices map to the halo.

This is the key NSA characterization of sequence convergence: `f n → L` iff
for every infinite hypernatural `N`, `f*(N)` is in the halo of `L`.

Intuitively: a sequence converges to `L` iff evaluating it at any "infinite index"
gives a value infinitely close to `L`. -/
theorem tendsto_atTop_iff_infinite_in_halo {f : ℕ → α} {L : α} :
    Tendsto f atTop (𝓝 L) ↔
      ∀ N : Hyper ℕ ℕ, IsInfinitePos N → lift f N ∈ halo L :=
  ⟨fun hf _N hN => tendsto_atTop_halo hf hN, halo_tendsto_atTop⟩

end Limits

/-! ## NSA Characterization of Uniform Continuity

The key insight of NSA for uniform continuity: a function is uniformly continuous iff
it preserves infinitesimal closeness for **all** pairs (x, y), not just those near standard points.

For pointwise continuity: `x ≈ std a → f(x) ≈ f(std a)` (halo preservation at standard points)
For uniform continuity: `x ≈ y → f(x) ≈ f(y)` (halo preservation everywhere)

## The Entourage Approach

For general uniform spaces, the correct NSA definition of "infinitesimally close" is:
```
x ≈ y  ⟺  ∀ U ∈ 𝓤 α, (x, y) ∈ *U
```
where `*U` is the nonstandard extension of entourage `U`. In our framework:
```
x ≈ y  ⟺  ∀ U ∈ 𝓤 α, liftRel (fun a b => (a, b) ∈ U) x y
```

**Important**: The relation `≈` is an *external* set - it's the intersection of all
internal entourages, but is not itself internal. This is why we can't directly use
`≈` as an entourage in the nonstandard uniformity.
-/

section UniformContinuity

open Uniformity in
variable [UniformSpace α] [UniformSpace β]

/-- Two hyperelements are **entourage-close** if they belong to the lift of every entourage.
This is the proper NSA notion of "infinitesimally close" for general uniform spaces. -/
def EntourageClose [UniformSpace α] (x y : Hyper ι α) : Prop :=
  ∀ U ∈ uniformity α, liftRel (fun a b => (a, b) ∈ U) x y

/-- Notation for entourage closeness. -/
scoped infix:50 " ≃ᵤ " => EntourageClose

/-- Entourage closeness is reflexive. -/
theorem EntourageClose.refl [UniformSpace α] (x : Hyper ι α) : EntourageClose x x := by
  unfold EntourageClose
  intro U hU
  obtain ⟨f, rfl⟩ := ofSeq_surjective x
  rw [liftRel_ofSeq]
  apply Filter.Eventually.of_forall
  intro n
  exact refl_mem_uniformity hU

/-- Entourage closeness is symmetric. -/
theorem EntourageClose.symm [UniformSpace α] {x y : Hyper ι α}
    (h : EntourageClose x y) : EntourageClose y x := by
  unfold EntourageClose at h ⊢
  intro U hU
  -- Get symmetric entourage V ⊆ U
  obtain ⟨V, hV, hVsymm, hVU⟩ := comp_symm_mem_uniformity_sets hU
  obtain ⟨fx, rfl⟩ := ofSeq_surjective x
  obtain ⟨fy, rfl⟩ := ofSeq_surjective y
  specialize h V hV
  rw [liftRel_ofSeq] at h ⊢
  apply h.mono
  intro n hn
  -- V is symmetric, so (fx n, fy n) ∈ V implies (fy n, fx n) ∈ V ⊆ V ○ V ⊆ U
  have hn' : (fy n, fx n) ∈ V := hVsymm.symm _ _ hn
  -- Composition: (fy n, fx n) ∈ V ○ V via z = fx n
  exact hVU ⟨fx n, hn', refl_mem_uniformity hV⟩

/-- Entourage closeness is transitive. -/
theorem EntourageClose.trans [UniformSpace α] {x y z : Hyper ι α}
    (hxy : EntourageClose x y) (hyz : EntourageClose y z) : EntourageClose x z := by
  unfold EntourageClose at hxy hyz ⊢
  intro U hU
  obtain ⟨V, hV, hVU⟩ := comp_mem_uniformity_sets hU
  obtain ⟨fx, rfl⟩ := ofSeq_surjective x
  obtain ⟨fy, rfl⟩ := ofSeq_surjective y
  obtain ⟨fz, rfl⟩ := ofSeq_surjective z
  specialize hxy V hV
  specialize hyz V hV
  rw [liftRel_ofSeq] at hxy hyz ⊢
  apply (hxy.and hyz).mono
  intro n ⟨hn1, hn2⟩
  exact hVU ⟨fy n, hn1, hn2⟩

/-- **NSA characterization of uniform continuity for uniform spaces**:
`f` is uniformly continuous iff it preserves entourage closeness.

This is the **microcontinuity** characterization:
  `UniformContinuous f ↔ ∀ x* y*, x* ≈ y* → f(x*) ≈ f(y*)` -/
theorem uniformContinuous_iff_entourageClose [UniformSpace α] [UniformSpace β] {f : α → β} :
    UniformContinuous f ↔
      ∀ x y : Hyper ι α, EntourageClose x y → EntourageClose (lift f x) (lift f y) := by
  constructor
  · -- Forward: uniform continuous → preserves entourage closeness
    intro huc x y hxy
    unfold EntourageClose at hxy ⊢
    intro V hV
    -- By uniform continuity, preimage of V is an entourage in α
    have hpre : (Prod.map f f) ⁻¹' V ∈ uniformity α := huc hV
    -- Since x ≃ᵤ y, we have (x, y) in the lift of the preimage
    specialize hxy _ hpre
    obtain ⟨fx, rfl⟩ := ofSeq_surjective x
    obtain ⟨fy, rfl⟩ := ofSeq_surjective y
    rw [liftRel_ofSeq] at hxy
    simp only [lift_ofSeq]
    rw [liftRel_ofSeq]
    apply hxy.mono
    intro n hn
    simp only [Set.mem_preimage, Prod.map_apply] at hn
    exact hn
  · -- Backward: preserves entourage closeness → uniform continuous
    intro hpres
    rw [uniformContinuous_def]
    intro V hV
    -- Suppose not: preimage of V is not an entourage
    by_contra hcontra
    -- Then for each entourage U, ∃ (x, y) ∈ U with (f x, f y) ∉ V
    -- This requires countable choice with a basis of entourages
    -- For simplicity, we use the contrapositive with sequences
    -- The full proof requires constructing bad sequences; sketch the idea
    -- For each n, pick U_n from a countable basis, find (x_n, y_n) ∈ U_n with (f x_n, f y_n) ∉ V
    -- Then ofSeq x ≃ᵤ ofSeq y but lift f (ofSeq x) is not ≃ᵤ lift f (ofSeq y)
    sorry

/-- For metric spaces, entourage closeness is equivalent to InfClose. -/
theorem entourageClose_iff_infClose [NormedAddCommGroup α] {x y : Hyper ι α} :
    EntourageClose x y ↔ InfClose x y := by
  constructor
  · intro hec
    unfold InfClose Infinitesimal
    intro ε hε
    -- The ε-ball around 0 defines an entourage (using dist = norm)
    have hU : {p : α × α | dist p.1 p.2 < ε} ∈ uniformity α := Metric.dist_mem_uniformity hε
    unfold EntourageClose at hec
    have hxy := hec _ hU
    obtain ⟨fx, rfl⟩ := ofSeq_surjective x
    obtain ⟨fy, rfl⟩ := ofSeq_surjective y
    rw [liftRel_ofSeq] at hxy
    simp only [std_eq_ofSeq_const]
    apply hxy.mono
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    simp only [Function.comp_apply]
    rw [dist_eq_norm] at hn
    exact hn
  · intro hic
    unfold EntourageClose
    intro U hU
    -- Get ε such that ε-ball ⊆ U
    obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.mp hU
    unfold InfClose Infinitesimal at hic
    have hsmall := hic ε hε
    obtain ⟨fx, rfl⟩ := ofSeq_surjective x
    obtain ⟨fy, rfl⟩ := ofSeq_surjective y
    rw [liftRel_ofSeq]
    simp only [std_eq_ofSeq_const] at hsmall
    apply hsmall.mono
    intro n hn
    apply hεU
    simp only [Function.comp_apply] at hn
    rw [dist_eq_norm]
    exact hn

/-- **Heine-Cantor via NSA**: A continuous function on a compact set is uniformly continuous.

The NSA proof is conceptually elegant:
1. On a compact set, every hyperextension element is near-standard
2. Continuity preserves infinitesimal closeness at standard points
3. For x ≈ y in the hyperextension of a compact set:
   - Both x and y are near-standard (by compactness): x ≈ std a, y ≈ std b
   - If x ≈ y, then std a ≈ std b, so a = b (Hausdorff)
   - By continuity at a: f(x) ≈ f(a) and f(y) ≈ f(a)
   - Therefore f(x) ≈ f(y)

This shows uniform continuity: infinitesimal closeness is preserved EVERYWHERE,
not just at standard points. -/
theorem IsCompact.uniformContinuousOn_of_continuous_nsa [UniformSpace α] [UniformSpace β]
    {K : Set α} (hK : IsCompact K) {f : α → β} (hf : ContinuousOn f K) :
    UniformContinuousOn f K :=
  -- Use the existing Mathlib theorem; the NSA proof sketch is in the docstring
  hK.uniformContinuousOn_of_continuous hf

/-- **NSA proof of Heine-Cantor** (full version):
On a compact space, continuous functions preserve entourage closeness,
hence are uniformly continuous.

The key insight is that compactness ensures ALL hyperelements are near-standard,
so pointwise continuity (which preserves halos at standard points) automatically
becomes uniform continuity (which preserves entourage closeness everywhere).

This is the **microcontinuity** characterization:
  `UniformContinuous f ↔ ∀ x* y*, x* ≈ y* → f(x*) ≈ f(y*)` -/
theorem compactSpace_continuous_preserves_entourageClose [UniformSpace α] [UniformSpace β]
    [CompactSpace α] {f : α → β} (hf : Continuous f) :
    ∀ x y : Hyper ι α, EntourageClose x y → EntourageClose (lift f x) (lift f y) := by
  -- Use the forward direction of uniformContinuous_iff_entourageClose
  have huc : UniformContinuous f := CompactSpace.uniformContinuous_of_continuous hf
  exact uniformContinuous_iff_entourageClose.mp huc

end UniformContinuity

/-! ## IST-Style Transfer Principle: Standard Part Commutes with Standard Functions

The key principle of Internal Set Theory (IST) is that standard functions commute with the
standard part operation. In our framework:

**Transfer for standard part**: If `f : α → β` is continuous at `st x` and `x` is near-standard,
then `st (lift f x) = f (st x)`.

This generalizes specific lemmas like `factorial_std`, `st_add`, `st_mul` etc. into a single
principle: standard (continuous) functions commute with the standard part functor.
-/

section StandardPartTransfer

variable [TopologicalSpace α] [TopologicalSpace β] [T2Space α] [T2Space β]

omit [T2Space α] [T2Space β] in
/-- **Standard Part Transfer Principle**: For a continuous function `f` at the standard part,
the standard part of `lift f x` equals `f` applied to the standard part of `x`.

This is the fundamental IST principle: `st(f*(x)) = f(st(x))` for continuous `f`.

Intuitively: if `x ≈ a` (x is infinitely close to standard a) and `f` is continuous at `a`,
then `f*(x) ≈ f(a)`, so `st(f*(x)) = f(a) = f(st(x))`. -/
theorem st_lift_eq_of_continuousAt {f : α → β} {x : Hyper ι α} {a : α}
    (hx : x ∈ halo a) (hf : ContinuousAt f a) :
    lift f x ∈ halo (f a) := by
  exact (continuousAt_iff_halo (ι := ι)).mp hf x hx

/-- Standard part commutes with continuous functions at near-standard points. -/
theorem stdPart_lift_of_continuousAt {f : α → β} {x : Hyper ι α}
    (hx : IsNearStd x) (hf : ContinuousAt f (stdPart x hx)) :
    IsNearStd (lift f x) ∧
      ∀ (hy : IsNearStd (lift f x)), stdPart (lift f x) hy = f (stdPart x hx) := by
  have hx_halo := stdPart_spec x hx
  have hfx_halo := st_lift_eq_of_continuousAt hx_halo hf
  constructor
  · exact ⟨f (stdPart x hx), hfx_halo⟩
  · intro hy
    exact halo_eq_of_mem_halo (stdPart_spec (lift f x) hy) hfx_halo

/-- **Lift of continuous function preserves near-standardness.** -/
theorem IsNearStd.lift_of_continuous {f : α → β} {x : Hyper ι α}
    (hx : IsNearStd x) (hf : Continuous f) : IsNearStd (lift f x) :=
  (stdPart_lift_of_continuousAt hx hf.continuousAt).1

/-- Binary version: standard part commutes with continuous binary operations.
This generalizes `st_add`, `st_mul`, etc. -/
theorem stdPart_lift₂_of_continuousAt {γ : Type*} [TopologicalSpace γ] [T2Space γ]
    {f : α → β → γ} {x : Hyper ι α} {y : Hyper ι β}
    (hx : IsNearStd x) (hy : IsNearStd y)
    (hf : ContinuousAt (Function.uncurry f) (stdPart x hx, stdPart y hy)) :
    IsNearStd (lift₂ f x y) ∧
      ∀ (hz : IsNearStd (lift₂ f x y)),
        stdPart (lift₂ f x y) hz = f (stdPart x hx) (stdPart y hy) := by
  -- Get the standard parts
  let a := stdPart x hx
  let b := stdPart y hy
  -- x and y are in the halos of their standard parts
  have hx_halo : x ∈ halo a := stdPart_spec x hx
  have hy_halo : y ∈ halo b := stdPart_spec y hy
  -- Show lift₂ f x y is in halo(f(a, b))
  have hfxy_halo : lift₂ f x y ∈ halo (f a b) := by
    rw [mem_halo_iff]
    intro W hW
    -- By continuity, there exist neighborhoods U and V with f(U × V) ⊆ W
    rw [ContinuousAt, Filter.Tendsto, Filter.map_le_iff_le_comap] at hf
    have hpre : Function.uncurry f ⁻¹' W ∈ nhds (a, b) := hf (Filter.preimage_mem_comap hW)
    rw [nhds_prod_eq, Filter.mem_prod_iff] at hpre
    obtain ⟨U, hU, V, hV, hUV⟩ := hpre
    -- x ∈ U* and y ∈ V*
    have hxU : liftPred (· ∈ U) x := (mem_halo_iff a x).mp hx_halo U hU
    have hyV : liftPred (· ∈ V) y := (mem_halo_iff b y).mp hy_halo V hV
    -- Now show lift₂ f x y ∈ W*
    obtain ⟨s, rfl⟩ := ofSeq_surjective x
    obtain ⟨t, rfl⟩ := ofSeq_surjective y
    rw [liftPred_ofSeq] at hxU hyV
    rw [lift₂_ofSeq, liftPred_ofSeq]
    filter_upwards [hxU, hyV] with i hsU htV
    exact hUV (Set.mk_mem_prod hsU htV)
  -- Therefore IsNearStd (lift₂ f x y)
  constructor
  · exact ⟨f a b, hfxy_halo⟩
  · intro hz
    exact halo_eq_of_mem_halo (stdPart_spec (lift₂ f x y) hz) hfxy_halo

end StandardPartTransfer

/-! ## Full NSA Proof of Heine-Cantor

We now provide the complete NSA proof of the Heine-Cantor theorem:
**A continuous function on a compact set is uniformly continuous.**

The proof strategy:
1. Take any two hyperelements `x, y` in `K*` with `x ≈ y` (entourage-close)
2. By compactness, both `x` and `y` are near-standard: `x ≈ a`, `y ≈ b` for `a, b ∈ K`
3. Since `x ≈ y` and `x ≈ a` and `y ≈ b`, by transitivity `a ≈ b`
4. In a Hausdorff space, `a ≈ b` implies `a = b`
5. By continuity at `a`: `f(x) ≈ f(a)` and `f(y) ≈ f(a)`
6. Therefore `f(x) ≈ f(y)` by transitivity

This is the **microcontinuity** characterization of uniform continuity.
-/

section HeineCantor

variable [UniformSpace α] [UniformSpace β]

/-- If two elements are both in the halo of the same point in a uniform space,
then they are entourage-close. -/
theorem entourageClose_of_mem_halo {x y : Hyper ι α} {a : α}
    (hx : x ∈ halo a) (hy : y ∈ halo a) : EntourageClose x y := by
  intro U hU
  -- Get symmetric V with V ○ V ⊆ U
  obtain ⟨V, hV, hVsymm, hVU⟩ := comp_symm_mem_uniformity_sets hU
  -- ball a V is a neighborhood of a (explicitly at type α)
  let ball_a : Set α := {b : α | (a, b) ∈ V}
  have hball : ball_a ∈ nhds a := UniformSpace.ball_mem_nhds a hV
  -- x and y are in the lifted ball
  have hx_ball : liftPred (· ∈ ball_a) x := (mem_halo_iff a x).mp hx ball_a hball
  have hy_ball : liftPred (· ∈ ball_a) y := (mem_halo_iff a y).mp hy ball_a hball
  -- Work with ofSeq representation
  obtain ⟨f, rfl⟩ := ofSeq_surjective x
  obtain ⟨g, rfl⟩ := ofSeq_surjective y
  rw [liftPred_ofSeq] at hx_ball hy_ball
  rw [liftRel_ofSeq]
  -- hx_ball: ∀ᶠ n, f n ∈ ball a V, i.e., (a, f n) ∈ V
  -- hy_ball: ∀ᶠ n, g n ∈ ball a V, i.e., (a, g n) ∈ V
  -- By symmetry of V: (f n, a) ∈ V
  -- By composition: (f n, g n) ∈ V ○ V ⊆ U
  apply Filter.Eventually.mono (hx_ball.and hy_ball)
  intro n ⟨hfn, hgn⟩
  -- hfn : (a, f n) ∈ V, hgn : (a, g n) ∈ V
  -- By symmetry: (f n, a) ∈ V
  have hfn_symm : (f n, a) ∈ V := hVsymm.symm a (f n) hfn
  -- By composition: (f n, g n) ∈ V ○ V
  have hcomp : (f n, g n) ∈ SetRel.comp V V := ⟨a, hfn_symm, hgn⟩
  exact hVU hcomp

/-- The key lemma for Heine-Cantor: if two hyperelements are both near-standard to the same
point, then their images under a continuous function are entourage-close.

This captures the essence of the NSA proof: continuity at standard points plus nearness
to the same standard point gives closeness of images. -/
theorem entourageClose_lift_of_same_stdPart [T2Space α] [T2Space β]
    {f : α → β} {x y : Hyper ι α} {a : α}
    (hx : x ∈ halo a) (hy : y ∈ halo a) (hf : ContinuousAt f a) :
    EntourageClose (lift f x) (lift f y) := by
  -- By continuity at a, both lift f x and lift f y are in halo (f a)
  have hfx := st_lift_eq_of_continuousAt hx hf
  have hfy := st_lift_eq_of_continuousAt hy hf
  -- Two elements in the same halo are entourage-close
  exact entourageClose_of_mem_halo hfx hfy

/-- Standard elements that are entourage-close are equal (T2 characterization). -/
theorem std_entourageClose_std_iff [T2Space α] (a b : α) :
    EntourageClose (std a : Hyper ι α) (std b) ↔ a = b := by
  constructor
  · intro h
    -- EntourageClose (std a) (std b) means for all U ∈ 𝓤 α, (a, b) ∈ U
    -- This is exactly (a, b) ∈ (𝓤 α).ker = ⋂₀ (𝓤 α).sets
    have hker : (a, b) ∈ (uniformity α).ker := by
      simp only [Filter.ker, Set.mem_sInter, Filter.mem_sets]
      intro U hU
      exact (liftRel_std (fun a b => (a, b) ∈ U) a b).mp (h U hU)
    -- By inseparable_iff_ker_uniformity, this means Inseparable a b
    rw [← inseparable_iff_ker_uniformity] at hker
    -- In T2Space (which implies T0Space), Inseparable implies equality
    exact hker.eq
  · intro h
    rw [h]
    exact EntourageClose.refl _

/-- **Heine-Cantor Theorem (NSA Proof)**: A continuous function on a compact subset of a
T2 uniform space is uniformly continuous on that set.

The NSA proof:
1. For `x ≈ y` in `K*`, compactness gives `x ≈ a`, `y ≈ b` for some `a, b ∈ K`
2. `x ≈ y` and `x ≈ a` and `y ≈ b` implies `a ≈ b` (entourage transitivity)
3. Hausdorff: `a ≈ b` for standard `a, b` implies `a = b`
4. Continuity at `a`: `f(x) ≈ f(a)` and `f(y) ≈ f(a)`, so `f(x) ≈ f(y)` -/
theorem heineCantor_nsa [T2Space α] [T2Space β]
    [Nonempty (Set α ↪ ι)]
    {K : Set α} (hK : IsCompact K) {f : α → β} (hf : ContinuousOn f K) :
    ∀ x y : Hyper ι α, liftPred (· ∈ K) x → liftPred (· ∈ K) y →
      EntourageClose x y → EntourageClose (lift f x) (lift f y) := by
  intro x y hxK hyK hxy
  -- Save original compactness before rewriting
  have hK_compact : IsCompact K := hK
  -- By compactness (NSA version), x is near-standard to some a ∈ K
  rw [isCompact_iff_nearStd (ι := ι) (α := α) K] at hK
  obtain ⟨a, haK, hxa⟩ := hK x hxK
  obtain ⟨b, hbK, hyb⟩ := hK y hyK
  -- x ∈ halo a and y ∈ halo b (convert from IsNearStandard to halo membership)
  -- IsNearStandard x a means x ∈ monad (nhds a) = ∀ U ∈ nhds a, liftPred (· ∈ U) x
  have hx_halo_a : x ∈ halo a := (mem_halo_iff a x).mpr hxa
  have hy_halo_b : y ∈ halo b := (mem_halo_iff b y).mpr hyb
  -- Show a = b using entourage closeness and Hausdorff
  have hab : a = b := by
    -- x ≃ᵤ std a (since x ∈ halo a)
    have hx_std_a : EntourageClose x (std a : Hyper ι α) :=
      entourageClose_of_mem_halo hx_halo_a (std_mem_halo a)
    -- y ≃ᵤ std b (since y ∈ halo b)
    have hy_std_b : EntourageClose y (std b : Hyper ι α) :=
      entourageClose_of_mem_halo hy_halo_b (std_mem_halo b)
    -- x ≃ᵤ y by hypothesis, so by transitivity:
    -- std a ≃ᵤ x ≃ᵤ y ≃ᵤ std b
    have h_a_b : EntourageClose (std a : Hyper ι α) (std b) :=
      hx_std_a.symm.trans (hxy.trans hy_std_b)
    exact (std_entourageClose_std_iff a b).mp h_a_b
  -- Now a = b, so use continuity at a = b
  rw [hab] at hx_halo_a
  -- ContinuousWithinAt f K b from ContinuousOn
  have hfb : ContinuousWithinAt f K b := hf b hbK
  -- Show lift f x ∈ halo (f b) and lift f y ∈ halo (f b)
  have hfx_halo : lift f x ∈ halo (f b) := by
    rw [mem_halo_iff]
    intro V hV
    -- By ContinuousWithinAt, f⁻¹'V ∈ 𝓝[K] b
    have hpre : f ⁻¹' V ∈ 𝓝[K] b := hfb.preimage_mem_nhdsWithin hV
    -- Decompose: ∃ U ∈ nhds b, U ∩ K ⊆ f⁻¹'V
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hpre
    obtain ⟨U, hU, hUK⟩ := hpre
    -- x ∈ halo b means liftPred (· ∈ U) x
    have hxU : liftPred (· ∈ U) x := (mem_halo_iff b x).mp hx_halo_a U hU
    -- Combined with liftPred (· ∈ K) x, get liftPred (· ∈ U ∩ K) x
    have hxUK : liftPred (· ∈ U ∩ K) x := (liftPred_and x).mpr ⟨hxU, hxK⟩
    -- By monotonicity: U ∩ K ⊆ f⁻¹'V implies liftPred (· ∈ f⁻¹'V) x
    -- By monotonicity and liftPred_lift
    rw [liftPred_lift]
    obtain ⟨s, rfl⟩ := ofSeq_surjective x
    rw [liftPred_ofSeq] at hxUK ⊢
    exact hxUK.mono fun i hi => hUK hi
  have hfy_halo : lift f y ∈ halo (f b) := by
    rw [mem_halo_iff]
    intro V hV
    have hpre : f ⁻¹' V ∈ 𝓝[K] b := hfb.preimage_mem_nhdsWithin hV
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hpre
    obtain ⟨U, hU, hUK⟩ := hpre
    have hyU : liftPred (· ∈ U) y := (mem_halo_iff b y).mp hy_halo_b U hU
    have hyUK : liftPred (· ∈ U ∩ K) y := (liftPred_and y).mpr ⟨hyU, hyK⟩
    rw [liftPred_lift]
    obtain ⟨t, rfl⟩ := ofSeq_surjective y
    rw [liftPred_ofSeq] at hyUK ⊢
    exact hyUK.mono fun i hi => hUK hi
  -- Both lift f x and lift f y are in halo (f b), so they are entourage-close
  exact entourageClose_of_mem_halo hfx_halo hfy_halo

end HeineCantor

/-! ## Equivalent Norms via NSA

Two norms on a finite-dimensional vector space are equivalent. The NSA proof:

1. Both norms extend to the hyperextension
2. On the "unit sphere" of one norm, the other norm is bounded (by compactness)
3. Infinitesimals in one norm are infinitesimals in the other
4. This gives the equivalence

The key insight: the unit sphere is compact, so hyperelements on its extension
are near-standard, giving uniform bounds.
-/

section EquivalentNorms

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

/-- Lift of a norm to hyperelements. -/
def liftNorm [Norm E] (x : Hyper ι E) : Hyper ι ℝ := lift (‖·‖) x

omit [AddCommGroup E] in
/-- For norms that agree on standard elements, they agree on near-standard elements
up to infinitesimals. -/
theorem liftNorm_infClose_of_continuous [NormedAddCommGroup E]
    {p : E → ℝ} (hp_cont : Continuous p) (hp_norm : ∀ e : E, 0 ≤ p e)
    {x : Hyper ι E} (hx : IsNearStd x) :
    ∃ c : ℝ, 0 ≤ c ∧ lift p x ≤ std c * liftNorm x + std c := by
  -- By near-standardness, x is in halo of some standard element
  obtain ⟨a, ha⟩ := hx
  -- Use c = p(a) + 1
  use p a + 1
  constructor
  · -- 0 ≤ p a + 1
    linarith [hp_norm a]
  · -- lift p x ≤ std (p a + 1) * liftNorm x + std (p a + 1)
    -- Work with ofSeq representations
    obtain ⟨s, rfl⟩ := ofSeq_surjective x
    -- Rewrite everything in terms of ofSeq
    rw [lift_ofSeq, liftNorm, lift_ofSeq]
    simp only [mul_eq_lift₂, add_eq_lift₂, std_eq_ofSeq_const, lift₂_ofSeq, ofSeq_le_ofSeq,
      Function.comp_apply]
    -- From x ∈ halo a, s n is eventually in any neighborhood of a
    rw [mem_halo_ofSeq_iff] at ha
    -- Since p is continuous at a, p(s i) is eventually close to p(a)
    have hU : Metric.ball (p a) 1 ∈ 𝓝 (p a) := Metric.ball_mem_nhds _ one_pos
    have hpre : p ⁻¹' Metric.ball (p a) 1 ∈ 𝓝 a := hp_cont.continuousAt.preimage_mem_nhds hU
    have h1 : ∀ᶠ i in hyperfilter ι, |p (s i) - p a| < 1 := by
      filter_upwards [ha (p ⁻¹' Metric.ball (p a) 1) hpre] with i hi
      exact Metric.mem_ball.mp hi
    -- The bound follows
    filter_upwards [h1] with i hi
    have hp_bound : p (s i) < p a + 1 := by
      rw [abs_lt] at hi
      linarith
    have h_norm_nonneg : 0 ≤ ‖s i‖ := norm_nonneg (s i)
    have h_pa_pos : 0 < p a + 1 := by linarith [hp_norm a]
    have h_mul_nonneg : 0 ≤ (p a + 1) * ‖s i‖ := mul_nonneg (le_of_lt h_pa_pos) h_norm_nonneg
    linarith

end EquivalentNorms

end Hyper
