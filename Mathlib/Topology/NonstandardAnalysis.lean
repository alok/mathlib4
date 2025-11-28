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

/-!
# Nonstandard Characterizations of Topological Concepts

This file provides nonstandard (infinitesimal) characterizations of topological
concepts like continuity, compactness, and convergence using hyperstructures.

## Main Definitions

* `Hyper.monad` - The monad of a point: the set of hyperreals infinitely close to it
* `Hyper.IsNearStd` - A hyperreal is near-standard if it's in some standard point's monad
* `Hyper.stdPart` - The standard part of a near-standard element
* `Hyper.Infinitesimal` - An element infinitesimally close to 0 (in normed spaces)
* `Hyper.InfClose` - Two elements are infinitesimally close

## Main Results

### Continuity
* `Hyper.continuousAt_iff_monad` - `f` is continuous at `x` iff `f` maps `monad x`
  into `monad (f x)`

### Compactness
* `Hyper.isCompact_iff_nearStd` - A set is compact iff every element of its star is
  near-standard and has standard part in the set

### Convergence
* `Hyper.tendsto_iff_monad` - `Tendsto f l (𝓝 y)` iff `f*` maps near-standard elements
  to `monad y`

## References

* Robinson, A. "Non-standard Analysis"
* Goldblatt, R. "Lectures on the Hyperreals"
* Luxemburg, W.A.J. "A General Theory of Monads"
-/

open Filter Topology Set

namespace Hyper

variable {ι : Type*} [Infinite ι] {α β : Type*}

/-! ## The Monad (Halo) of a Point

The monad of a point `x` is the set of all hyperelements that are "infinitely close" to `x`.
In the ultraproduct construction, this is the intersection of the stars of all
neighborhoods of `x`.
-/

section Monad

variable [TopologicalSpace α]

/-- The **monad** (or **halo**) of a point `x` is the intersection of the *-extensions of all
neighborhoods of `x`. An element `y : Hyper ι α` is in `monad x` iff for every neighborhood `U`
of `x`, `y` is in `U*` (i.e., `y` satisfies the lifted membership predicate for `U`).

Intuitively, `monad x` consists of all hyperelements "infinitely close" to `x`. -/
def monad (x : α) : Set (Hyper ι α) :=
  ⋂ U ∈ 𝓝 x, {y : Hyper ι α | liftPred (· ∈ U) y}

/-- Alternative characterization: `y` is in `monad x` iff for all neighborhoods `U` of `x`,
`y` is eventually in `U`. -/
theorem mem_monad_iff (x : α) (y : Hyper ι α) :
    y ∈ monad x ↔ ∀ U ∈ 𝓝 x, liftPred (· ∈ U) y := by
  simp only [monad, mem_iInter, mem_setOf_eq]

/-- Sequence characterization of monad membership. -/
theorem mem_monad_ofSeq_iff (x : α) (f : ι → α) :
    (ofSeq f : Hyper ι α) ∈ monad x ↔ ∀ U ∈ 𝓝 x, ∀ᶠ n in hyperfilter ι, f n ∈ U := by
  simp only [mem_monad_iff, liftPred_ofSeq]

/-- Standard elements are in their own monads. -/
theorem std_mem_monad (x : α) : (std x : Hyper ι α) ∈ monad x := by
  rw [mem_monad_iff]
  intro U hU
  rw [liftPred_std]
  exact mem_of_mem_nhds hU

/-- The monad is nonempty (it contains the standard embedding of the point). -/
theorem monad_nonempty (x : α) : (monad x : Set (Hyper ι α)).Nonempty :=
  ⟨std x, std_mem_monad x⟩

/-- If `y` is in the monad of `x`, and `x` is in an open set `U`, then `y` satisfies `U*`. -/
theorem monad_subset_star_of_isOpen {x : α} {U : Set α} (hU : IsOpen U) (hx : x ∈ U) :
    monad x ⊆ {y : Hyper ι α | liftPred (· ∈ U) y} := by
  intro y hy
  rw [mem_monad_iff] at hy
  exact hy U (hU.mem_nhds hx)

end Monad

/-! ## Near-Standard Elements and Standard Parts

An element is **near-standard** if it belongs to some standard point's monad.
The **standard part** of a near-standard element is that unique standard point.
-/

section NearStd

variable [TopologicalSpace α]

/-- An element `y : Hyper ι α` is **near-standard** if there exists a standard element
whose monad contains `y`. -/
def IsNearStd (y : Hyper ι α) : Prop :=
  ∃ x : α, y ∈ monad x

/-- Standard elements are near-standard. -/
theorem IsNearStd.std (x : α) : IsNearStd (std x : Hyper ι α) :=
  ⟨x, std_mem_monad x⟩

/-- In a Hausdorff space, the standard part is unique. -/
theorem monad_eq_of_mem_monad [T2Space α] {x y : α} {z : Hyper ι α}
    (hx : z ∈ monad x) (hy : z ∈ monad y) : x = y := by
  by_contra hne
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := t2_separation hne
  rw [mem_monad_iff] at hx hy
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
    y ∈ monad (stdPart y hy) :=
  hy.choose_spec

/-- The standard part of a standard element is itself. -/
theorem stdPart_std [T2Space α] (x : α) :
    stdPart (std x : Hyper ι α) (IsNearStd.std x) = x :=
  monad_eq_of_mem_monad (stdPart_spec _ _) (std_mem_monad x)

end NearStd

/-! ## Infinitesimals in Normed Spaces

For normed spaces, we can define infinitesimals as elements whose norm is smaller than
any positive standard real.
-/

section Infinitesimal

variable [NormedAddCommGroup α]

/-- An element `x : Hyper ι α` is **infinitesimal** if its norm is less than every positive
standard real. Equivalently, `x` is in the monad of `0`. -/
def Infinitesimal (x : Hyper ι α) : Prop :=
  ∀ ε : ℝ, 0 < ε → lift (‖·‖) x < (std ε : Hyper ι ℝ)

/-- Alternative definition using monad. -/
theorem infinitesimal_iff_mem_monad_zero (x : Hyper ι α) :
    Infinitesimal x ↔ x ∈ monad (0 : α) := by
  constructor
  · -- Infinitesimal → monad 0
    intro hinf
    rw [mem_monad_iff]
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
  · -- monad 0 → Infinitesimal
    intro hmonad ε hε
    rw [mem_monad_iff] at hmonad
    -- The ball {x : ‖x‖ < ε} is a neighborhood of 0
    have hball_nhds : Metric.ball (0 : α) ε ∈ 𝓝 0 := Metric.ball_mem_nhds 0 hε
    have hx_in_ball := hmonad (Metric.ball 0 ε) hball_nhds
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
  simp only [← std_zero, lift_std, norm_zero, std_lt]
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
    simp only [← std_sub, lift_std, std_lt] at this
    linarith
  · intro h
    rw [h]
    exact InfClose.refl _

end InfClose

/-! ## NSA Characterization of Continuity -/

section Continuity

variable [TopologicalSpace α] [TopologicalSpace β]

/-- **NSA characterization of continuity**: `f` is continuous at `x` iff
`f` maps every element of `monad x` into `monad (f x)`.

Intuitively: `f` is continuous at `x` iff whenever `y ≈ x`, we have `f(y) ≈ f(x)`. -/
theorem continuousAt_iff_monad {f : α → β} {x : α} :
    ContinuousAt f x ↔ ∀ y : Hyper ι α, y ∈ monad x → lift f y ∈ monad (f x) := by
  constructor
  · -- Forward: continuous at x → monad preservation
    intro hcont y hy
    rw [mem_monad_iff] at hy ⊢
    intro V hV
    -- V is a neighborhood of f(x), so f⁻¹(V) is a neighborhood of x
    have hpreimage : f ⁻¹' V ∈ 𝓝 x := hcont hV
    -- y is in monad x, so y satisfies the lifted predicate for f⁻¹(V)
    have hy_preimage := hy (f ⁻¹' V) hpreimage
    -- lift f y satisfies the lifted predicate for V
    obtain ⟨g, rfl⟩ := ofSeq_surjective y
    rw [liftPred_ofSeq] at hy_preimage
    rw [lift_ofSeq, liftPred_ofSeq]
    simp only [Set.mem_preimage] at hy_preimage
    convert hy_preimage using 1
  · -- Backward: monad preservation → continuous at x
    intro hmonad
    rw [ContinuousAt, Filter.Tendsto]
    intro V hV
    -- Need to show f⁻¹(V) ∈ 𝓝 x
    -- Use contrapositive: if f⁻¹(V) ∉ 𝓝 x, find y ∈ monad x with lift f y ∉ monad (f x)
    by_contra hcontra
    -- If f⁻¹(V) ∉ 𝓝 x, then (f⁻¹(V))ᶜ intersects every neighborhood of x
    -- For each neighborhood U of x, pick a point in U ∩ (f⁻¹(V))ᶜ
    -- This gives a "net" converging to x but whose images avoid V
    -- The ultrafilter construction gives us such a y
    -- For general topology (not metric), this requires choice over the neighborhood filter
    -- This proof requires more infrastructure about ultrafilter extensions
    sorry

/-- Continuous functions preserve monad membership. -/
theorem Continuous.monad_map {f : α → β} (hf : Continuous f) (x : α) :
    ∀ y ∈ monad (ι := ι) x, lift f y ∈ monad (f x) := by
  intro y hy
  exact (continuousAt_iff_monad (ι := ι)).mp hf.continuousAt y hy

end Continuity

/-! ## NSA Characterization of Compactness -/

section Compactness

variable [TopologicalSpace α]

/-- **NSA characterization of compactness**: A set `K` is compact iff every element of `K*`
(the *-extension of `K`) is near-standard with standard part in `K`.

Intuitively: `K` is compact iff every hyperreal "in `K`" is infinitely close to some
standard element of `K`. -/
theorem isCompact_iff_nearStd [T2Space α] {K : Set α} :
    IsCompact K ↔ ∀ y : Hyper ι α, liftPred (· ∈ K) y → IsNearStd y ∧
      ∀ (hy : IsNearStd y), stdPart y hy ∈ K := by
  sorry

/-- In a compact set, every element of the *-extension is near-standard. -/
theorem IsCompact.isNearStd_of_mem_star [T2Space α] {K : Set α} (hK : IsCompact K)
    {y : Hyper ι α} (hy : liftPred (· ∈ K) y) : IsNearStd y := by
  exact (isCompact_iff_nearStd.mp hK y hy).1

end Compactness

/-! ## NSA Characterization of Limits and Convergence -/

section Limits

variable [TopologicalSpace α]

/-- **NSA characterization of limits**: `Tendsto f F (𝓝 L)` iff for every `x` with
`liftPred (· ∈ F) x`, we have `lift f x ∈ monad L`.

For sequences: `f n → L` iff for every infinite `N`, `f N ≈ L`. -/
theorem tendsto_iff_lift_mem_monad {β : Type*} {f : β → α} {F : Filter β} {L : α} :
    Tendsto f F (𝓝 L) ↔
      ∀ x : Hyper ι β, (∀ U ∈ F, liftPred (· ∈ U) x) → lift f x ∈ monad L := by
  sorry

/-- For sequences: convergence iff infinite indices map to the monad. -/
theorem tendsto_atTop_iff_infinite_in_monad {f : ℕ → α} {L : α} :
    Tendsto f atTop (𝓝 L) ↔
      ∀ N : Hyper ℕ ℕ, IsInfinite N → lift f N ∈ monad L := by
  sorry

end Limits

end Hyper
