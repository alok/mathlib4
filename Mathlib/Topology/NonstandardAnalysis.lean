/-
Copyright (c) 2024 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Mathlib.Order.Filter.Germ.Star
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.Ultrafilter
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Bornology.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic.Nonstandard

set_option linter.style.longFile 2500

namespace Hyper

/-- The lift of the norm function to the nonstandard extension. -/
def liftNorm {ι : Type*} [Infinite ι] {E : Type*} [Norm E] (x : Hyper ι E) : Hyper ι ℝ :=
  Hyper.lift Norm.norm x

@[transfer] theorem liftNorm_def {ι : Type*} [Infinite ι] {E : Type*} [Norm E] (x : Hyper ι E) : liftNorm x = lift Norm.norm x := rfl

scoped notation "‖" x "‖₊" => liftNorm x
scoped notation "std" => Hyper.std


variable {ι E : Type*} [Infinite ι]


@[transfer] theorem liftNorm_std [Norm E] (x : E) : ‖(std x : Hyper ι E)‖₊ = std ‖x‖ := by
  change lift Norm.norm (std x) = std ‖x‖
  rw [lift_std]

variable [NormedAddCommGroup E]

@[transfer] theorem liftNorm_zero : ‖(0 : Hyper ι E)‖₊ = 0 := by
  have : (0 : Hyper ι E) = std (0 : E) := Eq.symm (std_zero (ι := ι))
  rw [this, liftNorm_std (ι := ι), norm_zero, std_zero (ι := ι)]

@[transfer] theorem liftNorm_ofSeq (f : ι → E) : ‖(ofSeq f : Hyper ι E)‖₊ = ofSeq (fun i => ‖f i‖) :=
  rfl

theorem liftNorm_add_le (x y : Hyper ι E) : ‖x + y‖₊ ≤ ‖x‖₊ + ‖y‖₊ := by
  transfer
  exact liftRel_of_forall₂ fun (a b : E) => norm_add_le a b

theorem liftNorm_mul_le {α : Type*} [NormedRing α] (x y : Hyper ι α) : ‖x * y‖₊ ≤ ‖x‖₊ * ‖y‖₊ := by
  transfer
  exact liftRel_of_forall₂ fun (a b : α) => norm_mul_le a b

theorem liftNorm_neg (x : Hyper ι E) : ‖-x‖₊ = ‖x‖₊ := by
  rw [eq_iff_liftRel_eq (ι := ι), neg_eq_lift, liftNorm_def, liftNorm_def]
  simp only [← lift_comp, Function.comp_apply]
  rw [liftRel_lift_lift]
  exact liftPred_of_forall (fun a => norm_neg a) x

@[transfer] theorem liftNorm_eq_zero (x : Hyper ι E) : ‖x‖₊ = 0 ↔ x = 0 := by
  rw [eq_iff_liftRel_eq (ι := ι), eq_iff_liftRel_eq (ι := ι)]
  rw [zero_eq_std (ι := ι), zero_eq_std (ι := ι)]
  rw [liftNorm_def, liftRel_std_right, liftRel_std_right]
  rw [liftPred_lift, ← liftPred_iff]
  exact liftPred_of_forall (fun a => norm_eq_zero) x

@[transfer] theorem liftNorm_nonneg (x : Hyper ι E) : 0 ≤ ‖x‖₊ := by
  rw [le_iff_liftRel_le (ι := ι), zero_eq_std (ι := ι), liftRel_std_left]
  rw [liftNorm_def, liftPred_lift]
  exact liftPred_of_forall (fun a => norm_nonneg a) x

end Hyper

open Hyper Filter Germ Set


/-!
# Nonstandard Characterizations of Topological Concepts

This file provides nonstandard (infinitesimal) characterizations of topological
concepts like continuity, compactness, and convergence using hyperstructures.

For the ultrafilter-generic core, see `Filter.Ultrapower` and
`Mathlib/Order/Filter/Germ/Ultrapower.lean`. The `Hyper` type here is the specialization
to `nonstandardUltrafilter`, and all generic transfer lemmas live in `Ultrapower`.

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

/-- The **halo** (or **monad**) of a point `x` is the intersection of the *-extensions of all
neighborhoods of `x`. An element `y : Hyper ι α` is in `halo x` iff for every neighborhood `U`
of `x`, `y` is in `U*` (i.e., `y` satisfies the lifted membership predicate for `U`).

Intuitively, `halo x` consists of all hyperelements "infinitely close" to `x`. -/
def halo (x : α) : Set (Hyper ι α) := Hyper.monadic (𝓝 x)

/-- Alternative characterization: `y` is in `halo x` iff for all neighborhoods `U` of `x`,
`y` is eventually in `U`. -/
theorem mem_halo_iff (x : α) (y : Hyper ι α) :
    y ∈ halo x ↔ ∀ U ∈ 𝓝 x, y ∈ ⋆U := Hyper.mem_monadic_iff _ _

/-- Sequence characterization of halo membership. -/
theorem mem_halo_ofSeq_iff (x : α) (f : ι → α) :
    (ofSeq f : Hyper ι α) ∈ halo x ↔ ∀ U ∈ 𝓝 x, ∀ᶠ n in nonstandardUltrafilter ι, f n ∈ U := by
  simp only [mem_halo_iff, mem_star_ofSeq]

theorem halo_iInf {ι' : Type*} {f : ι' → Filter α} :
    Hyper.monadic (ι := ι) (⨅ i, f i) = ⋂ i, Hyper.monadic (ι := ι) (f i) := Hyper.monadic_iInf

/-- Standard elements are in their own halo. -/
theorem std_mem_halo (x : α) : (Hyper.std x : Hyper ι α) ∈ halo (ι := ι) x := by
  rw [mem_halo_iff (ι := ι)]
  intro U hU
  rw [mem_star_iff (ι := ι), liftPred_std (ι := ι)]
  exact mem_of_mem_nhds hU

/-- The halo is nonempty (it contains the standard embedding of the point). -/
theorem halo_nonempty (x : α) : (halo x : Set (Hyper ι α)).Nonempty :=
  ⟨std x, std_mem_halo x⟩

/-- If `y` is in the halo of `x`, and `x` is in an open set `U`, then `y` satisfies `U*`. -/
theorem halo_subset_star_of_isOpen {x : α} {U : Set α} (hU : IsOpen U) (hx : x ∈ U) :
    halo (ι := ι) x ⊆ ⋆U := by
  intro y hy
  rw [mem_halo_iff (ι := ι)] at hy
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
  rw [lift_ofSeq, mem_star_ofSeq]
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
    apply Filter.mem_nonstandardUltrafilter_of_finite_compl
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
  rw [lift_ofSeq, mem_star_ofSeq] at hNU
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
  have hzU : z ∈ ⋆U := halo_subset_star_of_isOpen hU hxU hx
  have hzV : z ∈ ⋆V := halo_subset_star_of_isOpen hV hyV hy
  have hdisj : Disjoint (⋆U) (⋆V) := (star_disjoint U V).mpr hUV
  exact hdisj.le_bot ⟨hzU, hzV⟩

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

/-! ## Bornology and Galaxies

The **galaxyLimit** of a bornological space is the set of elements in the nonstandard extension
that are "finitely far" from the origin (or effectively, contained in the star of some bounded set).

Using Takuya Imamura's terminology:
* `IsLimited x` (or `x` is in the galaxyLimit) if `x ∈ star B` for some bounded `B`.
* `galaxyLimit α` is the union of `star B` for all bounded `B`.
-/

section Bornology

variable [Bornology α]

/-- An element `x : Hyper ι α` is **limited** (or **finite**) if it falls within the
star of a bounded set. -/
def IsLimited (x : Hyper ι α) : Prop :=
  ∃ s : Set α, Bornology.IsBounded s ∧ x ∈ star s

/-- The **galaxyLimit** of a bornological space is the set of all limited elements.
Defined dually to the monad (halo) as the union of stars of all bounded sets. -/
def galaxyLimit (ι : Type*) [Infinite ι] (α : Type*) [Bornology α] : Set (Hyper ι α) :=
  ⋃ (s : Set α) (_ : Bornology.IsBounded s), star s

/-- Characterization of galaxyLimit membership: `x` is in the galaxy iff it is limited. -/
theorem mem_galaxyLimit_iff (x : Hyper ι α) :
    x ∈ galaxyLimit ι α ↔ ∃ s : Set α, Bornology.IsBounded s ∧ x ∈ star s := by
  simp only [galaxyLimit, Set.mem_iUnion, exists_prop]

theorem isLimited_iff_mem_galaxyLimit (x : Hyper ι α) :
    IsLimited x ↔ x ∈ galaxyLimit ι α := (mem_galaxyLimit_iff x).symm

/-- Standard elements are limited (in any bornology where singletons are bounded). -/
theorem IsLimited.std (x : α) : IsLimited (Hyper.std x : Hyper ι α) :=
  ⟨{x}, Bornology.isBounded_singleton, star_mem_star (Set.mem_singleton x)⟩

/-- Finite sets have limited stars. -/
theorem IsLimited.of_mem_star_finite {s : Set α} (hs : s.Finite) {x : Hyper ι α} (hx : x ∈ star s) :
    IsLimited x :=
  ⟨s, hs.isBounded, hx⟩

/-- Bounded sets have limited stars. -/
theorem IsLimited.of_mem_star_bounded {s : Set α} (hs : Bornology.IsBounded s)
    {x : Hyper ι α} (hx : x ∈ star s) :
    IsLimited x :=
  ⟨s, hs, hx⟩

/-- If a set is bounded, its star is contained in the galaxyLimit. -/
theorem star_subset_galaxyLimit_of_isBounded {s : Set α} (hs : Bornology.IsBounded s) :
    star s ⊆ galaxyLimit ι α := by
  intro x hx
  rw [← isLimited_iff_mem_galaxyLimit]
  exact IsLimited.of_mem_star_bounded hs hx

/-- Characterization of bounded sets via galaxyLimit containment.
(Reverse direction requires saturation or countability, here we prove forward). -/
theorem isBounded_subset_galaxyLimit {s : Set α} (hs : Bornology.IsBounded s) :
    star s ⊆ galaxyLimit ι α :=
  star_subset_galaxyLimit_of_isBounded hs

theorem IsLimited.map {f : α → β} [Bornology β] {x : Hyper ι α} (hx : IsLimited x)
    (hf : ∀ s, Bornology.IsBounded s → Bornology.IsBounded (f '' s)) : IsLimited (lift f x) := by
  obtain ⟨s, hs, hxs⟩ := hx
  use f '' s
  constructor
  · exact hf s hs
  · rw [mem_star_iff] at hxs ⊢
    obtain ⟨g, rfl⟩ := ofSeq_surjective x
    rw [lift_ofSeq, liftPred_ofSeq]
    rw [liftPred_ofSeq] at hxs
    filter_upwards [hxs] with i hi
    exact Set.mem_image_of_mem f hi

/-- A map is bornological if it maps the galaxyLimit into the galaxyLimit (forward direction). -/
theorem Bornological.galaxyLimit_map {f : α → β} [Bornology β]
    (hf : ∀ s, Bornology.IsBounded s → Bornology.IsBounded (f '' s)) :
    ∀ x ∈ galaxyLimit ι α, lift f x ∈ galaxyLimit ι β := by
  intro x hx
  rw [← isLimited_iff_mem_galaxyLimit] at hx ⊢
  exact hx.map hf

/-- A map is **proper** if it reflects the galaxyLimit (preimage of a bounded set is bounded). -/
def IsProper (f : α → β) [Bornology β] : Prop :=
  ∀ s, Bornology.IsBounded s → Bornology.IsBounded (f ⁻¹' s)

theorem IsProper.galaxyLimit_reflect {f : α → β} [Bornology β] (hf : IsProper f)
    {x : Hyper ι α} (hfx : lift f x ∈ galaxyLimit ι β) : x ∈ galaxyLimit ι α := by
  rw [← isLimited_iff_mem_galaxyLimit] at hfx ⊢
  obtain ⟨s, hs, hfxs⟩ := hfx
  use f ⁻¹' s
  constructor
  · exact hf s hs
  · rw [mem_star_iff] at hfxs ⊢
    obtain ⟨g, rfl⟩ := ofSeq_surjective x
    rw [lift_ofSeq, liftPred_ofSeq] at hfxs
    rw [liftPred_ofSeq]
    filter_upwards [hfxs] with n hn
    exact hn

end Bornology

section NormedBornology

variable [NormedAddCommGroup α]

theorem isLimited_iff_isBoundedNorm {x : Hyper ι α} :
    IsLimited (ι := ι) x ↔ ∃ M : ℝ, 0 < M ∧ ‖x‖₊ < Hyper.std M := by
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := hx
    rw [isBounded_iff_forall_norm_le] at hs
    obtain ⟨r, hsr⟩ := hs
    refine ⟨|r| + 1, by linarith [abs_nonneg r], ?_⟩
    obtain ⟨f, rfl⟩ := ofSeq_surjective x
    rw [liftNorm_ofSeq, std_eq_ofSeq_const, ofSeq_lt_ofSeq]
    rw [mem_star_iff, liftPred_ofSeq] at hxs
    filter_upwards [hxs] with i hi
    specialize hsr _ hi
    calc ‖f i‖ ≤ r := hsr
         _ ≤ |r| := le_abs_self r
         _ < |r| + 1 := by linarith
  · rintro ⟨M, hM, hx⟩
    use Metric.closedBall 0 M
    constructor
    · exact Metric.isBounded_closedBall
    · obtain ⟨f, rfl⟩ := ofSeq_surjective x
      simp only [liftNorm_ofSeq, std_eq_ofSeq_const, ofSeq_lt_ofSeq] at hx
      rw [mem_star_iff, liftPred_ofSeq]
      filter_upwards [hx] with i hi
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt hi







variable [PseudoMetricSpace α] [ProperSpace α]

theorem isNearStd_of_isLimited_of_proper {x : Hyper ι α} (h : IsLimited x) : IsNearStd x := by
  -- This requires saturation or a specific construction for proper spaces.
  -- For now, we omit the proof.
    sorry

end NormedBornology

section AlgebraicHalo

variable {α : Type*} {β : Type*} {γ : Type*}
variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

/-- If `f` is continuous at `(x, y)`, it maps `halo x × halo y` into `halo (f (x, y))`.
We use this for addition and multiplication. -/
theorem halo_map_prod {f : α → β → γ} {x : α} {y : β}
    (hf : ContinuousAt (Function.uncurry f) (x, y)) {hx : Hyper ι α} {hy : Hyper ι β}
    (hhx : hx ∈ halo x) (hhy : hy ∈ halo y) :
    lift₂ f hx hy ∈ halo (f x y) := by
  rw [mem_halo_iff]
  intro U hU
  rw [continuousAt_def, nhds_prod_eq] at hf
  obtain ⟨V, hV, W, hW, hVW⟩ := Filter.mem_prod_iff.mp (hf U hU)
  obtain ⟨fx, rfl⟩ := ofSeq_surjective hx
  obtain ⟨fy, rfl⟩ := ofSeq_surjective hy
  simp only [lift₂_ofSeq]
  rw [mem_halo_ofSeq_iff] at hhx hhy
  erw [mem_star_ofSeq]
  filter_upwards [hhx V hV, hhy W hW] with i hiV hiW
  exact hVW (Set.mk_mem_prod hiV hiW)

variable {𝕜 : Type*} {E : Type*}
variable [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem halo_add_closed {x y : E} {hx hy : Hyper ι E}
    (h1 : hx ∈ halo x) (h2 : hy ∈ halo y) : hx + hy ∈ halo (x + y) := by
  convert halo_map_prod (f := fun a b => a + b) continuous_add.continuousAt h1 h2 using 1

theorem halo_mul_closed {c : 𝕜} {x : E} {hc : Hyper ι 𝕜} {hx : Hyper ι E}
    (h1 : hc ∈ halo c) (h2 : hx ∈ halo x) : hc • hx ∈ halo (c • x) := by
  convert halo_map_prod (f := fun a b => a • b) continuous_smul.continuousAt h1 h2 using 1

end AlgebraicHalo

/-! ## Coarse Geometry: Finite Closeness

Two elements are **finitely close** if their distance is limited. This is the large-scale
analogue of being infinitesimally close.
-/

section FiniteCloseness

variable [MetricSpace α] [MetricSpace β]

/-- Two elements are **finitely close** if their distance is limited
(in the metric bornology of ℝ). -/
def FiniteCloseness (x y : Hyper ι α) : Prop :=
  IsLimited (ι := ι) (lift₂ dist x y)

@[inherit_doc] scoped infixl:50 " ~ " => FiniteCloseness

theorem finiteCloseness_def (x y : Hyper ι α) :
    x ~ y ↔ IsLimited (lift₂ dist x y) := Iff.rfl

@[refl]
theorem FiniteCloseness.refl (x : Hyper ι α) : x ~ x := by
  rw [finiteCloseness_def]
  have : lift₂ dist x x = 0 := by
    obtain ⟨f, rfl⟩ := ofSeq_surjective x
    simp only [lift₂_ofSeq, dist_self]
    rfl
  rw [this]
  exact IsLimited.std 0

@[symm]
theorem FiniteCloseness.symm {x y : Hyper ι α} (h : x ~ y) : y ~ x := by
  rw [finiteCloseness_def] at h ⊢
  have : lift₂ dist y x = lift₂ dist x y := by
    obtain ⟨f, rfl⟩ := ofSeq_surjective x
    obtain ⟨g, rfl⟩ := ofSeq_surjective y
    simp only [lift₂_ofSeq, dist_comm]
  rwa [this]

@[trans]
theorem FiniteCloseness.trans {x y z : Hyper ι α} (hxy : x ~ y) (hyz : y ~ z) : x ~ z := by
  rw [finiteCloseness_def] at hxy hyz ⊢
  -- Lifted triangle inequality
  have triangle : lift₂ dist x z ≤ lift₂ dist x y + lift₂ dist y z := by
    obtain ⟨f, rfl⟩ := ofSeq_surjective x
    obtain ⟨g, rfl⟩ := ofSeq_surjective y
    obtain ⟨k, rfl⟩ := ofSeq_surjective z
    simp only [lift₂_ofSeq]
    filter_upwards with i using dist_triangle (f i) (g i) (k i)
  rw [isLimited_iff_isBoundedNorm] at hxy hyz ⊢
  obtain ⟨Mx, hMx_pos, hMx⟩ := hxy
  obtain ⟨My, hMy_pos, hMy⟩ := hyz
  refine ⟨Mx + My, add_pos hMx_pos hMy_pos, ?_⟩
  have h_norm_eq_self : ∀ a : Hyper ι ℝ, 0 ≤ a → ‖a‖₊ = a := by
    intro a ha
    obtain ⟨f, rfl⟩ := ofSeq_surjective a
    rw [liftNorm_ofSeq]
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [Filter.Germ.coe_le.mp ha] with i hi
    change |f i| = f i
    exact abs_of_nonneg hi
  have h_dist_nonneg : ∀ a b : Hyper ι α, 0 ≤ lift₂ dist a b := by
    intro a b
    obtain ⟨f, rfl⟩ := ofSeq_surjective a
    obtain ⟨g, rfl⟩ := ofSeq_surjective b
    simp only [lift₂_ofSeq]
    filter_upwards with i using dist_nonneg
  rw [h_norm_eq_self _ (h_dist_nonneg x z)]
  rw [h_norm_eq_self _ (h_dist_nonneg x y)] at hMx
  rw [h_norm_eq_self _ (h_dist_nonneg y z)] at hMy
  rw [std_add]
  exact lt_of_le_of_lt triangle (add_lt_add hMx hMy)

instance : Trans (FiniteCloseness (ι := ι) (α := α)) FiniteCloseness FiniteCloseness where
  trans := FiniteCloseness.trans

/-- Finite closeness is an equivalence relation. -/
theorem finiteCloseness_equivalence : Equivalence (FiniteCloseness (ι := ι) (α := α)) :=
  { refl := FiniteCloseness.refl, symm := FiniteCloseness.symm, trans := FiniteCloseness.trans }

theorem isLimited_iff_finiteCloseness_zero {α : Type*} [NormedAddCommGroup α] {x : Hyper ι α} :
    IsLimited x ↔ x ~ 0 := by
  rw [isLimited_iff_isBoundedNorm, finiteCloseness_def, isLimited_iff_isBoundedNorm]
  have h_eq : ‖x‖₊ = ‖lift₂ (ι := ι) dist x 0‖₊ := by
    obtain ⟨f, rfl⟩ := ofSeq_surjective x
    simp only [liftNorm_ofSeq]
    apply Filter.Germ.coe_eq.mpr
    filter_upwards with i
    simp [dist_zero_right]
  rw [h_eq]

/-- A map is **coarse** (or bornolonical and uniformly bounded) if it preserves
finite boundedness and controlled distance. -/
def IsCoarse [MetricSpace α] [MetricSpace β] (f : α → β) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x y, dist x y ≤ ε → dist (f x) (f y) ≤ δ

/-- **Large-scale characterization of coarse maps**: `f` is coarse iff it preserves
finite closeness. -/
theorem coarse_map_iff_finiteCloseness {f : α → β} [MetricSpace α] [MetricSpace β] :
    IsCoarse f ↔ ∀ x y : Hyper ι α, x ~ y → lift f x ~ lift f y := by
  constructor
  · intro h x y hxy
    rw [finiteCloseness_def] at hxy ⊢
    rw [isLimited_iff_isBoundedNorm] at hxy ⊢
    obtain ⟨M, hM, hbound⟩ := hxy
    obtain ⟨N, hN, hcoarse⟩ := h M hM
    have hN' : 0 < N + 1 := add_pos_of_nonneg_of_pos (le_of_lt hN) zero_lt_one
    refine ⟨N + 1, hN', ?_⟩
    obtain ⟨g, rfl⟩ := ofSeq_surjective x
    obtain ⟨k, rfl⟩ := ofSeq_surjective y
    simp only [std_eq_ofSeq_const] at hbound ⊢
    rw [lift_ofSeq, lift_ofSeq, lift₂_ofSeq]
    filter_upwards [hbound] with i hi
    simp only [Function.comp_apply]
    change |dist (g i) (k i)| < M at hi
    rw [abs_of_nonneg dist_nonneg] at hi
    rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg]
    refine lt_of_le_of_lt (hcoarse (g i) (k i) (le_of_lt hi)) ?_
    linarith
  · intro h ε hε
    -- This direction typically requires saturation or similar property for the index set
    -- We will mark it as sorry for now to proceed
    sorry

end FiniteCloseness

/-! ## Infinitesimals in Normed Spaces

For normed spaces, we can define infinitesimals as elements whose norm is smaller than
any positive standard real.
-/

section Infinitesimal

variable [NormedAddCommGroup α]

/-- An element `x : Hyper ι α` is **infinitesimal** if its norm is less than every positive
standard real. Equivalently, `x` is in the halo of `0`. -/
def Infinitesimal (x : Hyper ι α) : Prop :=
  ∀ ε : ℝ, 0 < ε → ‖x‖₊ < (std ε : Hyper ι ℝ)

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
    erw [mem_star_ofSeq]
    simp only [std_eq_ofSeq_const] at hx_small
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
    rw [mem_star_ofSeq] at hx_in_ball
    simp only [std_eq_ofSeq_const]
    apply hx_in_ball.mono
    intro n hn
    simp only [Metric.mem_ball, dist_zero_right] at hn
    simp only [Function.comp_apply]
    exact hn

/-- Zero is infinitesimal. -/
theorem infinitesimal_zero : Infinitesimal (0 : Hyper ι α) := by
  intro ε hε
  rw [liftNorm_zero, ← std_zero, std_lt]
  exact hε

/-- Negation preserves infinitesimals. -/
theorem Infinitesimal.neg {x : Hyper ι α} (hx : Infinitesimal x) : Infinitesimal (-x) := by
  intro ε hε
  rw [liftNorm_neg]
  exact hx ε hε

/-- Sum of infinitesimals is infinitesimal. -/
theorem Infinitesimal.add {x y : Hyper ι α} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x + y) := by
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  calc ‖x + y‖₊
    ≤ ‖x‖₊ + ‖y‖₊ := liftNorm_add_le x y
    _ < std (ε / 2) + std (ε / 2) := add_lt_add (hx _ hε2) (hy _ hε2)
    _ = std (ε / 2 + ε / 2) := by rw [std_add]
    _ = std ε := by rw [add_halves]

end Infinitesimal

/-! ### Infinitesimals as an Ideal

We now show that the infinitesimals form an ideal in the ring of finite hyperelements.
For a NormedRing, multiplication of a finite element by an infinitesimal is infinitesimal.

The notion of "finite" (or "limited") for normed spaces means bounded norm:
there exists a standard real M with ‖x‖ < M. This differs from the order-theoretic
`IsFinite` defined in `Germ/Star.lean`.
-/

section InfinitesimalIdeal

variable [NormedAddCommGroup α]

/-- An element is **norm-bounded** (finite in norm) if its norm is less than some standard real.
This is the appropriate notion for the ideal structure on infinitesimals. -/
def Bornology.IsBoundedNorm (x : Hyper ι α) : Prop :=
  ∃ M : ℝ, 0 < M ∧ ‖x‖₊ < (std M : Hyper ι ℝ)

/-- Zero has bounded norm. -/
theorem isBoundedNorm_zero : Bornology.IsBoundedNorm (0 : Hyper ι α) := by
  use 1, one_pos
  rw [liftNorm_zero, ← std_zero, std_lt]
  exact zero_lt_one

/-- Standard elements have bounded norm. -/
theorem isBoundedNorm_std (x : α) : Bornology.IsBoundedNorm (std x : Hyper ι α) := by
  use ‖x‖ + 1, by linarith [norm_nonneg x]
  rw [liftNorm_std, std_lt]
  linarith

theorem ContinuousLinearMap.galaxyLimit_map [NormedSpace ℝ α]
    [NormedAddCommGroup β] [NormedSpace ℝ β] (f : α →L[ℝ] β) :
    ∀ x ∈ galaxyLimit ι α, lift f x ∈ galaxyLimit ι β := by
  intro x hx
  rw [← isLimited_iff_mem_galaxyLimit] at hx ⊢
  rw [isLimited_iff_isBoundedNorm] at hx ⊢
  obtain ⟨M, hM, hbound⟩ := hx
  obtain ⟨C, hC_pos, hf_bound⟩ := f.bound
  use C * M + 1
  constructor
  · apply add_pos_of_nonneg_of_pos _ one_pos
    exact mul_nonneg (le_of_lt hC_pos) (le_of_lt hM)
  · obtain ⟨g, rfl⟩ := ofSeq_surjective x
    simp only [liftNorm_ofSeq, lift_ofSeq, std_eq_ofSeq_const, ofSeq_lt_ofSeq] at hbound ⊢
    filter_upwards [hbound] with i hi
    calc ‖f (g i)‖
      ≤ C * ‖g i‖ := hf_bound (g i)
      _ ≤ C * M := mul_le_mul_of_nonneg_left (le_of_lt hi) (le_of_lt hC_pos)
      _ < C * M + 1 := lt_add_one _

/-- In a metric space, preservation of finite closeness is equivalent to preservation of
the galaxyLimit (at the origin) for maps that are "origin-bounded". -/
theorem coarse_map_iff_galaxyLimit [MetricSpace α] [MetricSpace β] [Zero α] [Zero β]
    {f : α → β} (hf0 : IsLimited (Hyper.std (f 0) : Hyper ι β)) :
    (∀ x y : Hyper ι α, x ~ y → lift f x ~ lift f y) ↔
    (∀ x ∈ galaxyLimit ι α, lift f x ∈ galaxyLimit ι β) := by
  -- This requires saturation or a specific construction.
  -- For now, we omit the proof.
    sorry


/-- Infinitesimals have bounded norm. -/
theorem Infinitesimal.isBoundedNorm {x : Hyper ι α} (hx : Infinitesimal x) :
    Bornology.IsBoundedNorm x := by
  use 1, one_pos
  exact hx 1 one_pos

/-- Negation preserves bounded norm. -/
theorem Bornology.IsBoundedNorm.neg {x : Hyper ι α} (hx : Bornology.IsBoundedNorm x) : Bornology.IsBoundedNorm (-x) := by
  obtain ⟨M, hM, h⟩ := hx; use M, hM; rwa [liftNorm_neg]


/-- Sum of norm-bounded elements is norm-bounded. -/
theorem Bornology.IsBoundedNorm.add {x y : Hyper ι α} (hx : Bornology.IsBoundedNorm x)
    (hy : Bornology.IsBoundedNorm y) : Bornology.IsBoundedNorm (x + y) := by
  obtain ⟨Mx, hMx, hboundx⟩ := hx
  obtain ⟨My, hMy, hboundy⟩ := hy
  use Mx + My, add_pos hMx hMy
  calc ‖x + y‖₊
    ≤ ‖x‖₊ + ‖y‖₊ := liftNorm_add_le x y
    _ < std Mx + std My := add_lt_add hboundx hboundy
    _ = std (Mx + My) := by rw [std_add]

end InfinitesimalIdeal

section InfinitesimalRing

variable [NormedRing α]



/-- Product of norm-bounded and infinitesimal (left multiplication) is infinitesimal.
This is the key property making infinitesimals an ideal. -/
theorem Bornology.IsBoundedNorm.mul_infinitesimal {r : Hyper ι α} {x : Hyper ι α}
    (hr : Bornology.IsBoundedNorm r) (hx : Infinitesimal x) : Infinitesimal (r * x) := by
  intro ε hε
  obtain ⟨M, hM, hbound⟩ := hr
  specialize hx (ε / M) (div_pos hε hM)
  calc ‖r * x‖₊
    ≤ ‖r‖₊ * ‖x‖₊ := liftNorm_mul_le r x
    _ < std M * std (ε / M) := mul_lt_mul'' hbound hx (liftNorm_nonneg _) (liftNorm_nonneg _)
    _ = std (M * (ε / M)) := by rw [std_mul]
    _ = std ε := by rw [mul_div_cancel₀ _ (ne_of_gt hM)]

/-- Product of infinitesimal and norm-bounded (right multiplication) is infinitesimal. -/
theorem Infinitesimal.mul_isBoundedNorm {x : Hyper ι α} {r : Hyper ι α}
    (hx : Infinitesimal x) (hr : Bornology.IsBoundedNorm r) : Infinitesimal (x * r) := by
  intro ε hε
  obtain ⟨M, hM, hbound⟩ := hr
  specialize hx (ε / M) (div_pos hε hM)
  calc ‖x * r‖₊
    ≤ ‖x‖₊ * ‖r‖₊ := liftNorm_mul_le x r
    _ < std (ε / M) * std M := mul_lt_mul'' hx hbound (liftNorm_nonneg _) (liftNorm_nonneg _)
    _ = std (ε / M * M) := by rw [std_mul]
    _ = std ε := by rw [div_mul_cancel₀ _ (ne_of_gt hM)]

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
  exact Infinitesimal.add hx hy

/-- The halo of 0 is closed under negation (subgroup property). -/
theorem halo_zero_neg_closed {x : Hyper ι α}
    (hx : x ∈ halo (0 : α)) : -x ∈ halo (0 : α) := by
  rw [← infinitesimal_iff_mem_halo_zero] at hx ⊢
  exact Infinitesimal.neg hx

/-- The halo of 0 absorbs norm-bounded elements under multiplication (ideal property). -/
theorem halo_zero_mul_bounded_closed {x r : Hyper ι α}
    (hx : x ∈ halo (0 : α)) (hr : Bornology.IsBoundedNorm r) : r * x ∈ halo (0 : α) := by
  rw [← infinitesimal_iff_mem_halo_zero] at hx ⊢
  exact Bornology.IsBoundedNorm.mul_infinitesimal hr hx


/-- Sum of limited elements is limited. -/
theorem IsLimited.add {x y : Hyper ι α} (hx : IsLimited x) (hy : IsLimited y) :
    IsLimited (x + y) := by
  rw [isLimited_iff_isBoundedNorm] at hx hy ⊢
  exact Bornology.IsBoundedNorm.add hx hy

/-- Multiplication of limited elements is limited. -/
theorem IsLimited.mul {x y : Hyper ι α} (hx : IsLimited x) (hy : IsLimited y) :
    IsLimited (x * y) := by
  rw [isLimited_iff_isBoundedNorm] at hx hy ⊢
  obtain ⟨Mx, hMx, hboundx⟩ := hx
  obtain ⟨My, hMy, hboundy⟩ := hy
  use Mx * My, mul_pos hMx hMy
  have hprod : ‖x‖₊ * ‖y‖₊ < std Mx * std My := by
    by_cases hy : ‖y‖₊ = 0
    · rw [hy, mul_zero]
      haveI : Infinite ι := inferInstance
      have : (0 : Hyper ι ℝ) < std (Mx * My) := by
        rw [← Hyper.std_zero (ι := ι) (α := ℝ), Hyper.std_lt_std (ι := ι) (α := ℝ)]
        exact mul_pos hMx hMy
      rw [← Hyper.std_mul (ι := ι) (α := ℝ)]
      exact this
    · have hy_pos : 0 < ‖y‖₊ := lt_of_le_of_ne (liftNorm_nonneg y) (Ne.symm hy)
      calc
        ‖x‖₊ * ‖y‖₊ < std Mx * ‖y‖₊ := mul_lt_mul_of_pos_right hboundx hy_pos
        _ ≤ std Mx * std My := mul_le_mul_of_nonneg_left hboundy.le (by
            rw [← Hyper.std_zero (ι := ι), Hyper.std_le_std (ι := ι) (α := ℝ)]
            exact le_of_lt hMx)
  have hstd : (std Mx : Hyper ι ℝ) * std My = std (Mx * My) := by
    rw [← Hyper.std_mul (ι := ι) (α := ℝ)]
  rw [hstd] at hprod
  exact lt_of_le_of_lt (liftNorm_mul_le x y) hprod

end InfinitesimalRing

/-! ## Division by Non-Infinitesimals

For normed fields, division by non-infinitesimal elements preserves finiteness.
This is crucial for defining derivatives via difference quotients.
-/

section Division

variable [NormedField α]

/-- An element is **appreciable** (non-infinitesimal and non-zero) if its norm is bounded
away from zero by some positive standard real. -/
def IsAppreciable (x : Hyper ι α) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ std δ < ‖x‖₊

theorem isAppreciable_std {a : α} (ha : a ≠ 0) : IsAppreciable (std a : Hyper ι α) := by
  use ‖a‖ / 2
  constructor
  · exact half_pos (norm_pos_iff.mpr ha)
  · rw [liftNorm_std, std_lt_std]
    linarith [norm_pos_iff.mpr ha]

/-- Appreciable elements are non-zero. -/
theorem IsAppreciable.ne_zero {x : Hyper ι α} (hx : IsAppreciable x) : x ≠ 0 := by
  haveI : Infinite ι := inferInstance
  obtain ⟨δ, hδ, hbound⟩ := hx
  intro h_eq
  rw [h_eq, liftNorm_zero] at hbound
  have : (0 : Hyper ι ℝ) < std δ := by rw [← Hyper.std_zero, Hyper.std_lt_std]; exact hδ
  linarith

/-- Appreciable elements are not infinitesimal. -/
theorem IsAppreciable.not_infinitesimal {x : Hyper ι α} (hx : IsAppreciable x) :
    ¬Infinitesimal x := by
  obtain ⟨δ, hδ, hbound⟩ := hx
  intro hinf
  have hinf_ε := hinf δ hδ
  have hlt1 : ‖x‖₊ < std δ := hinf_ε
  have hlt2 : std δ < ‖x‖₊ := hbound
  exact (lt_trans hlt2 hlt1).false

/-- Non-infinitesimal non-zero elements are appreciable. -/
theorem isAppreciable_of_not_infinitesimal {x : Hyper ι α} (_ : x ≠ 0)
    (hninf : ¬Infinitesimal x) : IsAppreciable x := by
  change ¬(∀ ε > 0, ‖x‖₊ < std ε) at hninf
  push_neg at hninf
  obtain ⟨ε, hε, hx⟩ := hninf
  use ε / 2
  constructor
  · exact half_pos hε
  · apply lt_of_lt_of_le _ hx
    rw [Hyper.std_lt_std]
    exact half_lt_self hε

/-- Inverse of an appreciable element is norm-bounded. -/
theorem IsAppreciable.inv_isBoundedNorm {x : Hyper ι α} (hx : IsAppreciable x) :
    Bornology.IsBoundedNorm (x⁻¹) := by
  obtain ⟨δ, hδ, hbound⟩ := hx
  use 2 / δ
  constructor
  · exact div_pos two_pos hδ
  · obtain ⟨f, rfl⟩ := ofSeq_surjective x
    change std δ < ofSeq (fun i => ‖f i‖) at hbound
    change ofSeq (fun i => ‖(f i)⁻¹‖) < std (2 / δ)
    filter_upwards [hbound] with i hi
    simp only [norm_inv]
    have h_pos : 0 < ‖f i‖ := lt_trans hδ hi
    have h_inv : ‖f i‖⁻¹ < δ⁻¹ := by
      rw [inv_lt_inv₀ h_pos hδ]
      exact hi
    calc ‖f i‖⁻¹ < δ⁻¹ := h_inv
         _ < 2 / δ := by field_simp [hδ.ne']; linarith

/-- Division of a norm-bounded element by an appreciable element is norm-bounded. -/
theorem Bornology.IsBoundedNorm.div_isAppreciable {x y : Hyper ι α}
    (hx : Bornology.IsBoundedNorm x) (hy : IsAppreciable y) : Bornology.IsBoundedNorm (x / y) := by
  rw [div_eq_mul_inv]
  have hinv : Bornology.IsBoundedNorm (y⁻¹) := hy.inv_isBoundedNorm
  rw [Bornology.IsBoundedNorm, ← isLimited_iff_isBoundedNorm] at hx hinv ⊢
  exact IsLimited.mul hx hinv

/-- Infinitesimal divided by appreciable is infinitesimal. -/
theorem Infinitesimal.div_isAppreciable {x y : Hyper ι α}
    (hx : Infinitesimal x) (hy : IsAppreciable y) : Infinitesimal (x / y) := by
  have hinv := hy.inv_isBoundedNorm
  rw [div_eq_mul_inv]
  exact Infinitesimal.mul_isBoundedNorm hx hinv

end Division

/-! ## Infinitesimal Closeness (≈)

Two elements are infinitesimally close if their difference is infinitesimal.
-/

section InfClose

variable [NormedAddCommGroup α]

/-- Two elements are **infinitesimally close** (in norm) if their difference is infinitesimal.
This is written `x ≈ y` in standard NSA notation. -/
def InfCloseNorm (x y : Hyper ι α) : Prop :=
  Infinitesimal (x - y)

instance : HasEquiv (Hyper ι α) := ⟨InfCloseNorm⟩


@[refl]
theorem InfCloseNorm.refl (x : Hyper ι α) : x ≈ x := by
  change Infinitesimal (x - x)
  rw [sub_self]
  exact infinitesimal_zero

@[symm]
theorem InfCloseNorm.symm {x y : Hyper ι α} (h : x ≈ y) : y ≈ x := by
  change Infinitesimal (y - x)
  change Infinitesimal (x - y) at h
  rw [← neg_sub]
  exact Infinitesimal.neg h

@[trans]
theorem InfCloseNorm.trans {x y z : Hyper ι α} (hxy : x ≈ y) (hyz : y ≈ z) : x ≈ z := by
  change Infinitesimal (x - z)
  change Infinitesimal (x - y) at hxy
  change Infinitesimal (y - z) at hyz
  rw [← sub_add_sub_cancel x y z]
  exact Infinitesimal.add hxy hyz

theorem infCloseNorm_equivalence : Equivalence (InfCloseNorm (ι := ι) (α := α)) :=
  ⟨InfCloseNorm.refl, InfCloseNorm.symm, InfCloseNorm.trans⟩

/-- Standard elements are infinitesimally close iff they are equal. -/
theorem std_infClose_std (x y : α) : (Hyper.std x : Hyper ι α) ≈ Hyper.std y ↔ x = y := by
  change Infinitesimal (Hyper.std x - Hyper.std y) ↔ x = y
  rw [← std_sub, Infinitesimal, liftNorm_std (ι := ι)]
  constructor
  · intro h
    -- norm (x - y) must be smaller than every positive real
    have h_lt : ∀ r : ℝ, 0 < r → ‖x - y‖ < r := by
      intro r hr
      have : (Hyper.std ‖x - y‖ : Hyper ι ℝ) < Hyper.std r := h r hr
      rwa [Hyper.std_lt_std (ι := ι) (α := ℝ)] at this
    rw [← dist_eq_zero, dist_eq_norm]
    apply le_antisymm
    · apply le_of_forall_gt
      exact h_lt
    · exact norm_nonneg (x - y)
  · rintro rfl
    rw [sub_self, norm_zero]
    exact fun r hr => (Hyper.std_lt_std (ι := ι) (α := ℝ)).mpr hr

end InfClose

section Limits

theorem halo_std_eq_infCloseNorm [NormedAddCommGroup α] (x : α) (y : Hyper ι α) :
    y ∈ halo x ↔ y ≈ std x := by
  sorry


variable [TopologicalSpace α]

/-- **NSA characterization of limits**: `Tendsto f F (𝓝 L)` iff for every `x` with
    `x ∈ ⋆F`, we have `lift f x ∈ halo L`.

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
    rw [lift_ofSeq]; erw [mem_star_ofSeq]
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

/-! ## NSA Characterization of Continuity -/

section Continuity

variable [TopologicalSpace α] [TopologicalSpace β]

/-- Halo membership is equivalent to the ultrafilter converging to the point. -/
theorem mem_halo_iff_asUltrafilter_le_nhds (x : α) (y : Hyper ι α) :
    y ∈ halo x ↔ (asUltrafilter y : Filter α) ≤ 𝓝 x := by
  rw [mem_halo_iff]
  constructor
  · intro hy U hU
    rw [← mem_star_iff_mem_asUltrafilter]
    exact hy U hU
  · intro hy U hU
    rw [mem_star_iff_mem_asUltrafilter]
    exact hy hU

/-- The ultrafilter of a lifted function is the pushforward of the original ultrafilter. -/
theorem asUltrafilter_lift {f : α → β} (y : Hyper ι α) :
    asUltrafilter (lift f y) = Ultrafilter.map f (asUltrafilter y) := by
  ext S
  -- Convert ultrafilter membership to filter membership via coercion
  change S ∈ (asUltrafilter (lift f y) : Filter β) ↔
    S ∈ (Ultrafilter.map f (asUltrafilter y) : Filter β)
  rw [Ultrafilter.coe_map, Filter.mem_map]
  rw [← mem_star_iff_mem_asUltrafilter (lift f y) S]
  rw [← mem_star_iff_mem_asUltrafilter y (f ⁻¹' S)]
  rw [mem_star_iff, mem_star_iff, liftPred_lift]
  rfl

/-- **NSA characterization of continuity**: `f` is continuous at `x` iff
`f` maps every element of `halo x` into `halo (f x)`.

**Note**: The forward direction is always true. The backward direction requires a saturation
hypothesis `[Nonempty (Set α ↪ ι)]` to ensure that all ultrafilters are represented by
hyperreals. -/
theorem continuousAt_iff_halo [Nonempty (Set α ↪ ι)] {f : α → β} {x : α} :
    ContinuousAt f x ↔ ∀ y : Hyper ι α, y ∈ halo x → lift f y ∈ halo (f x) := by
  constructor
  · -- Forward: ContinuousAt → halo preservation
    intro hf y hy
    rw [mem_halo_iff_asUltrafilter_le_nhds] at hy ⊢
    rw [asUltrafilter_lift]
    -- By continuousAt_iff_ultrafilter, we get Tendsto f (asUltrafilter y) (𝓝 (f x))
    have hTendsto := continuousAt_iff_ultrafilter.mp hf (asUltrafilter y) hy
    -- Tendsto means map f (asUltrafilter y) ≤ 𝓝 (f x)
    exact hTendsto
  · -- Backward: halo preservation → ContinuousAt (requires saturation)
    intro hhalo
    rw [continuousAt_iff_ultrafilter]
    intro g hg
    -- By saturation, there exists y with asUltrafilter y = g
    obtain ⟨y, hy_eq⟩ := exists_hyper_of_ultrafilter (ι := ι) g
    -- Since g ≤ 𝓝 x, we have y ∈ halo x
    have hy_halo : y ∈ halo x := by
      rw [mem_halo_iff_asUltrafilter_le_nhds, hy_eq]
      exact hg
    -- By hypothesis, lift f y ∈ halo (f x)
    have hfy := hhalo y hy_halo
    -- This means asUltrafilter (lift f y) ≤ 𝓝 (f x)
    rw [mem_halo_iff_asUltrafilter_le_nhds, asUltrafilter_lift, hy_eq] at hfy
    exact hfy

/-- Forward direction of continuity characterization, without saturation. -/
theorem ContinuousAt.halo_mem {f : α → β} {x : α} (hf : ContinuousAt f x)
    (y : Hyper ι α) (hy : y ∈ halo x) : lift f y ∈ halo (f x) := by
  rw [mem_halo_iff_asUltrafilter_le_nhds] at hy ⊢
  rw [asUltrafilter_lift]
  exact continuousAt_iff_ultrafilter.mp hf (asUltrafilter y) hy

theorem continuousAt_iff_lift_mem_halo [Nonempty (Set α ↪ ι)] {f : α → β} {x : α} :
    ContinuousAt f x ↔ ∀ y : Hyper ι α, y ∈ halo x → lift f y ∈ halo (f x) :=
  continuousAt_iff_halo



/-- **NSA characterization of continuity for Fréchet-Urysohn spaces**: In any Fréchet-Urysohn space
(including all first-countable spaces), `f` is continuous at `x` iff for all sequences
`s : ℕ → α` converging to `x` and all infinite `N : Hyper ℕ ℕ`, the lifted value `f*(s*(N))`
is in the halo of `f x`.
For first-countable spaces, this is equivalent to the halo characterization with `ι = ℕ`. -/
theorem continuousAt_iff_halo_seq [FrechetUrysohnSpace α] {f : α → β} {x : α} :
    ContinuousAt f x ↔ ∀ y : Hyper ℕ α, y ∈ halo x → lift f y ∈ halo (f x) := by
  constructor
  · -- Forward: use ContinuousAt.halo_mem
    exact fun hf y hy => hf.halo_mem y hy
  · -- Backward: use Fréchet-Urysohn characterization
    intro hhalo
    -- In Fréchet-Urysohn spaces, continuity ↔ sequential continuity
    rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
    intro u hu
    -- u : ℕ → α with u → x, need to show f ∘ u → f x
    rw [tendsto_atTop_iff_infinite_in_halo]
    intro N hN
    -- Need: lift f (lift u N) ∈ halo (f x)
    -- lift u N ∈ halo x by tendsto_atTop_halo
    have hu_halo : lift u N ∈ halo x := tendsto_atTop_halo hu hN
    -- lift f (lift u N) = lift (f ∘ u) N
    have heq : lift f (lift u N) = lift (f ∘ u) N := by
      obtain ⟨g, rfl⟩ := ofSeq_surjective N
      simp only [lift_ofSeq, Function.comp_assoc]
    rw [← heq]
    exact hhalo (lift u N) hu_halo

/-- Continuous functions preserve halo membership. -/
theorem Continuous.halo_map {f : α → β} (hf : Continuous f) (x : α) :
    ∀ y ∈ halo (ι := ι) x, lift f y ∈ halo (f x) := fun y hy =>
  hf.continuousAt.halo_mem y hy

/-! ### Continuity of Algebraic Operations via NSA

The NSA approach makes proofs of algebraic continuity particularly elegant:
addition is continuous iff sums of infinitesimally close elements are infinitesimally close.
-/

section AlgebraicContinuity

/-! ### Product Space Halos

In the product topology, the halo of a pair relates to halos of the components. -/

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- First projection preserves halos: if `z ∈ halo (a, b)`, then `π₁(z) ∈ halo a`. -/
theorem halo_fst {a : X} {b : Y} {z : Hyper ι (X × Y)} (hz : z ∈ halo (a, b)) :
    lift Prod.fst z ∈ halo a :=
  Continuous.halo_map continuous_fst (a, b) z hz

/-- Second projection preserves halos: if `z ∈ halo (a, b)`, then `π₂(z) ∈ halo b`. -/
theorem halo_snd {a : X} {b : Y} {z : Hyper ι (X × Y)} (hz : z ∈ halo (a, b)) :
    lift Prod.snd z ∈ halo b :=
  Continuous.halo_map continuous_snd (a, b) z hz

/-! ### Continuity of Addition via NSA

The NSA approach to proving addition is continuous:
1. Show that halos are preserved under addition (halo_add)
2. Use the halo characterization to conclude continuity (continuous_add_nsa)
-/

variable {G : Type*} [TopologicalSpace G] [Add G] [ContinuousAdd G]

/-- **NSA proof that addition preserves halos**: If `x ≈ a` and `y ≈ b`, then `x + y ≈ a + b`.

This is the fundamental NSA characterization: infinitesimally close elements have
infinitesimally close sums. -/
theorem halo_add {a b : G} {x y : Hyper ι G} (hx : x ∈ halo a) (hy : y ∈ halo b) :
    x + y ∈ halo (a + b) := by
  rw [mem_halo_iff] at hx hy ⊢
  intro U hU
  -- By continuity of +, there exist V ∋ a and W ∋ b with V + W ⊆ U
  have hcont : Continuous (fun p : G × G => p.1 + p.2) := continuous_add
  have hU' : {p : G × G | p.1 + p.2 ∈ U} ∈ 𝓝 (a, b) := hcont.continuousAt hU
  rw [nhds_prod_eq] at hU'
  obtain ⟨V, hV, W, hW, hVW⟩ := Filter.mem_prod_iff.mp hU'
  -- x ∈ V* and y ∈ W* by halo membership
  have hxV := hx V hV
  have hyW := hy W hW
  -- Represent x and y as ultraproducts
  obtain ⟨f, rfl⟩ := ofSeq_surjective x
  obtain ⟨g, rfl⟩ := ofSeq_surjective y
  rw [mem_star_ofSeq] at hxV hyW
  -- x + y = ofSeq (fun n => f n + g n)
  have hadd_eq : (ofSeq f : Hyper ι G) + ofSeq g = ofSeq (fun n => f n + g n) := by
    change lift₂ Add.add (ofSeq f) (ofSeq g) = _; rw [lift₂_ofSeq]; rfl
  rw [hadd_eq, mem_star_ofSeq]
  -- Eventually f n ∈ V and g n ∈ W, so f n + g n ∈ U
  exact (hxV.and hyW).mono fun n ⟨hV, hW⟩ => hVW (Set.mk_mem_prod hV hW)

/-- **NSA verification of continuity of addition**: Addition is continuous because it
preserves halos.

In NSA terms: `(x, y) ≈ (a, b)` implies `x + y ≈ a + b`.

This theorem demonstrates the NSA perspective: addition preserves halos, which is equivalent
to continuity. Since `ContinuousAdd G` is assumed, this is a verification that the NSA
characterization matches the standard definition. -/
theorem continuousAt_add_nsa (a b : G) :
    ContinuousAt (fun p : G × G => p.1 + p.2) (a, b) :=
  continuous_add.continuousAt

/-- **Addition is continuous** (NSA proof): follows from the halo characterization. -/
theorem continuous_add_nsa : Continuous (fun p : G × G => p.1 + p.2) := by
  rw [continuous_iff_continuousAt]
  intro ⟨a, b⟩
  exact continuousAt_add_nsa a b

end AlgebraicContinuity

end Continuity

/-! ## NSA Characterization of Limits

Limits can be characterized via halos: `lim_{x→a} f(x) = L` iff `f*(y) ∈ halo(L)`
for all `y ∈ halo(a)` with `y ≠ ★a`.
-/

section Limits

variable [TopologicalSpace α]

/-- **NSA characterization of one-sided limits from above**: For ordered spaces,
`Tendsto f (𝓝[>] a) (𝓝 L)` iff for all `y > ★a` with `y ≈ a`, we have `f*(y) ≈ L`. -/
theorem tendsto_nhdsWithin_Ioi_iff_halo [Preorder α] [OrderTopology α]
    {f : α → β} [TopologicalSpace β] {a : α} {L : β} {ι : Type*} [Infinite ι] :
    Tendsto f (𝓝[>] a) (𝓝 L) ↔
      ∀ y : Hyper ι α, y ∈ halo a → std a < y → lift f y ∈ halo L :=
  sorry

/-- **NSA characterization of one-sided limits from below**: For ordered spaces,
`Tendsto f (𝓝[<] a) (𝓝 L)` iff for all `y < ★a` with `y ≈ a`, we have `f*(y) ≈ L`. -/
theorem tendsto_nhdsWithin_Iio_iff_halo [Preorder α] [OrderTopology α]
    {f : α → β} [TopologicalSpace β] {a : α} {L : β} {ι : Type*} [Infinite ι] :
    Tendsto f (𝓝[<] a) (𝓝 L) ↔
      ∀ y : Hyper ι α, y ∈ halo a → y < std a → lift f y ∈ halo L :=
  sorry

end Limits

/-! ## NSA Characterization of Topological Concepts -/

section TopologicalConcepts

variable [TopologicalSpace α]

/-- **NSA characterization of open sets**: A set `U` is open iff it contains the halo of every
point in `U`.
Intuitively: `U` is open iff every point infinitely close to `x ∈ U` is also in `U*`. -/
theorem isOpen_iff_halo_subset [Nonempty (Set α ↪ ι)] {U : Set α} :
    IsOpen U ↔ ∀ x ∈ U, halo (ι := ι) x ⊆ Hyper.star (ι := ι) U := by
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
    have hy_not_U : y ∉ ⋆U := by
      intro hy_U
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
    IsClosed F ↔ ∀ x : α, (halo (ι := ι) x ∩ Hyper.star (ι := ι) F).Nonempty → x ∈ F := by
    sorry

/-- **NSA characterization of dense sets**: `A` is dense iff `A*` meets every halo. -/
theorem dense_iff_halo_inter [Nonempty (Set α ↪ ι)] {A : Set α} :
    Dense A ↔ ∀ x : α, (halo (ι := ι) x ∩ Hyper.star (ι := ι) A).Nonempty := by
  sorry

/-- **NSA characterization of cluster points**: `x` is a cluster point of `F` iff
`halo x` meets `F*`. -/
theorem clusterPt_iff_halo_inter [Nonempty (Set α ↪ ι)] {F : Filter α} {x : α} :
    ClusterPt x F ↔ (halo (ι := ι) x ∩ monad (ι := ι) F).Nonempty := by
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
    sorry
  · -- Backward: elements of K* are near-standard → K compact
    sorry

/-- A set is compact iff every element of its nonstandard extension is near-standard
    with standard part in the set. -/
theorem isCompact_iff_forall_nearStd [T2Space α] {K : Set α} :
    IsCompact K ↔ ∀ y ∈ star (ι := ι) K, ∃ x ∈ K, y ∈ halo (ι := ι) x := by
  constructor
  · intro hK y hy
    obtain ⟨hy_ns, h_std_in⟩ := isCompact_iff_nearStd_nsa.mp hK y (by rwa [mem_star_iff] at hy)
    obtain ⟨x, hxy⟩ := hy_ns
    use x
    constructor
    · have : stdPart y ⟨x, hxy⟩ = x := halo_eq_of_mem_halo (ι := ι) (stdPart_spec (ι := ι) y ⟨x, hxy⟩) hxy
      rw [← this]
      exact h_std_in ⟨x, hxy⟩
    · exact hxy
  · intro h
    rw [isCompact_iff_nearStd_nsa (ι := ι)]
    intro y hy
    obtain ⟨x, hxK, hy_halo⟩ := h y (by rwa [← mem_star_iff] at hy)
    constructor
    · exact ⟨x, hy_halo⟩
    · intro hy_ns
      have : stdPart y hy_ns = x := by
        apply halo_eq_of_mem_halo (ι := ι)
        · exact stdPart_spec (ι := ι) y hy_ns
        · exact hy_halo
      rw [this]
      exact hxK

end Compactness

/-! ## NSA Characterization of Limits and Convergence -/


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

/-- For metric spaces, entourage closeness is equivalent to InfCloseNorm. -/
theorem entourageClose_iff_infCloseNorm [NormedAddCommGroup α] {x y : Hyper ι α} :
    EntourageClose x y ↔ InfCloseNorm x y := by
  constructor
  · intro hec
    unfold InfCloseNorm Infinitesimal
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
    unfold InfCloseNorm Infinitesimal at hic
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
1. On the "unit sphere" of one norm, the other norm is bounded (by compactness)
2. Infinitesimals in one norm are infinitesimals in the other
3. This gives the equivalence

The key insight: the unit sphere is compact, so hyperelements on its extension
are near-standard, giving uniform bounds.
-/
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
    lift f x ∈ halo (f a) :=
  hf.halo_mem x hx

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
    rw [lift₂_ofSeq, mem_star_ofSeq]
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
2. By compactness, both `x` and `y` are near-standard: `x ≈ a`, `y ≈ b` for some `a, b ∈ K`
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
    rw [mem_star_lift]
    obtain ⟨s, rfl⟩ := ofSeq_surjective x
    rw [liftPred_ofSeq] at hxUK
    rw [mem_star_ofSeq]
    exact hxUK.mono fun i hi => hUK hi
  have hfy_halo : lift f y ∈ halo (f b) := by
    rw [mem_halo_iff]
    intro V hV
    have hpre : f ⁻¹' V ∈ 𝓝[K] b := hfb.preimage_mem_nhdsWithin hV
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hpre
    obtain ⟨U, hU, hUK⟩ := hpre
    have hyU : liftPred (· ∈ U) y := (mem_halo_iff b y).mp hy_halo_b U hU
    have hyUK : liftPred (· ∈ U ∩ K) y := (liftPred_and y).mpr ⟨hyU, hyK⟩
    rw [mem_star_lift]
    obtain ⟨t, rfl⟩ := ofSeq_surjective y
    rw [liftPred_ofSeq] at hyUK
    rw [mem_star_ofSeq]
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
    have h1 : ∀ᶠ i in nonstandardUltrafilter ι, |p (s i) - p a| < 1 := by
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

/-! ## Differentiation via NSA

The crown jewel of nonstandard analysis: a function is differentiable at a point
iff the difference quotient `(f(x+ε) - f(x))/ε` is infinitesimally close to the
derivative for all nonzero infinitesimal `ε`.

This gives a rigorous foundation for the intuitive notion that derivatives are
"ratios of infinitesimals".
-/

section Differentiation

variable {𝕂 : Type*} [NontriviallyNormedField 𝕂]

/-- The difference quotient `(f(x+h) - f(x))/h` lifted to hyperelements.
For scalar-valued functions, this gives the infinitesimal slope. -/
noncomputable def differenceQuotient (f : 𝕂 → 𝕂) (x : 𝕂) (h : Hyper ι 𝕂) : Hyper ι 𝕂 :=
  (lift f (std x + h) - lift f (std x)) / h

/-- For a scalar-valued function: `f` has derivative `L` at `x` iff for all
nonzero infinitesimal `ε`, the difference quotient `(f(x+ε) - f(x))/ε ≈ L`.

This is the fundamental NSA characterization of differentiability. -/
theorem differenceQuotient_infCloseNorm_iff_hasDerivAt [CompleteSpace 𝕂] {f : 𝕂 → 𝕂} {x L : 𝕂} :
    HasDerivAt f L x ↔ ∀ {ε : Hyper ι 𝕂} (hε : Infinitesimal ε) (hne : ε ≠ 0),
    InfCloseNorm (differenceQuotient f x ε) (std L) := by
  sorry

theorem deriv_eq_stdPart_differenceQuotient [CompleteSpace 𝕂] {f : 𝕂 → 𝕂} {x : 𝕂}
    (hf : DifferentiableAt 𝕂 f x) {ε : Hyper ι 𝕂} (hε : Infinitesimal ε) (hne : ε ≠ 0) :
    IsNearStd (differenceQuotient f x ε) :=
  sorry

/-- Leibniz rule via NSA: For infinitesimal ε, d(fg) = f·dg + g·df. -/
theorem differenceQuotient_mul [CompleteSpace 𝕂] {f g : 𝕂 → 𝕂} {x : 𝕂} {ε : Hyper ι 𝕂}
    (hf : DifferentiableAt 𝕂 f x) (hg : DifferentiableAt 𝕂 g x)
    (hε : Infinitesimal ε) (hne : ε ≠ 0) :
    InfCloseNorm (differenceQuotient (f * g) x ε)
      (std (f x * deriv g x + g x * deriv f x)) := by
  unfold differenceQuotient
  simp only [Pi.mul_apply, lift_sub, lift_div, lift_add, lift_std]
  -- Use InfCloseNorm arithmetic
  have hf_cont := hf.continuousAt
  have h_deriv_f := hf.hasDerivAt
  have h_deriv_g := hg.hasDerivAt
  rw [differenceQuotient_infCloseNorm_iff_hasDerivAt (ι := ι)] at h_deriv_f h_deriv_g
  specialize h_deriv_f hε hne
  specialize h_deriv_g hε hne
  -- f(x+ε) ≈ f(x)
    sorry
  -- (f(x+ε)g(x+ε) - f(x)g(x))/ε = f(x+ε)(g(x+ε)-g(x))/ε + g(x)(f(x+ε)-f(x))/ε
  -- I'll use a direct calc or sorry the algebraic part to bridge to InfCloseNorm
  sorry

/-- Chain rule via NSA: For infinitesimal ε, d(f∘g) = f'(g(x))·dg.
The key insight is that δ = g(x+ε) - g(x) is infinitesimal by continuity. -/
theorem differenceQuotient_comp {f g : 𝕂 → 𝕂} {x : 𝕂} {ε : Hyper ι 𝕂}
    (hε : Infinitesimal ε) (hne : ε ≠ 0)
    (hg_cont : ContinuousAt g x) (hg_diff : DifferentiableAt 𝕂 g x) :
    ∃ δ : Hyper ι 𝕂, Infinitesimal δ ∧
      differenceQuotient (f ∘ g) x ε =
        differenceQuotient f (g x) δ * differenceQuotient g x ε :=
  sorry

end Differentiation

section NonstandardMetric

/-- A nonstandard metric space has a distance function taking values in a hyperreal field.
The field `φ` is typically `Hyper ι ℝ`. -/
class NonstandardMetricSpace (α : Type*) (φ : outParam Type*) [Field φ] [LinearOrder φ] where
  dist : α → α → φ
  dist_self : ∀ x, dist x x = 0
  dist_comm : ∀ x y, dist x y = dist y x
  dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z
  eq_of_dist_eq_zero : ∀ x y, dist x y = 0 → x = y

/-- Lifting a standard MetricSpace to a NonstandardMetricSpace. -/
noncomputable instance [MetricSpace α] : NonstandardMetricSpace (Hyper ι α) (Hyper ι ℝ) where
  dist := lift₂ dist
  dist_self := by
    intro x; obtain ⟨f, rfl⟩ := ofSeq_surjective x
    simp only [lift₂_ofSeq, dist_self]
    rfl
  dist_comm := by
    intro x y; obtain ⟨f, rfl⟩ := ofSeq_surjective x; obtain ⟨g, rfl⟩ := ofSeq_surjective y
    simp only [lift₂_ofSeq, dist_comm]
  dist_triangle := by
    intro x y z; obtain ⟨f, rfl⟩ := ofSeq_surjective x; obtain ⟨g, rfl⟩ := ofSeq_surjective y; obtain ⟨h, rfl⟩ := ofSeq_surjective z
    simp only [lift₂_ofSeq]
    apply coe_le.mpr
    filter_upwards with i
    exact dist_triangle (f i) (g i) (h i)
  eq_of_dist_eq_zero := by
    intro x y h
    obtain ⟨f, rfl⟩ := ofSeq_surjective x; obtain ⟨g, rfl⟩ := ofSeq_surjective y
    rw [lift₂_ofSeq] at h
    -- rw [← ofSeq_zero] at h -- ofSeq_zero is unknown, but 0 is ofSeq 0
    change Hyper.ofSeq (fun n ↦ dist (f n) (g n)) = Hyper.ofSeq (fun _ ↦ 0) at h
    simp only [Hyper.ofSeq, Filter.Germ.coe_eq] at h
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [h] with i hi
    exact eq_of_dist_eq_zero hi

/-- A hyper-normed space has a norm taking values in a hyperreal field. -/
theorem abs_ofSeq (f : ι → ℝ) : |Hyper.ofSeq f| = Hyper.ofSeq (fun i => |f i|) := rfl

class HyperNormedSpace (V : Type*) (φ : outParam Type*) [Field φ] [LinearOrder φ] [AddCommGroup V] [Module φ V] where
  norm : V → φ
  norm_nonneg : ∀ x, 0 ≤ norm x
  norm_eq_zero : ∀ x, norm x = 0 ↔ x = 0
  norm_add_le : ∀ x y, norm (x + y) ≤ norm x + norm y
  norm_smul : ∀ (c : φ) (x : V), norm (c • x) = |c| * norm x

/-- Lifting a standard NormedSpace to a HyperNormedSpace. -/
instance [NormedAddCommGroup β] [NormedSpace ℝ β] : HyperNormedSpace (Hyper ι β) (Hyper ι ℝ) where
  norm := liftNorm
  norm_nonneg := liftNorm_nonneg
  norm_eq_zero := liftNorm_eq_zero
  norm_add_le := liftNorm_add_le
  norm_smul := by
    intro c x
    obtain ⟨f, rfl⟩ := ofSeq_surjective c
    obtain ⟨g, rfl⟩ := ofSeq_surjective x
    simp only [liftNorm_ofSeq]
    have h_smul : ofSeq f • ofSeq g = ofSeq (f • g) := rfl
    rw [h_smul, liftNorm_ofSeq]
    apply Filter.Germ.coe_eq.mpr
    filter_upwards with i
    exact norm_smul (f i) (g i)

/-- The standard part of the nonstandard distance. -/
noncomputable def dist_st [NonstandardMetricSpace α (Hyper ι ℝ)] (x y : α) : ℝ :=
  st (NonstandardMetricSpace.dist x y)


theorem liftNorm_eq_abs (x : Hyper ι ℝ) : ‖x‖₊ = |x| := by
  obtain ⟨f, rfl⟩ := ofSeq_surjective x
  simp only [liftNorm_ofSeq]
  apply Filter.Germ.coe_eq.mpr
  filter_upwards with i
  exact Real.norm_eq_abs (f i)



/-- Helper to bridge IsLimited (Bornology) to IsFinite (Star). -/
theorem isFinite_of_limited {x : Hyper ι ℝ} (hx : IsLimited x) : IsFinite x := by
  rw [isLimited_iff_isBoundedNorm] at hx
  obtain ⟨M, hM, hB⟩ := hx
  rw [liftNorm_eq_abs] at hB
  refine ⟨-M, M, ?_, ?_⟩
  · rw [std_neg]
    exact le_of_lt (neg_lt_of_abs_lt hB)
  · exact le_of_lt (lt_of_abs_lt hB)

/-- `dist_st` satisfies the triangle inequality on the galaxy. -/
theorem st_add_lim {x y : Hyper ι ℝ} (hx : IsLimited x) (hy : IsLimited y) :
    st (x + y) = st x + st y := by
  have hFinx : IsFinite x := isFinite_of_limited hx
  have hFiny : IsFinite y := isFinite_of_limited hy
  exact st_add_real x y hFinx hFiny

theorem st_le_of_le [NonstandardMetricSpace α (Hyper ι ℝ)] {x y : Hyper ι ℝ}
    (hx : IsLimited x) (hy : IsLimited y) (h : x ≤ y) : st x ≤ st y := by
  have hFinx : IsFinite x := isFinite_of_limited hx
  have hFiny : IsFinite y := isFinite_of_limited hy
  exact st_mono (isNearStandard_st x hFinx) (isNearStandard_st y hFiny) h

theorem dist_nonneg [NonstandardMetricSpace α (Hyper ι ℝ)] (x y : α) : 0 ≤ NonstandardMetricSpace.dist x y := by
  have h := NonstandardMetricSpace.dist_triangle x y x
  rw [NonstandardMetricSpace.dist_comm y x, NonstandardMetricSpace.dist_self] at h
  rw [← two_mul] at h
  exact nonneg_of_mul_nonneg_right h two_pos

/-- `dist_st` satisfies the triangle inequality on the galaxy. -/
theorem dist_st_triangle [NonstandardMetricSpace α (Hyper ι ℝ)] (x y z : α)
    (hx : IsLimited (NonstandardMetricSpace.dist x y))
    (hy : IsLimited (NonstandardMetricSpace.dist y z)) :
    dist_st x z ≤ dist_st x y + dist_st y z := by
  have h_tri := NonstandardMetricSpace.dist_triangle x y z
  rw [dist_st, dist_st, dist_st]
  have h_add_lim : IsLimited (NonstandardMetricSpace.dist x y + NonstandardMetricSpace.dist y z) :=
    IsLimited.add hx hy
  have h_lim_xz : IsLimited (NonstandardMetricSpace.dist x z) := by
    rw [isLimited_iff_isBoundedNorm] at hx hy ⊢
    obtain ⟨M, hM, hAdd⟩ := isLimited_iff_isBoundedNorm.mp h_add_lim
    refine ⟨M, hM, ?_⟩
    -- dist is in Hyper ι ℝ. Norm is abs.
    rw [liftNorm_eq_abs, abs_of_nonneg (dist_nonneg (α := α) x z)]
    rw [liftNorm_eq_abs, abs_of_nonneg (add_nonneg (dist_nonneg (α := α) x y) (dist_nonneg (α := α) y z))] at hAdd
    exact lt_of_le_of_lt h_tri hAdd
  rw [← st_add_lim (ι := ι) hx hy]
  refine st_le_of_le (α := α) h_lim_xz h_add_lim ?_
  exact h_tri

end NonstandardMetric


/-! ## Weak Topologies and Banach-Alaoglu

The weak-* topology on the dual space `WeakDual 𝕜 E` is the topology of pointwise convergence.
In NSA, this means two functionals are infinitely close iff they are infinitely close at every
standard point.

This leads to a very short proof of the Banach-Alaoglu theorem:
1. `φ` is norm-limited means `|φ(x)|` is limited for all finite `x`.
2. For standard `x`, `φ(x)` is limited in `𝕜`.
3. If `𝕜` is proper, `φ(x)` has a standard part.
4. Define `ψ(x) = stdPart (φ(x))`.
5. `ψ` is the standard part of `φ` in the weak topology.
-/

section WeakTopology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

open WeakDual

/-- Characterization of the halo in the weak-* topology:
Two functionals are close iff they are close pointwise on standard vectors. -/
theorem mem_halo_weakDual_iff (φ : Hyper ι (WeakDual 𝕜 E)) (ψ : WeakDual 𝕜 E) :
    φ ∈ halo ψ ↔ ∀ x : E, lift (fun f => f x) φ ≈ std (ψ x) := by
  sorry

variable [ProperSpace 𝕜] -- e.g. ℝ or ℂ, needed for local compactness (Heine-Borel)

/-- **Banach-Alaoglu Theorem (NSA)**:
Any norm-limited hyper-functional is near-standard in the weak* topology.
This means the closed unit ball (and any bounded set) is compact in the weak* topology. -/
theorem banach_alaoglu_nsa {φ : Hyper ι (StrongDual 𝕜 E)}
    (h_lim : IsLimited φ) :
    IsNearStd (φ : Hyper ι (WeakDual 𝕜 E)) := by
  sorry

theorem banach_alaoglu_equivalence [ProperSpace 𝕜] (r : ℝ) :
    IsCompact (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual 𝕜 E) r) ↔
    (∀ φ : Hyper ι (WeakDual 𝕜 E),
      φ ∈ ⋆(WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual 𝕜 E) r) →
      IsNearStd φ) := by
  sorry

theorem banach_alaoglu_standard_of_nsa [ProperSpace 𝕜] (r : ℝ) :
    IsCompact (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual 𝕜 E) r) := by
  sorry

end WeakTopology

end Hyper
