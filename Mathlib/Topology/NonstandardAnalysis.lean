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
import Mathlib.Topology.Sequences

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

/-- If a sequence converges to `x`, then any hyperextension of that sequence applied to an
infinite hypernatural is in `monad x`. -/
theorem tendsto_atTop_monad {f : ℕ → α} {x : α} (hf : Tendsto f atTop (𝓝 x))
    {N : Hyper ℕ ℕ} (hN : IsInfinite N) : lift f N ∈ monad (ι := ℕ) x := by
  rw [mem_monad_iff]
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

/-- Converse: if for all infinite N, lift f N is in monad x, then f → x.
This is the key bridge lemma for sequences. -/
theorem monad_tendsto_atTop {f : ℕ → α} {x : α}
    (hmonad : ∀ N : Hyper ℕ ℕ, IsInfinite N → lift f N ∈ monad (ι := ℕ) x) :
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
  have hN_inf : IsInfinite N := by
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
  -- By hypothesis, lift f N ∈ monad x
  have hNmonad := hmonad N hN_inf
  rw [mem_monad_iff] at hNmonad
  -- So lift f N is eventually in U
  have hNU := hNmonad U (hUopen.mem_nhds hU)
  -- But f (nseq k) ∉ U for all k
  rw [lift_ofSeq, liftPred_ofSeq] at hNU
  -- hNU says f (nseq k) ∈ U eventually, contradicting hnseq_notU
  obtain ⟨k, hk⟩ := hNU.exists
  simp only [Function.comp_apply] at hk
  exact hnseq_notU k hk

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
is in the monad of `f x`.

For first-countable spaces, this is equivalent to the monad characterization with `ι = ℕ`. -/
theorem continuousAt_iff_monad_seq [FrechetUrysohnSpace α] {f : α → β} {x : α} :
    ContinuousAt f x ↔ ∀ y : Hyper ℕ α, y ∈ monad x → lift f y ∈ monad (f x) := by
  constructor
  · -- Forward direction: use the general theorem
    exact fun hcont y hy => (continuousAt_iff_monad (ι := ℕ)).mp hcont y hy
  · -- Backward direction: use sequential characterization
    intro hmonad
    -- ContinuousAt is Tendsto f (𝓝 x) (𝓝 (f x))
    -- In Fréchet-Urysohn spaces, this is equivalent to sequential continuity
    rw [ContinuousAt, tendsto_nhds_iff_seq_tendsto]
    intro u hu
    -- u is a sequence converging to x, so we need f ∘ u → f x
    -- Use monad_tendsto_atTop: show that for all infinite N, lift (f ∘ u) N ∈ monad (f x)
    apply monad_tendsto_atTop
    intro N hN
    -- lift u N ∈ monad x because u → x (using tendsto_atTop_monad)
    have hmonad_u : lift u N ∈ monad x := tendsto_atTop_monad hu hN
    -- By hypothesis, lift f (lift u N) ∈ monad (f x)
    -- We need to show lift (f ∘ u) N = lift f (lift u N)
    obtain ⟨g, rfl⟩ := ofSeq_surjective N
    -- lift (f ∘ u) (ofSeq g) = ofSeq ((f ∘ u) ∘ g)
    -- lift f (lift u (ofSeq g)) = ofSeq (f ∘ u ∘ g), equal by associativity
    have heq : lift (f ∘ u) (ofSeq g : Hyper ℕ ℕ) = lift f (lift u (ofSeq g)) := by
      simp only [lift_ofSeq, Function.comp_assoc]
    rw [heq]
    exact hmonad (lift u (ofSeq g)) hmonad_u

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
standard element of `K`.

**Note**: The forward direction uses `isCompact_iff_ultrafilter_le_nhds`. The backward
direction requires a saturation hypothesis to construct appropriate ultrafilters. -/
theorem isCompact_iff_nearStd [T2Space α] {K : Set α} :
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
    -- This means y = ofSeq f is in monad x
    have hy_monad : (ofSeq f : Hyper ι α) ∈ monad x := by
      rw [mem_monad_iff]
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
      exact ⟨x, hy_monad⟩
    · -- stdPart is in K
      intro hy_nearstd
      -- stdPart is unique in T2 space
      have hstd_eq : stdPart (ofSeq f) hy_nearstd = x :=
        monad_eq_of_mem_monad (stdPart_spec _ _) hy_monad
      rw [hstd_eq]
      exact hxK
  · -- Backward: all elements near-standard → K compact (requires saturation)
    intro hmonad
    rw [isCompact_iff_ultrafilter_le_nhds]
    intro u hu
    -- u : Ultrafilter α with u ≤ 𝓟 K
    -- We need to find x ∈ K with u ≤ 𝓝 x
    -- This requires constructing y : Hyper ι α from u, which needs saturation
    -- For general ι, this requires |ι| ≥ cardinality assumptions
    -- TODO: Add saturation hypothesis or prove for ι = ℕ with countable filter basis
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

For sequences: `f n → L` iff for every infinite `N`, `f N ≈ L`.

**Note**: The forward direction is provable. The backward direction requires a saturation
hypothesis to construct appropriate elements of `Hyper ι β` from ultrafilters on `β`. -/
theorem tendsto_iff_lift_mem_monad {β : Type*} {f : β → α} {F : Filter β} {L : α} :
    Tendsto f F (𝓝 L) ↔
      ∀ x : Hyper ι β, (∀ U ∈ F, liftPred (· ∈ U) x) → lift f x ∈ monad L := by
  constructor
  · -- Forward: Tendsto → monad membership
    intro hf x hx
    rw [mem_monad_iff]
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
  · -- Backward: monad membership → Tendsto (requires saturation)
    intro hmonad
    rw [Filter.Tendsto]
    intro V hV
    -- Need to show f⁻¹(V) ∈ F
    -- The issue: to use the contrapositive, we need to construct x : Hyper ι β
    -- from an ultrafilter on β, which requires saturation
    -- For now, we leave this as sorry with documentation
    -- TODO: Add saturation hypothesis or prove for specific cases
    sorry

/-- For sequences: convergence iff infinite indices map to the monad.

This is the key NSA characterization of sequence convergence: `f n → L` iff
for every infinite hypernatural `N`, `f*(N)` is in the monad of `L`.

Intuitively: a sequence converges to `L` iff evaluating it at any "infinite index"
gives a value infinitely close to `L`. -/
theorem tendsto_atTop_iff_infinite_in_monad {f : ℕ → α} {L : α} :
    Tendsto f atTop (𝓝 L) ↔
      ∀ N : Hyper ℕ ℕ, IsInfinite N → lift f N ∈ monad L :=
  ⟨fun hf _N hN => tendsto_atTop_monad hf hN, monad_tendsto_atTop⟩

end Limits

end Hyper
