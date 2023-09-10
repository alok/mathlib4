/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Alistair Tucker, Wen Yang
-/
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Topology.Order.Basic

#align_import topology.algebra.order.intermediate_value from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"

/-!
# Intermediate Value Theorem

In this file we prove the Intermediate Value Theorem: if `f : α → β` is a function defined on a
connected set `s` that takes both values `≤ a` and values `≥ a` on `s`, then it is equal to `a` at
some point of `s`. We also prove that intervals in a dense conditionally complete order are
preconnected and any preconnected set is an interval. Then we specialize IVT to functions continuous
on intervals.

## Main results

* `IsPreconnected_I??` : all intervals `I??` are preconnected,
* `IsPreconnected.intermediate_value`, `intermediate_value_univ` : Intermediate Value Theorem for
  connected sets and connected spaces, respectively;
* `intermediate_value_Icc`, `intermediate_value_Icc'`: Intermediate Value Theorem for functions
  on closed intervals.

### Miscellaneous facts

* `IsClosed.Icc_subset_of_forall_mem_nhdsWithin` : “Continuous induction” principle;
  if `s ∩ [a, b]` is closed, `a ∈ s`, and for each `x ∈ [a, b) ∩ s` some of its right neighborhoods
  is included `s`, then `[a, b] ⊆ s`.
* `IsClosed.Icc_subset_of_forall_exists_gt`, `IsClosed.mem_of_ge_of_forall_exists_gt` : two
  other versions of the “continuous induction” principle.

## Tags

intermediate value theorem, connected space, connected set
-/


open Filter OrderDual TopologicalSpace Function Set

open Topology Filter

universe u v w

/-!
### Intermediate value theorem on a (pre)connected space

In this section we prove the following theorem (see `IsPreconnected.intermediate_value₂`): if `f`
and `g` are two functions continuous on a preconnected set `s`, `f a ≤ g a` at some `a ∈ s` and
`g b ≤ f b` at some `b ∈ s`, then `f c = g c` at some `c ∈ s`. We prove several versions of this
statement, including the classical IVT that corresponds to a constant function `g`.
-/


section

variable {X : Type u} {α : Type v} [TopologicalSpace X] [LinearOrder α] [TopologicalSpace α]
  [OrderClosedTopology α]

/-- Intermediate value theorem for two functions: if `f` and `g` are two continuous functions
on a preconnected space and `f a ≤ g a` and `g b ≤ f b`, then for some `x` we have `f x = g x`. -/
theorem intermediate_value_univ₂ [PreconnectedSpace X] {a b : X} {f g : X → α} (hf : Continuous f)
    (hg : Continuous g) (ha : f a ≤ g a) (hb : g b ≤ f b) : ∃ x, f x = g x := by
  obtain ⟨x, _, hfg, hgf⟩ : (univ ∩ { x | f x ≤ g x ∧ g x ≤ f x }).Nonempty
  exact
    isPreconnected_closed_iff.1 PreconnectedSpace.isPreconnected_univ _ _ (isClosed_le hf hg)
      (isClosed_le hg hf) (fun _ _ => le_total _ _) ⟨a, trivial, ha⟩ ⟨b, trivial, hb⟩
  exact ⟨x, le_antisymm hfg hgf⟩
#align intermediate_value_univ₂ intermediate_value_univ₂

theorem intermediate_value_univ₂_eventually₁ [PreconnectedSpace X] {a : X} {l : Filter X} [NeBot l]
    {f g : X → α} (hf : Continuous f) (hg : Continuous g) (ha : f a ≤ g a) (he : g ≤ᶠ[l] f) :
    ∃ x, f x = g x :=
  let ⟨_, h⟩ := he.exists; intermediate_value_univ₂ hf hg ha h
#align intermediate_value_univ₂_eventually₁ intermediate_value_univ₂_eventually₁

theorem intermediate_value_univ₂_eventually₂ [PreconnectedSpace X] {l₁ l₂ : Filter X} [NeBot l₁]
    [NeBot l₂] {f g : X → α} (hf : Continuous f) (hg : Continuous g) (he₁ : f ≤ᶠ[l₁] g)
    (he₂ : g ≤ᶠ[l₂] f) : ∃ x, f x = g x :=
  let ⟨_, h₁⟩ := he₁.exists
  let ⟨_, h₂⟩ := he₂.exists
  intermediate_value_univ₂ hf hg h₁ h₂
#align intermediate_value_univ₂_eventually₂ intermediate_value_univ₂_eventually₂

/-- Intermediate value theorem for two functions: if `f` and `g` are two functions continuous
on a preconnected set `s` and for some `a b ∈ s` we have `f a ≤ g a` and `g b ≤ f b`,
then for some `x ∈ s` we have `f x = g x`. -/
theorem IsPreconnected.intermediate_value₂ {s : Set X} (hs : IsPreconnected s) {a b : X}
    (ha : a ∈ s) (hb : b ∈ s) {f g : X → α} (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (ha' : f a ≤ g a) (hb' : g b ≤ f b) : ∃ x ∈ s, f x = g x :=
  let ⟨x, hx⟩ :=
    @intermediate_value_univ₂ s α _ _ _ _ (Subtype.preconnectedSpace hs) ⟨a, ha⟩ ⟨b, hb⟩ _ _
      (continuousOn_iff_continuous_restrict.1 hf) (continuousOn_iff_continuous_restrict.1 hg) ha'
      hb'
  ⟨x, x.2, hx⟩
#align is_preconnected.intermediate_value₂ IsPreconnected.intermediate_value₂

theorem IsPreconnected.intermediate_value₂_eventually₁ {s : Set X} (hs : IsPreconnected s) {a : X}
    {l : Filter X} (ha : a ∈ s) [NeBot l] (hl : l ≤ 𝓟 s) {f g : X → α} (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) (ha' : f a ≤ g a) (he : g ≤ᶠ[l] f) : ∃ x ∈ s, f x = g x := by
  rw [continuousOn_iff_continuous_restrict] at hf hg
  obtain ⟨b, h⟩ :=
    @intermediate_value_univ₂_eventually₁ _ _ _ _ _ _ (Subtype.preconnectedSpace hs) ⟨a, ha⟩ _
      (comap_coe_neBot_of_le_principal hl) _ _ hf hg ha' (he.comap _)
  exact ⟨b, b.prop, h⟩
#align is_preconnected.intermediate_value₂_eventually₁ IsPreconnected.intermediate_value₂_eventually₁

theorem IsPreconnected.intermediate_value₂_eventually₂ {s : Set X} (hs : IsPreconnected s)
    {l₁ l₂ : Filter X} [NeBot l₁] [NeBot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f g : X → α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) (he₁ : f ≤ᶠ[l₁] g) (he₂ : g ≤ᶠ[l₂] f) :
    ∃ x ∈ s, f x = g x := by
  rw [continuousOn_iff_continuous_restrict] at hf hg
  obtain ⟨b, h⟩ :=
    @intermediate_value_univ₂_eventually₂ _ _ _ _ _ _ (Subtype.preconnectedSpace hs) _ _
      (comap_coe_neBot_of_le_principal hl₁) (comap_coe_neBot_of_le_principal hl₂) _ _ hf hg
      (he₁.comap _) (he₂.comap _)
  exact ⟨b, b.prop, h⟩
#align is_preconnected.intermediate_value₂_eventually₂ IsPreconnected.intermediate_value₂_eventually₂

/-- **Intermediate Value Theorem** for continuous functions on connected sets. -/
theorem IsPreconnected.intermediate_value {s : Set X} (hs : IsPreconnected s) {a b : X} (ha : a ∈ s)
    (hb : b ∈ s) {f : X → α} (hf : ContinuousOn f s) : Icc (f a) (f b) ⊆ f '' s := fun _x hx =>
  hs.intermediate_value₂ ha hb hf continuousOn_const hx.1 hx.2
#align is_preconnected.intermediate_value IsPreconnected.intermediate_value

theorem IsPreconnected.intermediate_value_Ico {s : Set X} (hs : IsPreconnected s) {a : X}
    {l : Filter X} (ha : a ∈ s) [NeBot l] (hl : l ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s) {v : α}
    (ht : Tendsto f l (𝓝 v)) : Ico (f a) v ⊆ f '' s := fun _ h =>
  hs.intermediate_value₂_eventually₁ ha hl hf continuousOn_const h.1
    (eventually_ge_of_tendsto_gt h.2 ht)
#align is_preconnected.intermediate_value_Ico IsPreconnected.intermediate_value_Ico

theorem IsPreconnected.intermediate_value_Ioc {s : Set X} (hs : IsPreconnected s) {a : X}
    {l : Filter X} (ha : a ∈ s) [NeBot l] (hl : l ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s) {v : α}
    (ht : Tendsto f l (𝓝 v)) : Ioc v (f a) ⊆ f '' s := fun _ h =>
  (hs.intermediate_value₂_eventually₁ ha hl continuousOn_const hf h.2
    (eventually_le_of_tendsto_lt h.1 ht)).imp fun _ h => h.imp_right Eq.symm
#align is_preconnected.intermediate_value_Ioc IsPreconnected.intermediate_value_Ioc

theorem IsPreconnected.intermediate_value_Ioo {s : Set X} (hs : IsPreconnected s) {l₁ l₂ : Filter X}
    [NeBot l₁] [NeBot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s)
    {v₁ v₂ : α} (ht₁ : Tendsto f l₁ (𝓝 v₁)) (ht₂ : Tendsto f l₂ (𝓝 v₂)) :
    Ioo v₁ v₂ ⊆ f '' s := fun _ h =>
  hs.intermediate_value₂_eventually₂ hl₁ hl₂ hf continuousOn_const
    (eventually_le_of_tendsto_lt h.1 ht₁) (eventually_ge_of_tendsto_gt h.2 ht₂)
#align is_preconnected.intermediate_value_Ioo IsPreconnected.intermediate_value_Ioo

theorem IsPreconnected.intermediate_value_Ici {s : Set X} (hs : IsPreconnected s) {a : X}
    {l : Filter X} (ha : a ∈ s) [NeBot l] (hl : l ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s)
    (ht : Tendsto f l atTop) : Ici (f a) ⊆ f '' s := fun y h =>
  hs.intermediate_value₂_eventually₁ ha hl hf continuousOn_const h (tendsto_atTop.1 ht y)
#align is_preconnected.intermediate_value_Ici IsPreconnected.intermediate_value_Ici

theorem IsPreconnected.intermediate_value_Iic {s : Set X} (hs : IsPreconnected s) {a : X}
    {l : Filter X} (ha : a ∈ s) [NeBot l] (hl : l ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s)
    (ht : Tendsto f l atBot) : Iic (f a) ⊆ f '' s := fun y h =>
  (hs.intermediate_value₂_eventually₁ ha hl continuousOn_const hf h (tendsto_atBot.1 ht y)).imp
    fun _ h => h.imp_right Eq.symm
#align is_preconnected.intermediate_value_Iic IsPreconnected.intermediate_value_Iic

theorem IsPreconnected.intermediate_value_Ioi {s : Set X} (hs : IsPreconnected s) {l₁ l₂ : Filter X}
    [NeBot l₁] [NeBot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s)
    {v : α} (ht₁ : Tendsto f l₁ (𝓝 v)) (ht₂ : Tendsto f l₂ atTop) : Ioi v ⊆ f '' s := fun y h =>
  hs.intermediate_value₂_eventually₂ hl₁ hl₂ hf continuousOn_const
    (eventually_le_of_tendsto_lt h ht₁) (tendsto_atTop.1 ht₂ y)
#align is_preconnected.intermediate_value_Ioi IsPreconnected.intermediate_value_Ioi

theorem IsPreconnected.intermediate_value_Iio {s : Set X} (hs : IsPreconnected s) {l₁ l₂ : Filter X}
    [NeBot l₁] [NeBot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s)
    {v : α} (ht₁ : Tendsto f l₁ atBot) (ht₂ : Tendsto f l₂ (𝓝 v)) : Iio v ⊆ f '' s := fun y h =>
  hs.intermediate_value₂_eventually₂ hl₁ hl₂ hf continuousOn_const (tendsto_atBot.1 ht₁ y)
    (eventually_ge_of_tendsto_gt h ht₂)
#align is_preconnected.intermediate_value_Iio IsPreconnected.intermediate_value_Iio

theorem IsPreconnected.intermediate_value_Iii {s : Set X} (hs : IsPreconnected s) {l₁ l₂ : Filter X}
    [NeBot l₁] [NeBot l₂] (hl₁ : l₁ ≤ 𝓟 s) (hl₂ : l₂ ≤ 𝓟 s) {f : X → α} (hf : ContinuousOn f s)
    (ht₁ : Tendsto f l₁ atBot) (ht₂ : Tendsto f l₂ atTop) : univ ⊆ f '' s := fun y _ =>
  hs.intermediate_value₂_eventually₂ hl₁ hl₂ hf continuousOn_const (tendsto_atBot.1 ht₁ y)
    (tendsto_atTop.1 ht₂ y)
set_option linter.uppercaseLean3 false in
#align is_preconnected.intermediate_value_Iii IsPreconnected.intermediate_value_Iii

/-- **Intermediate Value Theorem** for continuous functions on connected spaces. -/
theorem intermediate_value_univ [PreconnectedSpace X] (a b : X) {f : X → α} (hf : Continuous f) :
    Icc (f a) (f b) ⊆ range f := fun _ hx => intermediate_value_univ₂ hf continuous_const hx.1 hx.2
#align intermediate_value_univ intermediate_value_univ

/-- **Intermediate Value Theorem** for continuous functions on connected spaces. -/
theorem mem_range_of_exists_le_of_exists_ge [PreconnectedSpace X] {c : α} {f : X → α}
    (hf : Continuous f) (h₁ : ∃ a, f a ≤ c) (h₂ : ∃ b, c ≤ f b) : c ∈ range f :=
  let ⟨a, ha⟩ := h₁; let ⟨b, hb⟩ := h₂; intermediate_value_univ a b hf ⟨ha, hb⟩
#align mem_range_of_exists_le_of_exists_ge mem_range_of_exists_le_of_exists_ge

/-!
### (Pre)connected sets in a linear order

In this section we prove the following results:

* `IsPreconnected.ordConnected`: any preconnected set `s` in a linear order is `ord_connected`,
  i.e. `a ∈ s` and `b ∈ s` imply `Icc a b ⊆ s`;

* `IsPreconnected.mem_intervals`: any preconnected set `s` in a conditionally complete linear order
  is one of the intervals `Set.Icc`, `set.`Ico`, `set.Ioc`, `set.Ioo`, ``Set.Ici`, `Set.Iic`,
  `Set.Ioi`, `Set.Iio`; note that this is false for non-complete orders: e.g., in `ℝ \ {0}`, the set
  of positive numbers cannot be represented as `Set.Ioi _`.

-/


/-- If a preconnected set contains endpoints of an interval, then it includes the whole interval. -/
theorem IsPreconnected.Icc_subset {s : Set α} (hs : IsPreconnected s) {a b : α} (ha : a ∈ s)
    (hb : b ∈ s) : Icc a b ⊆ s := by
  simpa only [image_id] using hs.intermediate_value ha hb continuousOn_id
#align is_preconnected.Icc_subset IsPreconnected.Icc_subset

theorem IsPreconnected.ordConnected {s : Set α} (h : IsPreconnected s) : OrdConnected s :=
  ⟨fun _ hx _ hy => h.Icc_subset hx hy⟩
#align is_preconnected.ord_connected IsPreconnected.ordConnected

/-- If a preconnected set contains endpoints of an interval, then it includes the whole interval. -/
theorem IsConnected.Icc_subset {s : Set α} (hs : IsConnected s) {a b : α} (ha : a ∈ s)
    (hb : b ∈ s) : Icc a b ⊆ s :=
  hs.2.Icc_subset ha hb
#align is_connected.Icc_subset IsConnected.Icc_subset

/-- If preconnected set in a linear order space is unbounded below and above, then it is the whole
space. -/
theorem IsPreconnected.eq_univ_of_unbounded {s : Set α} (hs : IsPreconnected s) (hb : ¬BddBelow s)
    (ha : ¬BddAbove s) : s = univ := by
  refine' eq_univ_of_forall fun x => _
  obtain ⟨y, ys, hy⟩ : ∃ y ∈ s, y < x := not_bddBelow_iff.1 hb x
  obtain ⟨z, zs, hz⟩ : ∃ z ∈ s, x < z := not_bddAbove_iff.1 ha x
  exact hs.Icc_subset ys zs ⟨le_of_lt hy, le_of_lt hz⟩
#align is_preconnected.eq_univ_of_unbounded IsPreconnected.eq_univ_of_unbounded

end

variable {α : Type u} {β : Type v} {γ : Type w} [ConditionallyCompleteLinearOrder α]
  [TopologicalSpace α] [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β]
  [OrderTopology β] [Nonempty γ]

/-- A bounded connected subset of a conditionally complete linear order includes the open interval
`(Inf s, Sup s)`. -/
theorem IsConnected.Ioo_csInf_csSup_subset {s : Set α} (hs : IsConnected s) (hb : BddBelow s)
    (ha : BddAbove s) : Ioo (sInf s) (sSup s) ⊆ s := fun _x hx =>
  let ⟨_y, ys, hy⟩ := (isGLB_lt_iff (isGLB_csInf hs.nonempty hb)).1 hx.1
  let ⟨_z, zs, hz⟩ := (lt_isLUB_iff (isLUB_csSup hs.nonempty ha)).1 hx.2
  hs.Icc_subset ys zs ⟨hy.le, hz.le⟩
#align is_connected.Ioo_cInf_cSup_subset IsConnected.Ioo_csInf_csSup_subset

theorem eq_Icc_csInf_csSup_of_connected_bdd_closed {s : Set α} (hc : IsConnected s)
    (hb : BddBelow s) (ha : BddAbove s) (hcl : IsClosed s) : s = Icc (sInf s) (sSup s) :=
  (subset_Icc_csInf_csSup hb ha).antisymm <|
    hc.Icc_subset (hcl.csInf_mem hc.nonempty hb) (hcl.csSup_mem hc.nonempty ha)
#align eq_Icc_cInf_cSup_of_connected_bdd_closed eq_Icc_csInf_csSup_of_connected_bdd_closed

theorem IsPreconnected.Ioi_csInf_subset {s : Set α} (hs : IsPreconnected s) (hb : BddBelow s)
    (ha : ¬BddAbove s) : Ioi (sInf s) ⊆ s := fun x hx =>
  have sne : s.Nonempty := nonempty_of_not_bddAbove ha
  let ⟨_y, ys, hy⟩ : ∃ y ∈ s, y < x := (isGLB_lt_iff (isGLB_csInf sne hb)).1 hx
  let ⟨_z, zs, hz⟩ : ∃ z ∈ s, x < z := not_bddAbove_iff.1 ha x
  hs.Icc_subset ys zs ⟨hy.le, hz.le⟩
#align is_preconnected.Ioi_cInf_subset IsPreconnected.Ioi_csInf_subset

theorem IsPreconnected.Iio_csSup_subset {s : Set α} (hs : IsPreconnected s) (hb : ¬BddBelow s)
    (ha : BddAbove s) : Iio (sSup s) ⊆ s :=
  @IsPreconnected.Ioi_csInf_subset αᵒᵈ _ _ _ s hs ha hb
#align is_preconnected.Iio_cSup_subset IsPreconnected.Iio_csSup_subset

/-- A preconnected set in a conditionally complete linear order is either one of the intervals
`[Inf s, Sup s]`, `[Inf s, Sup s)`, `(Inf s, Sup s]`, `(Inf s, Sup s)`, `[Inf s, +∞)`,
`(Inf s, +∞)`, `(-∞, Sup s]`, `(-∞, Sup s)`, `(-∞, +∞)`, or `∅`. The converse statement requires
`α` to be densely ordered. -/
theorem IsPreconnected.mem_intervals {s : Set α} (hs : IsPreconnected s) :
    s ∈
      ({Icc (sInf s) (sSup s), Ico (sInf s) (sSup s), Ioc (sInf s) (sSup s), Ioo (sInf s) (sSup s),
          Ici (sInf s), Ioi (sInf s), Iic (sSup s), Iio (sSup s), univ, ∅} :
        Set (Set α)) := by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · apply_rules [Or.inr, mem_singleton]
  have hs' : IsConnected s := ⟨hne, hs⟩
  by_cases hb : BddBelow s <;> by_cases ha : BddAbove s
  · rcases mem_Icc_Ico_Ioc_Ioo_of_subset_of_subset (hs'.Ioo_csInf_csSup_subset hb ha)
        (subset_Icc_csInf_csSup hb ha) with (hs | hs | hs | hs)
    · exact Or.inl hs
    · exact Or.inr <| Or.inl hs
    · exact Or.inr <| Or.inr <| Or.inl hs
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl hs
  · refine' Or.inr <| Or.inr <| Or.inr <| Or.inr _
    cases'
      mem_Ici_Ioi_of_subset_of_subset (hs.Ioi_csInf_subset hb ha) fun x hx => csInf_le hb hx with
      hs hs
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
  · iterate 6 apply Or.inr
    cases' mem_Iic_Iio_of_subset_of_subset (hs.Iio_csSup_subset hb ha) fun x hx => le_csSup ha hx
      with hs hs
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
  · iterate 8 apply Or.inr
    exact Or.inl (hs.eq_univ_of_unbounded hb ha)
#align is_preconnected.mem_intervals IsPreconnected.mem_intervals

/-- A preconnected set is either one of the intervals `Icc`, `Ico`, `Ioc`, `Ioo`, `Ici`, `Ioi`,
`Iic`, `Iio`, or `univ`, or `∅`. The converse statement requires `α` to be densely ordered. Though
one can represent `∅` as `(Inf s, Inf s)`, we include it into the list of possible cases to improve
readability. -/
theorem setOf_isPreconnected_subset_of_ordered :
    { s : Set α | IsPreconnected s } ⊆
      -- bounded intervals
      (range (uncurry Icc) ∪ range (uncurry Ico) ∪ range (uncurry Ioc) ∪ range (uncurry Ioo)) ∪
      -- unbounded intervals and `univ`
      (range Ici ∪ range Ioi ∪ range Iic ∪ range Iio ∪ {univ, ∅}) := by
  intro s hs
  rcases hs.mem_intervals with (hs | hs | hs | hs | hs | hs | hs | hs | hs | hs)
  · exact Or.inl <| Or.inl <| Or.inl <| Or.inl ⟨(sInf s, sSup s), hs.symm⟩
  · exact Or.inl <| Or.inl <| Or.inl <| Or.inr ⟨(sInf s, sSup s), hs.symm⟩
  · exact Or.inl <| Or.inl <| Or.inr ⟨(sInf s, sSup s), hs.symm⟩
  · exact Or.inl <| Or.inr ⟨(sInf s, sSup s), hs.symm⟩
  · exact Or.inr <| Or.inl <| Or.inl <| Or.inl <| Or.inl ⟨sInf s, hs.symm⟩
  · exact Or.inr <| Or.inl <| Or.inl <| Or.inl <| Or.inr ⟨sInf s, hs.symm⟩
  · exact Or.inr <| Or.inl <| Or.inl <| Or.inr ⟨sSup s, hs.symm⟩
  · exact Or.inr <| Or.inl <| Or.inr ⟨sSup s, hs.symm⟩
  · exact Or.inr <| Or.inr <| Or.inl hs
  · exact Or.inr <| Or.inr <| Or.inr hs
#align set_of_is_preconnected_subset_of_ordered setOf_isPreconnected_subset_of_ordered

/-!
### Intervals are connected

In this section we prove that a closed interval (hence, any `ord_connected` set) in a dense
conditionally complete linear order is preconnected.
-/


/-- A "continuous induction principle" for a closed interval: if a set `s` meets `[a, b]`
on a closed subset, contains `a`, and the set `s ∩ [a, b)` has no maximal point, then `b ∈ s`. -/
theorem IsClosed.mem_of_ge_of_forall_exists_gt {a b : α} {s : Set α} (hs : IsClosed (s ∩ Icc a b))
    (ha : a ∈ s) (hab : a ≤ b) (hgt : ∀ x ∈ s ∩ Ico a b, (s ∩ Ioc x b).Nonempty) : b ∈ s := by
  let S := s ∩ Icc a b
  replace ha : a ∈ S
  exact ⟨ha, left_mem_Icc.2 hab⟩
  have Sbd : BddAbove S := ⟨b, fun z hz => hz.2.2⟩
  let c := sSup (s ∩ Icc a b)
  have c_mem : c ∈ S := hs.csSup_mem ⟨_, ha⟩ Sbd
  have c_le : c ≤ b := csSup_le ⟨_, ha⟩ fun x hx => hx.2.2
  cases' eq_or_lt_of_le c_le with hc hc
  exact hc ▸ c_mem.1
  exfalso
  rcases hgt c ⟨c_mem.1, c_mem.2.1, hc⟩ with ⟨x, xs, cx, xb⟩
  exact not_lt_of_le (le_csSup Sbd ⟨xs, le_trans (le_csSup Sbd ha) (le_of_lt cx), xb⟩) cx
#align is_closed.mem_of_ge_of_forall_exists_gt IsClosed.mem_of_ge_of_forall_exists_gt

/-- A "continuous induction principle" for a closed interval: if a set `s` meets `[a, b]`
on a closed subset, contains `a`, and for any `a ≤ x < y ≤ b`, `x ∈ s`, the set `s ∩ (x, y]`
is not empty, then `[a, b] ⊆ s`. -/
theorem IsClosed.Icc_subset_of_forall_exists_gt {a b : α} {s : Set α} (hs : IsClosed (s ∩ Icc a b))
    (ha : a ∈ s) (hgt : ∀ x ∈ s ∩ Ico a b, ∀ y ∈ Ioi x, (s ∩ Ioc x y).Nonempty) : Icc a b ⊆ s := by
  intro y hy
  have : IsClosed (s ∩ Icc a y) := by
    suffices s ∩ Icc a y = s ∩ Icc a b ∩ Icc a y by
      rw [this]
      exact IsClosed.inter hs isClosed_Icc
    rw [inter_assoc]
    congr
    exact (inter_eq_self_of_subset_right <| Icc_subset_Icc_right hy.2).symm
  exact
    IsClosed.mem_of_ge_of_forall_exists_gt this ha hy.1 fun x hx =>
      hgt x ⟨hx.1, Ico_subset_Ico_right hy.2 hx.2⟩ y hx.2.2
#align is_closed.Icc_subset_of_forall_exists_gt IsClosed.Icc_subset_of_forall_exists_gt

variable [DenselyOrdered α] {a b : α}

/-- A "continuous induction principle" for a closed interval: if a set `s` meets `[a, b]`
on a closed subset, contains `a`, and for any `x ∈ s ∩ [a, b)` the set `s` includes some open
neighborhood of `x` within `(x, +∞)`, then `[a, b] ⊆ s`. -/
theorem IsClosed.Icc_subset_of_forall_mem_nhdsWithin {a b : α} {s : Set α}
    (hs : IsClosed (s ∩ Icc a b)) (ha : a ∈ s) (hgt : ∀ x ∈ s ∩ Ico a b, s ∈ 𝓝[>] x) :
    Icc a b ⊆ s := by
  apply hs.Icc_subset_of_forall_exists_gt ha
  rintro x ⟨hxs, hxab⟩ y hyxb
  have : s ∩ Ioc x y ∈ 𝓝[>] x :=
    inter_mem (hgt x ⟨hxs, hxab⟩) (Ioc_mem_nhdsWithin_Ioi ⟨le_rfl, hyxb⟩)
  exact (nhdsWithin_Ioi_self_neBot' ⟨b, hxab.2⟩).nonempty_of_mem this
#align is_closed.Icc_subset_of_forall_mem_nhds_within IsClosed.Icc_subset_of_forall_mem_nhdsWithin

theorem isPreconnected_Icc_aux (x y : α) (s t : Set α) (hxy : x ≤ y) (hs : IsClosed s)
    (ht : IsClosed t) (hab : Icc a b ⊆ s ∪ t) (hx : x ∈ Icc a b ∩ s) (hy : y ∈ Icc a b ∩ t) :
    (Icc a b ∩ (s ∩ t)).Nonempty := by
  have xyab : Icc x y ⊆ Icc a b := Icc_subset_Icc hx.1.1 hy.1.2
  by_contra hst
  suffices : Icc x y ⊆ s
  exact hst ⟨y, xyab <| right_mem_Icc.2 hxy, this <| right_mem_Icc.2 hxy, hy.2⟩
  apply (IsClosed.inter hs isClosed_Icc).Icc_subset_of_forall_mem_nhdsWithin hx.2
  rintro z ⟨zs, hz⟩
  have zt : z ∈ tᶜ := fun zt => hst ⟨z, xyab <| Ico_subset_Icc_self hz, zs, zt⟩
  have : tᶜ ∩ Ioc z y ∈ 𝓝[>] z := by
    rw [← nhdsWithin_Ioc_eq_nhdsWithin_Ioi hz.2]
    exact mem_nhdsWithin.2 ⟨tᶜ, ht.isOpen_compl, zt, Subset.rfl⟩
  apply mem_of_superset this
  have : Ioc z y ⊆ s ∪ t := fun w hw => hab (xyab ⟨le_trans hz.1 (le_of_lt hw.1), hw.2⟩)
  exact fun w ⟨wt, wzy⟩ => (this wzy).elim id fun h => (wt h).elim
#align is_preconnected_Icc_aux isPreconnected_Icc_aux

/-- A closed interval in a densely ordered conditionally complete linear order is preconnected. -/
theorem isPreconnected_Icc : IsPreconnected (Icc a b) :=
  isPreconnected_closed_iff.2
    (by
      rintro s t hs ht hab ⟨x, hx⟩ ⟨y, hy⟩
      -- This used to use `wlog`, but it was causing timeouts.
      cases' le_total x y with h h
      · exact isPreconnected_Icc_aux x y s t h hs ht hab hx hy
      · rw [inter_comm s t]
        rw [union_comm s t] at hab
        exact isPreconnected_Icc_aux y x t s h ht hs hab hy hx)
#align is_preconnected_Icc isPreconnected_Icc

theorem isPreconnected_uIcc : IsPreconnected (uIcc a b) :=
  isPreconnected_Icc
#align is_preconnected_uIcc isPreconnected_uIcc

theorem Set.OrdConnected.isPreconnected {s : Set α} (h : s.OrdConnected) : IsPreconnected s :=
  isPreconnected_of_forall_pair fun x hx y hy =>
    ⟨uIcc x y, h.uIcc_subset hx hy, left_mem_uIcc, right_mem_uIcc, isPreconnected_uIcc⟩
#align set.ord_connected.is_preconnected Set.OrdConnected.isPreconnected

theorem isPreconnected_iff_ordConnected {s : Set α} : IsPreconnected s ↔ OrdConnected s :=
  ⟨IsPreconnected.ordConnected, Set.OrdConnected.isPreconnected⟩
#align is_preconnected_iff_ord_connected isPreconnected_iff_ordConnected

theorem isPreconnected_Ici : IsPreconnected (Ici a) :=
  ordConnected_Ici.isPreconnected
#align is_preconnected_Ici isPreconnected_Ici

theorem isPreconnected_Iic : IsPreconnected (Iic a) :=
  ordConnected_Iic.isPreconnected
#align is_preconnected_Iic isPreconnected_Iic

theorem isPreconnected_Iio : IsPreconnected (Iio a) :=
  ordConnected_Iio.isPreconnected
#align is_preconnected_Iio isPreconnected_Iio

theorem isPreconnected_Ioi : IsPreconnected (Ioi a) :=
  ordConnected_Ioi.isPreconnected
#align is_preconnected_Ioi isPreconnected_Ioi

theorem isPreconnected_Ioo : IsPreconnected (Ioo a b) :=
  ordConnected_Ioo.isPreconnected
#align is_preconnected_Ioo isPreconnected_Ioo

theorem isPreconnected_Ioc : IsPreconnected (Ioc a b) :=
  ordConnected_Ioc.isPreconnected
#align is_preconnected_Ioc isPreconnected_Ioc

theorem isPreconnected_Ico : IsPreconnected (Ico a b) :=
  ordConnected_Ico.isPreconnected
#align is_preconnected_Ico isPreconnected_Ico

theorem isConnected_Ici : IsConnected (Ici a) :=
  ⟨nonempty_Ici, isPreconnected_Ici⟩
#align is_connected_Ici isConnected_Ici

theorem isConnected_Iic : IsConnected (Iic a) :=
  ⟨nonempty_Iic, isPreconnected_Iic⟩
#align is_connected_Iic isConnected_Iic

theorem isConnected_Ioi [NoMaxOrder α] : IsConnected (Ioi a) :=
  ⟨nonempty_Ioi, isPreconnected_Ioi⟩
#align is_connected_Ioi isConnected_Ioi

theorem isConnected_Iio [NoMinOrder α] : IsConnected (Iio a) :=
  ⟨nonempty_Iio, isPreconnected_Iio⟩
#align is_connected_Iio isConnected_Iio

theorem isConnected_Icc (h : a ≤ b) : IsConnected (Icc a b) :=
  ⟨nonempty_Icc.2 h, isPreconnected_Icc⟩
#align is_connected_Icc isConnected_Icc

theorem isConnected_Ioo (h : a < b) : IsConnected (Ioo a b) :=
  ⟨nonempty_Ioo.2 h, isPreconnected_Ioo⟩
#align is_connected_Ioo isConnected_Ioo

theorem isConnected_Ioc (h : a < b) : IsConnected (Ioc a b) :=
  ⟨nonempty_Ioc.2 h, isPreconnected_Ioc⟩
#align is_connected_Ioc isConnected_Ioc

theorem isConnected_Ico (h : a < b) : IsConnected (Ico a b) :=
  ⟨nonempty_Ico.2 h, isPreconnected_Ico⟩
#align is_connected_Ico isConnected_Ico

instance (priority := 100) ordered_connected_space : PreconnectedSpace α :=
  ⟨ordConnected_univ.isPreconnected⟩
#align ordered_connected_space ordered_connected_space

/-- In a dense conditionally complete linear order, the set of preconnected sets is exactly
the set of the intervals `Icc`, `Ico`, `Ioc`, `Ioo`, `Ici`, `Ioi`, `Iic`, `Iio`, `(-∞, +∞)`,
or `∅`. Though one can represent `∅` as `(sInf s, sInf s)`, we include it into the list of
possible cases to improve readability. -/
theorem setOf_isPreconnected_eq_of_ordered :
    { s : Set α | IsPreconnected s } =
      -- bounded intervals
      range (uncurry Icc) ∪ range (uncurry Ico) ∪ range (uncurry Ioc) ∪ range (uncurry Ioo) ∪
      -- unbounded intervals and `univ`
      (range Ici ∪ range Ioi ∪ range Iic ∪ range Iio ∪ {univ, ∅}) := by
  refine' Subset.antisymm setOf_isPreconnected_subset_of_ordered _
  simp only [subset_def, forall_range_iff, uncurry, or_imp, forall_and, mem_union,
    mem_setOf_eq, insert_eq, mem_singleton_iff, forall_eq, forall_true_iff, and_true_iff,
    isPreconnected_Icc, isPreconnected_Ico, isPreconnected_Ioc, isPreconnected_Ioo,
    isPreconnected_Ioi, isPreconnected_Iio, isPreconnected_Ici, isPreconnected_Iic,
    isPreconnected_univ, isPreconnected_empty]
#align set_of_is_preconnected_eq_of_ordered setOf_isPreconnected_eq_of_ordered

/-!
### Intermediate Value Theorem on an interval

In this section we prove several versions of the Intermediate Value Theorem for a function
continuous on an interval.
-/


variable {δ : Type*} [LinearOrder δ] [TopologicalSpace δ] [OrderClosedTopology δ]

/-- **Intermediate Value Theorem** for continuous functions on closed intervals, case
`f a ≤ t ≤ f b`.-/
theorem intermediate_value_Icc {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (Icc a b)) :
    Icc (f a) (f b) ⊆ f '' Icc a b :=
  isPreconnected_Icc.intermediate_value (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hf
#align intermediate_value_Icc intermediate_value_Icc

/-- **Intermediate Value Theorem** for continuous functions on closed intervals, case
`f a ≥ t ≥ f b`.-/
theorem intermediate_value_Icc' {a b : α} (hab : a ≤ b) {f : α → δ}
    (hf : ContinuousOn f (Icc a b)) : Icc (f b) (f a) ⊆ f '' Icc a b :=
  isPreconnected_Icc.intermediate_value (right_mem_Icc.2 hab) (left_mem_Icc.2 hab) hf
#align intermediate_value_Icc' intermediate_value_Icc'

/-- **Intermediate Value Theorem** for continuous functions on closed intervals, unordered case. -/
theorem intermediate_value_uIcc {a b : α} {f : α → δ} (hf : ContinuousOn f (uIcc a b)) :
    uIcc (f a) (f b) ⊆ f '' uIcc a b := by
  cases le_total (f a) (f b) <;> simp [*, isPreconnected_uIcc.intermediate_value]
#align intermediate_value_uIcc intermediate_value_uIcc

theorem intermediate_value_Ico {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (Icc a b)) :
    Ico (f a) (f b) ⊆ f '' Ico a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he _ h => absurd h.2 (not_lt_of_le (he ▸ h.1))) fun hlt =>
    @IsPreconnected.intermediate_value_Ico _ _ _ _ _ _ _ isPreconnected_Ico _ _ ⟨refl a, hlt⟩
      (right_nhdsWithin_Ico_neBot hlt) inf_le_right _ (hf.mono Ico_subset_Icc_self) _
      ((hf.continuousWithinAt ⟨hab, refl b⟩).mono Ico_subset_Icc_self)
#align intermediate_value_Ico intermediate_value_Ico

theorem intermediate_value_Ico' {a b : α} (hab : a ≤ b) {f : α → δ}
    (hf : ContinuousOn f (Icc a b)) : Ioc (f b) (f a) ⊆ f '' Ico a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he _ h => absurd h.1 (not_lt_of_le (he ▸ h.2))) fun hlt =>
    @IsPreconnected.intermediate_value_Ioc _ _ _ _ _ _ _ isPreconnected_Ico _ _ ⟨refl a, hlt⟩
      (right_nhdsWithin_Ico_neBot hlt) inf_le_right _ (hf.mono Ico_subset_Icc_self) _
      ((hf.continuousWithinAt ⟨hab, refl b⟩).mono Ico_subset_Icc_self)
#align intermediate_value_Ico' intermediate_value_Ico'

theorem intermediate_value_Ioc {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (Icc a b)) :
    Ioc (f a) (f b) ⊆ f '' Ioc a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he _ h => absurd h.2 (not_le_of_lt (he ▸ h.1))) fun hlt =>
    @IsPreconnected.intermediate_value_Ioc _ _ _ _ _ _ _ isPreconnected_Ioc _ _ ⟨hlt, refl b⟩
      (left_nhdsWithin_Ioc_neBot hlt) inf_le_right _ (hf.mono Ioc_subset_Icc_self) _
      ((hf.continuousWithinAt ⟨refl a, hab⟩).mono Ioc_subset_Icc_self)
#align intermediate_value_Ioc intermediate_value_Ioc

theorem intermediate_value_Ioc' {a b : α} (hab : a ≤ b) {f : α → δ}
    (hf : ContinuousOn f (Icc a b)) : Ico (f b) (f a) ⊆ f '' Ioc a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he _ h => absurd h.1 (not_le_of_lt (he ▸ h.2))) fun hlt =>
    @IsPreconnected.intermediate_value_Ico _ _ _ _ _ _ _ isPreconnected_Ioc _ _ ⟨hlt, refl b⟩
      (left_nhdsWithin_Ioc_neBot hlt) inf_le_right _ (hf.mono Ioc_subset_Icc_self) _
      ((hf.continuousWithinAt ⟨refl a, hab⟩).mono Ioc_subset_Icc_self)
#align intermediate_value_Ioc' intermediate_value_Ioc'

theorem intermediate_value_Ioo {a b : α} (hab : a ≤ b) {f : α → δ} (hf : ContinuousOn f (Icc a b)) :
    Ioo (f a) (f b) ⊆ f '' Ioo a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he _ h => absurd h.2 (not_lt_of_lt (he ▸ h.1))) fun hlt =>
    @IsPreconnected.intermediate_value_Ioo _ _ _ _ _ _ _ isPreconnected_Ioo _ _
      (left_nhdsWithin_Ioo_neBot hlt) (right_nhdsWithin_Ioo_neBot hlt) inf_le_right inf_le_right _
      (hf.mono Ioo_subset_Icc_self) _ _
      ((hf.continuousWithinAt ⟨refl a, hab⟩).mono Ioo_subset_Icc_self)
      ((hf.continuousWithinAt ⟨hab, refl b⟩).mono Ioo_subset_Icc_self)
#align intermediate_value_Ioo intermediate_value_Ioo

theorem intermediate_value_Ioo' {a b : α} (hab : a ≤ b) {f : α → δ}
    (hf : ContinuousOn f (Icc a b)) : Ioo (f b) (f a) ⊆ f '' Ioo a b :=
  Or.elim (eq_or_lt_of_le hab) (fun he _ h => absurd h.1 (not_lt_of_lt (he ▸ h.2))) fun hlt =>
    @IsPreconnected.intermediate_value_Ioo _ _ _ _ _ _ _ isPreconnected_Ioo _ _
      (right_nhdsWithin_Ioo_neBot hlt) (left_nhdsWithin_Ioo_neBot hlt) inf_le_right inf_le_right _
      (hf.mono Ioo_subset_Icc_self) _ _
      ((hf.continuousWithinAt ⟨hab, refl b⟩).mono Ioo_subset_Icc_self)
      ((hf.continuousWithinAt ⟨refl a, hab⟩).mono Ioo_subset_Icc_self)
#align intermediate_value_Ioo' intermediate_value_Ioo'

/-- **Intermediate value theorem**: if `f` is continuous on an order-connected set `s` and `a`,
`b` are two points of this set, then `f` sends `s` to a superset of `Icc (f x) (f y)`. -/
theorem ContinuousOn.surjOn_Icc {s : Set α} [hs : OrdConnected s] {f : α → δ}
    (hf : ContinuousOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) : SurjOn f s (Icc (f a) (f b)) :=
  hs.isPreconnected.intermediate_value ha hb hf
#align continuous_on.surj_on_Icc ContinuousOn.surjOn_Icc

/-- **Intermediate value theorem**: if `f` is continuous on an order-connected set `s` and `a`,
`b` are two points of this set, then `f` sends `s` to a superset of `[f x, f y]`. -/
theorem ContinuousOn.surjOn_uIcc {s : Set α} [hs : OrdConnected s] {f : α → δ}
    (hf : ContinuousOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) : SurjOn f s (uIcc (f a) (f b)) :=
  by cases' le_total (f a) (f b) with hab hab <;> simp [hf.surjOn_Icc, *]
#align continuous_on.surj_on_uIcc ContinuousOn.surjOn_uIcc

/-- A continuous function which tendsto `Filter.atTop` along `Filter.atTop` and to `atBot` along
`at_bot` is surjective. -/
theorem Continuous.surjective {f : α → δ} (hf : Continuous f) (h_top : Tendsto f atTop atTop)
    (h_bot : Tendsto f atBot atBot) : Function.Surjective f := fun p =>
  mem_range_of_exists_le_of_exists_ge hf (h_bot.eventually (eventually_le_atBot p)).exists
    (h_top.eventually (eventually_ge_atTop p)).exists
#align continuous.surjective Continuous.surjective

/-- A continuous function which tendsto `Filter.atBot` along `Filter.atTop` and to `Filter.atTop`
along `atBot` is surjective. -/
theorem Continuous.surjective' {f : α → δ} (hf : Continuous f) (h_top : Tendsto f atBot atTop)
    (h_bot : Tendsto f atTop atBot) : Function.Surjective f :=
  @Continuous.surjective αᵒᵈ _ _ _ _ _ _ _ _ _ hf h_top h_bot
#align continuous.surjective' Continuous.surjective'

/-- If a function `f : α → β` is continuous on a nonempty interval `s`, its restriction to `s`
tends to `at_bot : Filter β` along `at_bot : Filter ↥s` and tends to `Filter.atTop : Filter β` along
`Filter.atTop : Filter ↥s`, then the restriction of `f` to `s` is surjective. We formulate the
conclusion as `Function.surjOn f s Set.univ`. -/
theorem ContinuousOn.surjOn_of_tendsto {f : α → δ} {s : Set α} [OrdConnected s] (hs : s.Nonempty)
    (hf : ContinuousOn f s) (hbot : Tendsto (fun x : s => f x) atBot atBot)
    (htop : Tendsto (fun x : s => f x) atTop atTop) : SurjOn f s univ :=
  haveI := Classical.inhabited_of_nonempty hs.to_subtype
  surjOn_iff_surjective.2 <| hf.restrict.surjective htop hbot
#align continuous_on.surj_on_of_tendsto ContinuousOn.surjOn_of_tendsto

/-- If a function `f : α → β` is continuous on a nonempty interval `s`, its restriction to `s`
tends to `Filter.atTop : Filter β` along `Filter.atBot : Filter ↥s` and tends to
`Filter.atBot : Filter β` along `Filter.atTop : Filter ↥s`, then the restriction of `f` to `s` is
surjective. We formulate the conclusion as `Function.surjOn f s Set.univ`. -/
theorem ContinuousOn.surjOn_of_tendsto' {f : α → δ} {s : Set α} [OrdConnected s] (hs : s.Nonempty)
    (hf : ContinuousOn f s) (hbot : Tendsto (fun x : s => f x) atBot atTop)
    (htop : Tendsto (fun x : s => f x) atTop atBot) : SurjOn f s univ :=
  @ContinuousOn.surjOn_of_tendsto α _ _ _ _ δᵒᵈ _ _ _ _ _ _ hs hf hbot htop
#align continuous_on.surj_on_of_tendsto' ContinuousOn.surjOn_of_tendsto'

/-- Suppose f : [a, b] → δ is continuous and injective. Then f is strictly monotone.
Here is the case where f is strictly increasing. -/
theorem continuous_inj_is_monotone_Icc {a b : α} {f : α → δ} (h1 : a < b) (h2 : f a < f b)
    (p1 : ContinuousOn f (Icc a b)) (p2 : InjOn f (Icc a b)) :
    StrictMonoOn f (Icc a b) := by
-- I learned this proof from
-- <https://www.math.cuhk.edu.hk/course_builder/2021/math1050b/1050b-l14h-3.pdf>
  unfold StrictMonoOn
  intro s hs t ht h3
  have h4 : f s ≠ f t := by
    by_contra'
    have : s = t := p2 hs ht this
    rw [this] at h3
    exact LT.lt.false h3
  by_contra' h5
  have h6 : f t < f s := Ne.lt_of_le (id (Ne.symm h4)) h5
  by_cases h7 : f s ≤ f a
  · have h9 : Icc t b ⊆ Icc a b := Icc_subset_Icc_left ht.1
    have p3 : ContinuousOn f (Icc t b) := ContinuousOn.mono p1 h9
    have h10 := intermediate_value_Ioo ht.2 p3
    have h11 : f a ∈ Ioo (f t) (f b) := ⟨(LT.lt.trans_le h6 h7), h2⟩
    have h12 : f a ∈ f '' Ioo t b := h10 h11
    choose u hu using h12
    have h13 : u = a :=
      p2 (h9 (Ioo_subset_Icc_self hu.1)) (left_mem_Icc.mpr (le_of_lt h1)) hu.2
    have h14 : a < u := lt_of_lt_of_le' hu.1.1 ht.1
    rw [h13] at h14
    exact LT.lt.false h14
  · have h8 : a < t := lt_of_lt_of_le' h3 hs.1
    have h9 : f a ≠ f t := by
      by_contra' this
      have : a = t := p2 (left_mem_Icc.mpr (le_of_lt h1)) ht this
      rw [this] at h8
      exact LT.lt.false h8
    by_cases h10 : f a < f t
    · have h11 : Icc a s ⊆ Icc a b := Icc_subset_Icc_right hs.2
      have p3 : ContinuousOn f (Icc a s) := ContinuousOn.mono p1 h11
      have h12 := intermediate_value_Ioo hs.1 p3
      have h13 : f t ∈ Ioo (f a) (f s) := ⟨h10, h6⟩
      choose u hu using h12 h13
      have h14 : u = t := p2 (h11 (Ioo_subset_Icc_self hu.1)) ht hu.2
      have h15 : u < t := lt_trans hu.1.2 h3
      rw [h14] at h15
      exact LT.lt.false h15
    · push_neg at h10
      have h11 : f t < f a := Ne.lt_of_le (id (Ne.symm h9)) h10
      have h12 : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
      have p3 : ContinuousOn f (Icc s t) := ContinuousOn.mono p1 h12
      push_neg at h7
      have h13 := intermediate_value_Ioo' (le_of_lt h3) p3
      have h14 : f a ∈ Ioo (f t) (f s) := ⟨h11, h7⟩
      choose u hu using h13 h14
      have h15 : u = a :=
        p2 (h12 (Ioo_subset_Icc_self hu.1)) (left_mem_Icc.mpr (le_of_lt h1)) hu.2
      have h16 : a < u := lt_of_lt_of_le' hu.1.1 hs.1
      rw [h15] at h16
      exact LT.lt.false h16
/-- Suppose f : [a, b] → δ is continuous and injective. Then f is strictly monotone.
Here is the case where f is strictly decreasing. -/
theorem continuous_inj_is_monotone_Icc' {a b : α} {f : α → δ} (h1 : a < b) (h2 : f b < f a)
    (p1 : ContinuousOn f (Icc a b)) (p2 : InjOn f (Icc a b)) :
    StrictAntiOn f (Icc a b) := by
    let g (x : α) : OrderDual δ := f x
    have h2' : g a < g b := h2
    have p1' : ContinuousOn g (Icc a b) := p1
    have p2' : InjOn g (Icc a b) := p2
    exact continuous_inj_is_monotone_Icc h1 h2' p1' p2'
/-- Suppose f : [a, b] → δ is continuous and injective. Then f is strictly monotone.-/
theorem continuous_inj_is_monotone_Icc'' {a b : α} {f : α → δ} (h1 : a < b)
    (p1 : ContinuousOn f (Icc a b)) (p2 : InjOn f (Icc a b)) :
    StrictMonoOn f (Icc a b) ∨ StrictAntiOn f (Icc a b) := by
  by_cases h2 : f a < f b
  · exact Or.inl (continuous_inj_is_monotone_Icc h1 h2 p1 p2)
  · have ha : a ∈ Icc a b := left_mem_Icc.mpr (le_of_lt h1)
    have hb : b ∈ Icc a b := right_mem_Icc.mpr (le_of_lt h1)
    have h3 : f a ≠ f b := (InjOn.ne_iff p2 ha hb).mpr (ne_of_lt h1)
    push_neg at h2
    have h4 : f b < f a := Ne.lt_of_le (id (Ne.symm h3)) h2
    exact Or.inr (continuous_inj_is_monotone_Icc' h1 h4 p1 p2)

/-- This lemma is only used to
prove and will be immediately superseded by
`continuous_inj_is_monotone_Ioo` below.
It asserts that a continuous injective `f: (a, b) → δ` must be strictly monotone on
every closed interval `[c, d] ⊆ (a, b)`.-/
private lemma continuous_inj_is_monotone_Ioo_H1 {a b : α} {f : α → δ}
    (p1 : ContinuousOn f (Ioo a b)) (p2 : InjOn f (Ioo a b))
    {c d : α} (h2 : c ∈ Ioo a b) (h3 : d ∈ Ioo a b) (h4 : c < d) :
    StrictMonoOn f (Icc c d) ∨ StrictAntiOn f (Icc c d) := by
  have h5 : Icc c d ⊆ Ioo a b := Set.Icc_subset (Ioo a b) h2 h3
  have h6 : ContinuousOn f (Icc c d) := ContinuousOn.mono p1 h5
  have h7 : InjOn f (Icc c d) := InjOn.mono h5 p2
  exact continuous_inj_is_monotone_Icc'' h4 h6 h7
/-- This lemma is only used to
prove and will be immediately superseded by
`continuous_inj_is_monotone_Ioo` below.
It asserts that a continuous injective `f: (a, b) → δ` is strictly increasing if
it is strictly increasing on some closed interval `[c, d] ⊆ (a, b)`.-/
private lemma continuous_inj_is_monotone_Ioo_H2 {a b : α} {f : α → δ}
    {c d : α} (hc : c ∈ Ioo a b) (hd : d ∈ Ioo a b) (hcd : c < d)
    (p1 : ContinuousOn f (Ioo a b)) (p2 : InjOn f (Ioo a b))
    (h5 : StrictMonoOn f (Icc c d)) : StrictMonoOn f (Ioo a b) := by
  unfold StrictMonoOn
  intro x hx y hy hxy
  let s := min c x
  let t := max d y
  have hsc : s ≤ c := min_le_left c x
  have hdt : d ≤ t := le_max_left d y
  have hs : s ∈ Ioo a b := ⟨lt_min hc.1 hx.1, min_lt_of_left_lt hc.2⟩
  have ht : t ∈ Ioo a b := ⟨lt_max_of_lt_right hy.1, max_lt hd.2 hy.2⟩
  have hst : s < t := lt_of_le_of_lt hsc (lt_of_lt_of_le hcd hdt)
  have h6 : Icc c d ⊆ Icc s t := Icc_subset_Icc hsc hdt
  have h7 : StrictMonoOn f (Icc s t) ∨ StrictAntiOn f (Icc s t) := 
    continuous_inj_is_monotone_Ioo_H1 p1 p2 hs ht hst
  have h8' : StrictAntiOn f (Icc s t) → False := by
    intro h7
    have h9 : StrictAntiOn f (Icc c d) := StrictAntiOn.mono h7 h6
    have hcd' : c ≤ d := LT.lt.le hcd
    have hc : c ∈ Icc c d := Iff.mpr left_mem_Icc hcd'
    have hd : d ∈ Icc c d := Iff.mpr right_mem_Icc hcd'
    have hcd_1 : f c < f d := h5 hc hd hcd
    have hcd_2 : f d < f c := h9 hc hd hcd
    have : f c < f c := lt_trans hcd_1 hcd_2
    exact LT.lt.false this
  have h8 : StrictMonoOn f (Icc s t) := by tauto
  have hsx : s ≤ x := min_le_right c x
  have hyt : y ≤ t := le_max_right d y
  have h9 : Icc x y ⊆ Icc s t := Icc_subset_Icc hsx hyt
  have h10 : StrictMonoOn f (Icc x y) := StrictMonoOn.mono h8 h9
  exact h10 (left_mem_Icc.mpr (le_of_lt hxy)) (right_mem_Icc.mpr (le_of_lt hxy)) hxy
/-- Every continuous injective `f: (a, b) → δ` is strictly monotone.-/
theorem continuous_inj_is_monotone_Ioo {a b : α} {f : α → δ} (h1 : a < b)
    (p1 : ContinuousOn f (Ioo a b)) (p2 : InjOn f (Ioo a b)) :
    StrictMonoOn f (Ioo a b) ∨ StrictAntiOn f (Ioo a b) := by
  have h3 : (Ioo a b).Nonempty := Iff.mpr nonempty_Ioo h1
  choose c hc using h3
  have h4 : (Ioo c b).Nonempty := Iff.mpr nonempty_Ioo hc.2
  choose d hd' using h4
  have hcd : c < d := hd'.1
  have hd : d ∈ Ioo a b := ⟨lt_trans hc.1 hcd, hd'.2⟩
  have h5 : StrictMonoOn f (Icc c d) ∨ StrictAntiOn f (Icc c d) :=
    continuous_inj_is_monotone_Ioo_H1 p1 p2 hc hd hcd
  have h5_1 := continuous_inj_is_monotone_Ioo_H2 hc hd hcd p1 p2
  have h5_2 (h5 : StrictAntiOn f (Icc c d)) : StrictAntiOn f (Ioo a b) := by
    let g (x : α) : OrderDual δ := f x
    have hg' : StrictMonoOn g (Ioo a b) := continuous_inj_is_monotone_Ioo_H2 hc hd hcd p1 p2 h5
    exact hg'
  tauto
