import Mathlib.Order.Filter.Germ.Star
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

import Mathlib.MeasureTheory.OuterMeasure.Caratheodory
import Mathlib.MeasureTheory.OuterMeasure.OfFunction
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Measure.Content
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Order.Filter.Ultrafilter.Nonstandard
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.MeasureTheory.OuterMeasure.OfAddContent
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Pairwise
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option linter.style.multiGoal false
set_option linter.style.emptyLine false


open Finset
open Classical
open Ultrafilter
open scoped BigOperators
open MeasureTheory

attribute [local instance] Classical.propDecidable

/-!
# Loeb Measure Construction - Roadmap

This file outlines the Loeb measure construction for connecting hyperfinite
combinatorics to standard measure theory.
-/

namespace Hyper

open scoped NonstandardAnalysis ENNReal
open MeasureTheory
open Set
open Filter

variable {ι : Type*} [Infinite ι] {α : Type*}

/-! ## Internal Counting Measure -/

section InternalMeasure

/-- The cardinality of an internal subset of a hyperfinite set. -/
noncomputable def hyperfiniteSubsetCard
    (H : Set (Hyper ι α)) (hH : IsHyperfinite H)
    (A : Set (Hyper ι α)) (hA : IsInternal A) : Hyper ι ℕ :=
  hyperfiniteCard (A ∩ H) (hA.inter_isHyperfinite hH)

/-- The internal counting measure of an internal set A relative to H. -/
noncomputable def internalCountingMeasure
    (H : Set (Hyper ι α)) (hH : IsHyperfinite H) [Infinite ι]
    (A : Set (Hyper ι α)) (hA : IsInternal A) : Hyper ι ℝ :=
  let num := Hyper.lift (Nat.cast : ℕ → ℝ) (hyperfiniteSubsetCard H hH A hA)
  let den := Hyper.lift (Nat.cast : ℕ → ℝ) (hyperfiniteCard H hH)
  num / den

end InternalMeasure

/-! ## NearStandard Helper Section -/

section NearStandard

variable {x y : Hyper ι ℝ} {r s : ℝ}

lemma IsNearStandard_iff_forall_epsilon (x : Hyper ι ℝ) (r : ℝ) :
    x ≈ r ↔ ∀ ε > 0, (Hyper.std (r - ε) < x) ∧ (x < Hyper.std (r + ε)) := by
  have : (x ≈ r) ↔ IsNearStandard x r := Iff.rfl
  rw [this]
  rw [Hyper.isNearStandard_def]
  constructor
  · intro h ε hε
    have : Ioo (r - ε) (r + ε) ∈ nhds r := Ioo_mem_nhds (sub_lt_self r hε) (lt_add_of_pos_right r hε)
    have h_mem := h _ this
    rw [Hyper.mem_star_Ioo] at h_mem
    exact h_mem
  · intro h U hU
    rw [Metric.mem_nhds_iff] at hU
    obtain ⟨ε, hε, sub⟩ := hU
    have := h ε hε
    rw [← Hyper.mem_star_Ioo] at this
    rw [Real.ball_eq_Ioo] at sub
    exact (Hyper.star_mono sub) this


lemma IsNearStandard_add (hx : x ≈ r) (hy : y ≈ s) : x + y ≈ r + s := by
  rw [IsNearStandard_iff_forall_epsilon] at *
  intro ε hε
  have hε2 : ε / 2 > 0 := by linarith
  have hx := hx _ hε2
  have hy := hy _ hε2
  simp only [Filter.Germ.coe_add, Filter.Germ.coe_neg] at *
  constructor
  · have : r + s + -ε = (r + -(ε/2)) + (s + -(ε/2)) := by ring
    rw [sub_eq_add_neg, this]
    rw [Hyper.std_add]
    exact add_lt_add hx.1 hy.1
  · have : r + s + ε = (r + ε/2) + (s + ε/2) := by ring
    rw [this]
    rw [Hyper.std_add]
    exact add_lt_add hx.2 hy.2





lemma IsFinite_sum {β : Type*} {s : Finset β} {f : β → Hyper ι ℝ} (hf : ∀ b ∈ s, Hyper.IsFinite (f b)) :
    Hyper.IsFinite (∑ b ∈ s, f b) := by
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    use 0, 0
    rw [Hyper.std_zero]
    exact ⟨le_refl _, le_refl _⟩
  | insert a s' ha ih =>
    simp only [Finset.sum_insert ha]
    apply Hyper.IsFinite.add
    · exact hf a (Finset.mem_insert_self a s')
    · apply ih
      intro b hb
      exact hf b (Finset.mem_insert_of_mem hb)

lemma st_sum {β : Type*} {s : Finset β} {f : β → Hyper ι ℝ} (hf : ∀ b ∈ s, Hyper.IsFinite (f b)) :
    Hyper.st (∑ b ∈ s, f b) = ∑ b ∈ s, Hyper.st (f b) := by
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty]; exact st_std (ι := ι) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [st_add_real]
    · rw [ih]
      intro b hb; exact hf b (Finset.mem_insert_of_mem hb)
    · exact hf a (Finset.mem_insert_self a s)
    · apply IsFinite_sum
      intro b hb; exact hf b (Finset.mem_insert_of_mem hb)



lemma isFinite_of_le_one {x : Hyper ι ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : Hyper.IsFinite x := by
  rw [Hyper.IsFinite_iff_abs_le]
  use 1
  rw [abs_of_nonneg h0]
  exact h1

theorem st_nonneg {x : Hyper ι ℝ} (h_fin : Hyper.IsFinite x) (hx : 0 ≤ x) : 0 ≤ Hyper.st x := by
  rw [← st_std (ι := ι) 0]
  apply st_mono (ι := ι)
  · exact isNearStandard_st _ (IsStandard.isFinite ⟨0, rfl⟩)
  · exact isNearStandard_st _ h_fin
  · exact hx


theorem st_zero_eq_zero : Hyper.st (0 : Hyper ι ℝ) = 0 := by
  apply st_eq_of_isNearStandard
  -- Prove 0 \approx 0
  have : (0 : Hyper ι ℝ) ≈ (0 : ℝ) := by
    rw [Hyper.isNearStandard_def]
    intro U hU
    rw [Metric.mem_nhds_iff] at hU
    obtain ⟨ε, hε, sub⟩ := hU
    apply (Hyper.star_mono sub)
    rw [Real.ball_eq_Ioo]
    rw [Hyper.mem_star_Ioo]
    rw [← Set.mem_Ioo]
    constructor
    · rw [← Hyper.std_zero]
      rw [Hyper.std_lt_std]
      linarith
    · rw [← Hyper.std_zero]
      rw [Hyper.std_lt_std]
      linarith
  exact this

end NearStandard

/-! ## Loeb Measure -/

section LoebMeasure

set_option linter.unusedSectionVars false
variable [Nonempty α]

/-- The collection of internal sets forms a Boolean algebra. -/
def InternalAlgebra : Set (Set (Hyper ι α)) := { A | IsInternal A }

theorem isSetRing_InternalAlgebra : IsSetRing (@InternalAlgebra ι _ α) := {
  empty_mem := isInternal_empty
  union_mem := fun A B hA hB => IsInternal.union hA hB
  diff_mem := fun A B hA hB => IsInternal.diff hA hB
}

attribute [local instance] isSetRing_InternalAlgebra

theorem hyperfiniteCard_empty (H : Set (Hyper ι α)) (hH : IsHyperfinite H) (h : H = ∅) :
    hyperfiniteCard H hH = 0 := by
  dsimp [hyperfiniteCard]
  let S := hH.choose
  have hS_mem := hH.choose_spec.2
  have h_empty_ae : ∀ᶠ i in nonstandardUltrafilter ι, S i = ∅ := by
    by_contra h_freq
    have h_ne_ae : ∀ᶠ i in nonstandardUltrafilter ι, S i ≠ ∅ :=
      Ultrafilter.compl_mem_iff_notMem.mpr h_freq
    let f := fun i => if h : (S i).Nonempty then h.some else Classical.choice (by infer_instance)
    have hf : ∀ᶠ i in nonstandardUltrafilter ι, f i ∈ S i := by
       filter_upwards [h_ne_ae] with i hi
       have : (S i).Nonempty := Set.nonempty_iff_ne_empty.mpr hi
       simp only [f, dif_pos this]
       exact Classical.choose_spec this
    have h_in : (Hyper.ofSeq f) ∈ H := by
       rw [hS_mem]
       change liftPredSeq (fun i y ↦ y ∈ S i) (Hyper.ofSeq f)
       rw [Hyper.liftPredSeq_ofSeq]
       exact hf
    rw [h] at h_in
    exact h_in
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [h_empty_ae] with i hi
  apply Finset.card_eq_zero.mpr
  apply Set.Finite.toFinset_eq_empty.mpr
  exact hi

theorem hyperfiniteCard_pos_iff_nonempty {H : Set (Hyper ι α)} (hH : IsHyperfinite H) :
    0 < hyperfiniteCard H hH ↔ H.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  constructor
  · intro h h_empty
    rw [hyperfiniteCard_empty H hH h_empty] at h
    exact lt_irrefl 0 h
  · intro h_ne
    dsimp [hyperfiniteCard]
    let S := hH.choose
    have hS_mem := hH.choose_spec.2
    obtain ⟨x_germ, hx_germ⟩ := Set.nonempty_iff_ne_empty.mpr h_ne
    -- Unpack Hyper.ofSeq f \in H -> f =ae[L] y, y \in S.
    induction x_germ using Filter.Germ.inductionOn with | _ f =>
    rw [hS_mem] at hx_germ
    change liftPredSeq (fun i y ↦ y ∈ S i) (Hyper.ofSeq f) at hx_germ
    rw [Hyper.liftPredSeq_ofSeq] at hx_germ
    -- hx_germ : ∀ᶠ i, f i \in S i
    change 0 < Hyper.ofSeq (fun i => (hH.choose_spec.1 i).toFinset.card)
    rw [Hyper.lt_def]
    filter_upwards [hx_germ] with i hi
    -- hi : f i \in S i
    simp only [Nat.cast_zero, Finset.card_pos, Set.Finite.toFinset_nonempty]
    exact ⟨f i, hi⟩

/-- The pre-Loeb measure of an internal set. -/
noncomputable def preLoebMeasure
    (H : Set (Hyper ι α)) (hH : IsHyperfinite H)
    (A : Set (Hyper ι α)) : ENNReal :=
  if hA : IsInternal A then
    ENNReal.ofReal (Hyper.st (internalCountingMeasure H hH A hA))
  else
    ∞

theorem preLoebMeasure_empty (H : Set (Hyper ι α)) (hH : IsHyperfinite H) :
    preLoebMeasure H hH ∅ = 0 := by
  dsimp [preLoebMeasure, internalCountingMeasure, hyperfiniteSubsetCard]
  simp only [isInternal_empty, dif_pos]
  have h_card : hyperfiniteCard (∅ ∩ H) (IsInternal.inter_isHyperfinite isInternal_empty hH) = 0 := by
    apply hyperfiniteCard_empty
    simp only [Set.empty_inter]


  have zero_cast_eq : (0 : Hyper ι ℕ).map (Nat.cast : ℕ → ℝ) = 0 := by
    change (Filter.Germ.const 0).map (Nat.cast : ℕ → ℝ) = 0
    erw [Filter.Germ.map_const]
    rw [Nat.cast_zero]
    rfl
  have h_frac_zero : (0 : Hyper ι ℝ).map₂ Div.div ((hyperfiniteCard H hH).map (Nat.cast : ℕ → ℝ)) = 0 := by
    let x : Germ (nonstandardUltrafilter ι : Filter ι) ℕ := hyperfiniteCard H hH
    change (0 : Hyper ι ℝ).map₂ Div.div (x.map Nat.cast) = 0
    induction x using Filter.Germ.inductionOn with
    | h f =>
    rw [Filter.Germ.map_coe, ← Filter.Germ.coe_zero, Filter.Germ.map₂_coe]
    apply Filter.Germ.coe_eq.2
    filter_upwards
    intro i
    dsimp
    have : Div.div (0 : ℝ) (Nat.cast (f i)) = 0 / (Nat.cast (f i)) := rfl
    rw [this, zero_div]
  rw [h_card]
  change ENNReal.ofReal (Hyper.st (((0 : Hyper ι ℕ).map (Nat.cast : ℕ → ℝ)).map₂ Div.div ((hyperfiniteCard H hH).map Nat.cast))) = 0
  rw [zero_cast_eq, h_frac_zero, Hyper.st_zero_eq_zero, ENNReal.ofReal_zero]

theorem hyperfiniteCard_congr {A B : Set (Hyper ι α)} (hA : IsHyperfinite A) (hB : IsHyperfinite B) (h : A = B) :
    hyperfiniteCard A hA = hyperfiniteCard B hB := by
  subst h
  rfl

variable {l : Filter α}

theorem Filter.Germ.map_add {M N} [Add M] [Add N] (f : M → N) (hf : ∀ x y, f (x + y) = f x + f y)
    (x y : Filter.Germ l M) : Filter.Germ.map f (x + y) = Filter.Germ.map f x + Filter.Germ.map f y := by
  induction x using Filter.Germ.inductionOn
  induction y using Filter.Germ.inductionOn
  simp only [Filter.Germ.map_coe]
  apply Filter.Germ.coe_eq.mpr
  filter_upwards with a
  simp only [Function.comp_apply, hf, Filter.Germ.coe_add]

theorem hyperfiniteSubsetCard_union {H : Set (Hyper ι α)} (hH : IsHyperfinite H)
    {A B : Set (Hyper ι α)} (hA : IsInternal A) (hB : IsInternal B) (h_dis : Disjoint A B) :
    hyperfiniteSubsetCard H hH (A ∪ B) (IsInternal.union hA hB) =
    hyperfiniteSubsetCard H hH A hA + hyperfiniteSubsetCard H hH B hB := by
  dsimp [hyperfiniteSubsetCard, hyperfiniteCard]
  let hAB := (IsInternal.union hA hB).inter_isHyperfinite hH
  let hA' := hA.inter_isHyperfinite hH
  let hB' := hB.inter_isHyperfinite hH
  let SA := hA'.choose
  let SB := hB'.choose
  let SAB := hAB.choose
  apply Filter.Germ.coe_eq.mpr

  -- Transfer extensionality lemma
  have h_internal_ext : ∀ (S T : ι → Set α),
      (∀ x, liftPredSeq (fun i y => y ∈ S i) x ↔ liftPredSeq (fun i y => y ∈ T i) x) →
      {i | S i = T i} ∈ nonstandardUltrafilter ι := by
    intro S T h_eq
    by_contra h_bad
    have h_freq : {i | S i ≠ T i} ∈ nonstandardUltrafilter ι := Ultrafilter.compl_mem_iff_notMem.mpr h_bad
    -- let f := fun i =>
    --   if h : S i ≠ T i
    --   then (Set.nonempty_iff_ne_empty.mpr (mt Set.symmDiff_eq_simp.mp h)).some
    --   else Classical.choice (by infer_instance)
    let f := fun i => Classical.epsilon (fun y => y ∈ symmDiff (S i) (T i))
    have hf_prop : ∀ᶠ i in nonstandardUltrafilter ι, f i ∈ symmDiff (S i) (T i) := by
      filter_upwards [h_freq] with i hi
      exact Classical.epsilon_spec (Set.nonempty_iff_ne_empty.mpr (mt Set.symmDiff_eq_empty.mp hi))
    let x := Hyper.ofSeq f
    have h_diff : liftPredSeq (fun i y => y ∈ S i) x ↔ ¬ liftPredSeq (fun i y => y ∈ T i) x := by
      change liftPredSeq (fun i y => y ∈ S i) (Hyper.ofSeq f) ↔ ¬ liftPredSeq (fun i y => y ∈ T i) (Hyper.ofSeq f)
      have h_rw : liftPredSeq (fun i y => y ∈ S i) (Hyper.ofSeq f) ↔ ∀ᶠ i in nonstandardUltrafilter ι, f i ∈ S i :=
        Hyper.liftPredSeq_ofSeq _ _
      have h_rw2 : liftPredSeq (fun i y => y ∈ T i) (Hyper.ofSeq f) ↔ ∀ᶠ i in nonstandardUltrafilter ι, f i ∈ T i :=
        Hyper.liftPredSeq_ofSeq _ _
      rw [h_rw, h_rw2]
      have h_iff : ∀ᶠ i in nonstandardUltrafilter ι, f i ∈ S i ↔ f i ∉ T i := by
        filter_upwards [hf_prop] with i hi
        simp [Set.mem_symmDiff] at hi
        tauto
      rw [Filter.eventually_congr h_iff]
      rw [Ultrafilter.eventually_not]

    simp only [h_eq x] at h_diff
    tauto

  -- Use h_internal_ext for h_eq_ae
  have h_eq_ae : {i | SAB i = SA i ∪ SB i} ∈ nonstandardUltrafilter ι := by
    apply h_internal_ext
    intro x
    -- RHS is x \in (A U B) \cap H
    rw [← (hAB.choose_spec.2 x)]
    rw [Set.union_inter_distrib_right]
    rw [Set.mem_union]
    rw [(hA'.choose_spec.2 x)]
    rw [(hB'.choose_spec.2 x)]
    induction x using Filter.Germ.inductionOn with | _ f
    change liftPredSeq (fun i y ↦ y ∈ SA i) (Hyper.ofSeq f) ∨ liftPredSeq (fun i y ↦ y ∈ SB i) (Hyper.ofSeq f) ↔
      liftPredSeq (fun i y ↦ y ∈ SA i ∪ SB i) (Hyper.ofSeq f)

    have h1 : liftPredSeq (fun i y => y ∈ SA i) (Hyper.ofSeq f) ↔ ∀ᶠ i in nonstandardUltrafilter ι, f i ∈ SA i := Hyper.liftPredSeq_ofSeq _ _
    have h2 : liftPredSeq (fun i y => y ∈ SB i) (Hyper.ofSeq f) ↔ ∀ᶠ i in nonstandardUltrafilter ι, f i ∈ SB i := Hyper.liftPredSeq_ofSeq _ _
    have h3 : liftPredSeq (fun i y => y ∈ SA i ∪ SB i) (Hyper.ofSeq f) ↔ ∀ᶠ i in nonstandardUltrafilter ι, f i ∈ SA i ∪ SB i := Hyper.liftPredSeq_ofSeq _ _
    rw [h1, h2, h3]

    -- Use Ultrafilter property
    change (∀ᶠ i in nonstandardUltrafilter ι, f i ∈ SA i) ∨ (∀ᶠ i in nonstandardUltrafilter ι, f i ∈ SB i) ↔
           {i | f i ∈ SA i ∪ SB i} ∈ nonstandardUltrafilter ι
    have h_set_eq : {i | f i ∈ SA i ∪ SB i} = {i | f i ∈ SA i} ∪ {i | f i ∈ SB i} := by ext; simp
    rw [h_set_eq, Ultrafilter.union_mem_iff]
    rfl

  have h_dis_ae : {i | Disjoint (SA i) (SB i)} ∈ nonstandardUltrafilter ι := by
    have h_inter_empty : {i | SA i ∩ SB i = ∅} ∈ nonstandardUltrafilter ι := by
      apply h_internal_ext
      intro x
      induction x using Filter.Germ.inductionOn with | _ f =>
      change liftPredSeq (fun i y ↦ y ∈ SA i ∩ SB i) (Hyper.ofSeq f) ↔ liftPredSeq (fun i y ↦ y ∈ ∅) (Hyper.ofSeq f)
      rw [Hyper.liftPredSeq_ofSeq, Hyper.liftPredSeq_ofSeq]
      constructor
      · intro h

        have h_mem : Hyper.ofSeq f ∈ (A ∩ H) ∩ (B ∩ H) := by
             rw [Set.mem_inter_iff]
             constructor
             · have h_iff := hA'.choose_spec.2 (Hyper.ofSeq f)
               change Hyper.ofSeq f ∈ A ∩ H
               erw [h_iff]
               erw [Hyper.liftPredSeq_ofSeq]
               filter_upwards [h] with j hj using hj.1
             · have h_iff := hB'.choose_spec.2 (Hyper.ofSeq f)
               change Hyper.ofSeq f ∈ B ∩ H
               erw [h_iff]
               erw [Hyper.liftPredSeq_ofSeq]
               filter_upwards [h] with j hj using hj.2
        have h_dis_H : Disjoint (A ∩ H) (B ∩ H) := h_dis.mono Set.inter_subset_left Set.inter_subset_left
        rw [Set.disjoint_iff_inter_eq_empty.mp h_dis_H] at h_mem
        exact (Set.notMem_empty _ h_mem).elim
      · intro h
        simp only [Set.mem_empty_iff_false] at h
        exfalso
        exact (nonstandardUltrafilter ι).neBot.ne (Filter.eventually_false_iff_eq_bot.mp h)

    filter_upwards [h_inter_empty] with i hi
    exact Set.disjoint_iff_inter_eq_empty.mpr hi

  let h_fin_SA := hA'.choose_spec.1
  let h_fin_SB := hB'.choose_spec.1
  let h_fin_SAB := hAB.choose_spec.1
  filter_upwards [h_eq_ae, h_dis_ae] with i hi_eq hi_disj

  -- Explicitly construct proof of set equality
  have h_set_eq : SAB i = SA i ∪ SB i := hi_eq
  have h_fin_eq : Set.Finite.toFinset (h_fin_SAB i) = Set.Finite.toFinset ((h_fin_SA i).union (h_fin_SB i)) := by
    apply Finset.ext
    intro x
    rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    change x ∈ SAB i ↔ x ∈ SA i ∪ SB i
    rw [h_set_eq]


  rw [h_fin_eq]
  rw [Set.Finite.toFinset_union (h_fin_SA i) (h_fin_SB i)]
  have h_dis_fin : Disjoint (Set.Finite.toFinset (h_fin_SA i)) (Set.Finite.toFinset (h_fin_SB i)) := by
    classical
    rw [Finset.disjoint_iff_inter_eq_empty]
    rw [← Set.Finite.toFinset_inter (h_fin_SA i) (h_fin_SB i)]
    · rw [Set.Finite.toFinset_eq_empty]
      exact Set.disjoint_iff_inter_eq_empty.mp hi_disj
    · exact (h_fin_SA i).subset Set.inter_subset_left
  rw [Finset.card_union_of_disjoint h_dis_fin]
  rfl

theorem hyperfiniteSubsetCard_le {H : Set (Hyper ι α)} (hH : IsHyperfinite H)
    {A : Set (Hyper ι α)} (hA : IsInternal A) :
    hyperfiniteSubsetCard H hH A hA ≤ hyperfiniteCard H hH := by
  dsimp [hyperfiniteSubsetCard, hyperfiniteCard]
  let hAH := hA.inter_isHyperfinite hH
  let SAH := hAH.choose
  let SH := hH.choose
  apply Filter.Germ.coe_le.mpr
  have h_ae_sub : {i | SAH i ⊆ SH i} ∈ nonstandardUltrafilter ι := by
    -- Same extraction logic
    have h_internal_ext_sub : ∀ (S T : ι → Set α),
      (∀ x, liftPredSeq (fun i y => y ∈ S i) x → liftPredSeq (fun i y => y ∈ T i) x) →
      {i | S i ⊆ T i} ∈ nonstandardUltrafilter ι := by
        intro S T h_imp
        by_contra h_bad
        have h_freq : {i | ¬ S i ⊆ T i} ∈ nonstandardUltrafilter ι := Ultrafilter.compl_mem_iff_notMem.mpr h_bad
        -- Simplify to epsilon for robustness
        let f := fun i => Classical.epsilon (fun y => y ∈ S i ∧ y ∉ T i)
        have h_choose : ∀ i, ¬ S i ⊆ T i → f i ∈ S i ∧ f i ∉ T i := fun i hi =>
            Classical.epsilon_spec (Set.not_subset.mp hi)

        have hf_def : ∀ᶠ i in nonstandardUltrafilter ι, f i ∈ S i ∧ f i ∉ T i := by
          filter_upwards [h_freq] with i hi
          exact h_choose i hi
        let x := Hyper.ofSeq f
        have h_in : liftPredSeq (fun i y => y ∈ S i) x := by
           change liftPredSeq (fun i y => y ∈ S i) (Hyper.ofSeq f)
           have h_rw : liftPredSeq (fun i y => y ∈ S i) (Hyper.ofSeq f) ↔ ∀ᶠ i in nonstandardUltrafilter ι, f i ∈ S i :=
             Hyper.liftPredSeq_ofSeq _ _
           rw [h_rw]
           apply Filter.mem_of_superset hf_def
           intro i hi; exact hi.1
        have h_notin : ¬ liftPredSeq (fun i y => y ∈ T i) x := by
           change ¬ liftPredSeq (fun i y => y ∈ T i) (Hyper.ofSeq f)
           have h_rw : liftPredSeq (fun i y => y ∈ T i) (Hyper.ofSeq f) ↔ ∀ᶠ i in nonstandardUltrafilter ι, f i ∈ T i :=
             Hyper.liftPredSeq_ofSeq _ _
           rw [h_rw]
           intro h_true
           apply (nonstandardUltrafilter ι).neBot.ne
           apply Filter.empty_mem_iff_bot.mp
           apply Filter.mem_of_superset (Filter.inter_mem hf_def h_true)
           intro i hi
           exact hi.1.2 hi.2
        exact h_notin (h_imp x h_in)
    apply h_internal_ext_sub
    intro x hx
    rw [← hAH.choose_spec.2] at hx
    rw [← hH.choose_spec.2 (x := x)]
    exact Set.mem_of_mem_inter_right hx

  let h_fin_SAH := hAH.choose_spec.1
  let h_fin_SH := hH.choose_spec.1
  filter_upwards [h_ae_sub] with i hi
  apply Finset.card_le_card
  have h_sub : (h_fin_SAH i).toFinset ⊆ (h_fin_SH i).toFinset := by
    apply Iff.mpr Set.Finite.toFinset_subset_toFinset
    exact hi
  exact h_sub

theorem internalCountingMeasure_nonneg {H : Set (Hyper ι α)} (hH : IsHyperfinite H)
    {A : Set (Hyper ι α)} (hA : IsInternal A) :
    0 ≤ internalCountingMeasure H hH A hA := by
  dsimp [internalCountingMeasure]
  apply div_nonneg
  · apply Filter.Germ.coe_le.mpr; filter_upwards; intro i; exact Nat.cast_nonneg _
  · apply Filter.Germ.coe_le.mpr; filter_upwards; intro i; exact Nat.cast_nonneg _

theorem internalCountingMeasure_le_one {H : Set (Hyper ι α)} (hH : IsHyperfinite H)
    {A : Set (Hyper ι α)} (hA : IsInternal A) :
    internalCountingMeasure H hH A hA ≤ 1 := by
  dsimp [internalCountingMeasure]
  have h_le := hyperfiniteSubsetCard_le hH hA
  apply Filter.Germ.coe_le.mpr
  filter_upwards [Filter.Germ.coe_le.mp h_le] with i h_le_i
  by_cases hc : (hH.choose_spec.1 i).toFinset.card = 0
  · simp [hc, Nat.cast_zero, div_zero, zero_le_one]
  · have h_pos : 0 < ((hH.choose_spec.1 i).toFinset.card : ℝ) := by
      rw [Nat.cast_pos]
      exact Nat.pos_of_ne_zero hc
    apply (div_le_one h_pos).mpr
    refine (@Nat.cast_le ℝ _ _ _).mpr h_le_i

theorem internalCountingMeasure_union {H : Set (Hyper ι α)} (hH : IsHyperfinite H)
    {A B : Set (Hyper ι α)} (hA : IsInternal A) (hB : IsInternal B) (h_dis : Disjoint A B) :
    internalCountingMeasure H hH (A ∪ B) (IsInternal.union hA hB) =
    internalCountingMeasure H hH A hA + internalCountingMeasure H hH B hB := by
  dsimp [internalCountingMeasure, Hyper.lift] -- Expose map
  rw [hyperfiniteSubsetCard_union hH hA hB h_dis]
  -- Now we have map cast (card A + card B) ...
  rw [Filter.Germ.map_add Nat.cast Nat.cast_add]
  rw [add_div]

theorem preLoebMeasure_union {H : Set (Hyper ι α)} (hH : IsHyperfinite H)
    {A B : Set (Hyper ι α)} (hA : IsInternal A) (hB : IsInternal B) (h_dis : Disjoint A B) :
    preLoebMeasure H hH (A ∪ B) = preLoebMeasure H hH A + preLoebMeasure H hH B := by
  dsimp [preLoebMeasure]
  rw [dif_pos (IsInternal.union hA hB), dif_pos hA, dif_pos hB]
  let μ := internalCountingMeasure H hH
  have h_union : μ (A ∪ B) (IsInternal.union hA hB) = μ A hA + μ B hB :=
    internalCountingMeasure_union hH hA hB h_dis
  -- Add finiteness proofs for st_nonneg
  have h_fin_A : Hyper.IsFinite (μ A hA) := isFinite_of_le_one (internalCountingMeasure_nonneg hH hA) (internalCountingMeasure_le_one hH hA)
  have h_fin_B : Hyper.IsFinite (μ B hB) := isFinite_of_le_one (internalCountingMeasure_nonneg hH hB) (internalCountingMeasure_le_one hH hB)
  rw [← ENNReal.ofReal_add (st_nonneg h_fin_A (internalCountingMeasure_nonneg hH hA)) (st_nonneg h_fin_B (internalCountingMeasure_nonneg hH hB))]
  congr 1
  rw [← st_add_real (μ A hA) (μ B hB) h_fin_A h_fin_B]
  exact congr_arg Hyper.st h_union

/-- The pre-Loeb content. -/
noncomputable def preLoebContent (H : Set (Hyper ι α)) (hH : IsHyperfinite H) : MeasureTheory.AddContent (@InternalAlgebra ι _ α) :=
  IsSetRing.addContent_of_union (preLoebMeasure H hH) isSetRing_InternalAlgebra (preLoebMeasure_empty H hH)
    (fun hA hB h_dis => preLoebMeasure_union hH hA hB h_dis)

/-- The Loeb outer measure. -/
noncomputable def loebOuterMeasure (H : Set (Hyper ι α)) (hH : IsHyperfinite H) :
    OuterMeasure (Hyper ι α) :=
  MeasureTheory.inducedOuterMeasure (fun s _ => (preLoebContent H hH) s) (IsSetRing.isSetSemiring isSetRing_InternalAlgebra).empty_mem (preLoebMeasure_empty H hH)

/-- The Loeb σ-algebra. -/
def loebMeasurableSet (H : Set (Hyper ι α)) (hH : IsHyperfinite H) : MeasurableSpace (Hyper ι α) :=
  (loebOuterMeasure H hH).caratheodory

/-- All internal sets are Loeb measurable. -/
theorem isInternal_loebMeasurable (H : Set (Hyper ι α)) (hH : IsHyperfinite H)
    (A : Set (Hyper ι α)) (hA : IsInternal A) :
    (loebOuterMeasure H hH).IsCaratheodory A :=
  MeasureTheory.AddContent.isCaratheodory_inducedOuterMeasure_of_mem (IsSetRing.isSetSemiring isSetRing_InternalAlgebra)
    (preLoebContent H hH)
    hA

/-- Lift a standard function to an internal function (constant sequence). -/
noncomputable def liftFun {α β : Type*} (f : α → β) : Hyper ι (α → β) :=
  Hyper.ofSeq (fun _ => f)

/-- The Loeb measure. -/
noncomputable def loebMeasure (H : Set (Hyper ι α)) (hH : IsHyperfinite H) : @Measure (Hyper ι α) (loebMeasurableSet H hH) :=
  @MeasureTheory.OuterMeasure.toMeasure (Hyper ι α) (loebMeasurableSet H hH) (loebOuterMeasure H hH) le_rfl

/-- Internal sum of an internal function over a hyperfinite set. -/
noncomputable def internalSum (H : Set (Hyper ι α)) (hH : IsHyperfinite H)
    (f : Hyper ι (α → ℝ)) : Hyper ι ℝ :=
  let hS_fin := hH.choose_spec.1
  let finsets : ι → Finset α := fun i => (hS_fin i).toFinset
  Hyper.lift₂ (fun (s : Finset α) (g : α → ℝ) => ∑ x ∈ s, g x) (Hyper.ofSeq finsets) f


/-- The standard part function is Loeb measurable. -/
theorem st_loebMeasurable (H : Set (Hyper ι ℝ)) (hH : IsHyperfinite H) :
    @Measurable (Hyper ι ℝ) ℝ (loebMeasurableSet H hH) _ Hyper.st := by
  sorry

/-- The Loeb measure of an internal set is the standard part of its internal measure. -/
theorem loebMeasure_internal (H : Set (Hyper ι α)) (hH : IsHyperfinite H)
    (A : Set (Hyper ι α)) (hA : IsInternal A) :
    loebMeasure H hH A = ENNReal.ofReal (Hyper.st (internalCountingMeasure H hH A hA)) := by
  dsimp [loebMeasure]
  let m := loebMeasurableSet H hH
  have h_meas : @MeasurableSet (Hyper ι α) m A := isInternal_loebMeasurable H hH A hA
  rw [toMeasure_apply _ _ h_meas]
  sorry -- Depends on sigma-additivity of pre-measure (saturation) and induced measure property

/-- The Loeb measure is finite. -/
theorem loebMeasure_univ_finite (H : Set (Hyper ι α)) (hH : IsHyperfinite H) :
    loebMeasure H hH Set.univ < ⊤ :=
  sorry

/-- Integration of an indicator function over Loeb measure. -/
theorem loebIntegral_indicator (H : Set (Hyper ι α)) (hH : IsHyperfinite H)
    (A : Set (Hyper ι α)) (hA : IsInternal A) :
    letI m := loebMeasurableSet H hH
    ∫ x, indicator A (fun _ => (1 : ℝ)) x ∂(loebMeasure H hH) =
      Hyper.st (internalCountingMeasure H hH A hA) := by
  have h_meas := isInternal_loebMeasurable H hH A hA
  rw [@integral_indicator _ _ (loebMeasurableSet H hH) _ _ _ A (loebMeasure H hH) h_meas]
  rw [integral_const, smul_eq_mul, mul_one]
  · unfold Measure.real
    have h_eq : (loebMeasure H hH).restrict A Set.univ = loebMeasure H hH A := sorry
    rw [h_eq]
    rw [loebMeasure_internal H hH A hA]
    rw [ENNReal.toReal_ofReal]
    · apply Hyper.st_nonneg
      · apply isFinite_of_le_one
        · exact internalCountingMeasure_nonneg hH hA
        · exact internalCountingMeasure_le_one hH hA
      · exact internalCountingMeasure_nonneg hH hA

/-- Integration of a simple function over Loeb measure. -/
theorem loebIntegral_simple_eq_sum (H : Set (Hyper ι α)) (hH : IsHyperfinite H)
    [m : MeasurableSpace (Hyper ι α)] (hm : m = loebMeasurableSet H hH)
    (f : SimpleFunc (Hyper ι α) ℝ) (hf_int : ∀ x, IsInternal {y | f y = x}) :
    ∫ x, f x ∂(loebMeasure H hH) =
      Hyper.st (∑ r ∈ f.range, Hyper.std r * internalCountingMeasure H hH {y | f y = r} (hf_int r)) := by
  letI : MeasurableSpace (Hyper ι α) := m
  subst hm
  have hfi : Integrable f (loebMeasure H hH) := by
    -- Every simple function on a finite measure space is integrable.
    sorry
  calc ∫ x, f x ∂(loebMeasure H hH)
    _ = ∑ r ∈ f.range, (loebMeasure H hH).real (f ⁻¹' {r}) * r := by
      rw [SimpleFunc.integral_eq_sum f hfi]
      simp only [smul_eq_mul]
    _ = ∑ r ∈ f.range, Hyper.st (internalCountingMeasure H hH {y | f y = r} (hf_int r)) * r := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Measure.real]
      erw [loebMeasure_internal H hH _ (hf_int r)]
      rw [ENNReal.toReal_ofReal]
      let val := internalCountingMeasure H hH {y | f y = r} (hf_int r)
      have h_le : val ≤ 1 := internalCountingMeasure_le_one hH (hf_int r)
      have h_nn : 0 ≤ val := internalCountingMeasure_nonneg hH (hf_int r)
      have h_fin : IsFinite val := isFinite_of_le_one h_nn h_le
      apply Hyper.st_nonneg h_fin h_nn
    _ = Hyper.st (∑ r ∈ f.range, Hyper.std r * internalCountingMeasure H hH {y | f y = r} (hf_int r)) := by
      rw [st_sum]
      · congr
        ext r
        rw [mul_comm, Hyper.st_std_mul]
        apply isFinite_of_le_one (internalCountingMeasure_nonneg hH (hf_int r)) (internalCountingMeasure_le_one hH (hf_int r))
      · intro r _
        apply Hyper.IsFinite.mul ⟨r, r, le_refl _, le_refl _⟩
        apply isFinite_of_le_one (internalCountingMeasure_nonneg hH (hf_int r)) (internalCountingMeasure_le_one hH (hf_int r))

/-- Key Lemma: Integration of standard functions.
For a standard bounded function `f`, the integral against Loeb measure is the standard part
of the internal sum. This is a simplified version focusing on the core equality.

Note: This requires α to have the appropriate structure for `st` to be defined.
For now, we specialize to ℝ. -/
theorem loebIntegral_eq_st_hyperSum
    (H : Set (Hyper ι ℝ)) (hH : IsHyperfinite H)
    (f : ℝ → ℝ) (hf_bound : ∃ C, ∀ x, |f x| ≤ C) (hf_cont : Continuous f) :
    ∫ x, f (Hyper.st x) ∂(loebMeasure H hH) =
      Hyper.st (internalSum H hH (Hyper.liftFun f) /
        Hyper.lift (Nat.cast : ℕ → ℝ) (hyperfiniteCard H hH)) := by
  -- 1. Approximate f by simple functions g_n
  -- 2. Use loebIntegral_simple_eq_sum for g_n
  -- 3. Take limits
  sorry

end LoebMeasure

end Hyper

noncomputable instance {ι : Type*} [Infinite ι] {α : Type*}
    [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] :
    IsOrderedAddMonoid (Hyper ι α) where
  add_le_add_left := by
      intro a b h c
      induction a using Filter.Germ.inductionOn with | _ fa =>
      induction b using Filter.Germ.inductionOn with | _ fb =>
      induction c using Filter.Germ.inductionOn with | _ fc =>
      apply Filter.Germ.coe_le.mpr
      filter_upwards [Filter.Germ.coe_le.mp h] with i hi
      exact add_le_add_left hi (fc i)

noncomputable instance {ι : Type*} [Infinite ι] {α : Type*}
    [AddCommMonoid α] [PartialOrder α] [CanonicallyOrderedAdd α] :
    CanonicallyOrderedAdd (Hyper ι α) where
  exists_add_of_le := by
      intro a b h
      induction a using Filter.Germ.inductionOn with | _ fa =>
      induction b using Filter.Germ.inductionOn with | _ fb =>
      revert h
      intro h_le
      let S := {i | fa i ≤ fb i}
      have hS : S ∈ nonstandardUltrafilter ι := Filter.Germ.coe_le.mp h_le
      let c := fun i => if hi : i ∈ S then (exists_add_of_le (a := fa i) (b := fb i) hi).choose else 0
      use Hyper.ofSeq c
      apply Filter.Germ.coe_eq.mpr
      filter_upwards [hS] with i hi
      simp only [c, dif_pos hi]
      exact (exists_add_of_le (a := fa i) (b := fb i) hi).choose_spec
  le_self_add := by
      intro a b
      induction a using Filter.Germ.inductionOn with | _ fa =>
      induction b using Filter.Germ.inductionOn with | _ fb =>
      apply Filter.Germ.coe_le.mpr
      filter_upwards with i
      exact le_self_add
  le_add_self := by
      intro a b
      induction a using Filter.Germ.inductionOn with | _ fa =>
      induction b using Filter.Germ.inductionOn with | _ fb =>
      apply Filter.Germ.coe_le.mpr
      filter_upwards with i
      exact le_add_self
