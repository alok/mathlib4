/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Probability.Notation
import Mathlib.Probability.ConditionalProbability

/-!
# Entropy and conditional entropy

## Main definitions

* `measureEntropy`: entropy of a measure
* `entropy`: entropy of a random variable, defined as `measureEntropy (volume.map X)`
* `condEntropy`: conditional entropy of a random variable `X` w.r.t. another one `Y`

## Main statements

* `chain_rule`: `entropy (fun ω ↦ (X ω, Y ω)) = entropy Y + condEntropy X Y`

-/

open Real MeasureTheory

open scoped ENNReal NNReal Topology ProbabilityTheory BigOperators

section x_log_x

/-! Properties of the function `x ↦ x * log x`. -/

namespace Real

lemma tendsto_log_mul_nhds_zero_left :
    Filter.Tendsto (fun x ↦ log x * x) (𝓝[<] 0) (𝓝 0) := by
  have h := tendsto_log_mul_rpow_nhds_zero zero_lt_one
  simp only [rpow_one] at h
  have h_eq : ∀ x ∈ Set.Iio 0, (- (fun x ↦ log x * x) ∘ (fun x ↦ |x|)) x = log x * x := by
    intro x hx
    simp only [Set.mem_Iio] at hx
    simp only [Pi.neg_apply, Function.comp_apply, log_abs]
    rw [abs_of_nonpos hx.le]
    simp only [mul_neg, neg_neg]
  refine tendsto_nhdsWithin_congr h_eq ?_
  rw [← neg_zero]
  refine Filter.Tendsto.neg ?_
  simp only [neg_zero]
  refine h.comp ?_
  refine tendsto_abs_nhdsWithin_zero.mono_left ?_
  refine nhdsWithin_mono 0 (fun x hx ↦ ?_)
  simp only [Set.mem_Iio] at hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hx.ne, not_false_eq_true]

lemma continuous_id_mul_log : Continuous (fun x ↦ x * log x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  swap; · exact (continuous_id'.continuousAt).mul (continuousAt_log hx)
  rw [hx]
  have h := tendsto_log_mul_rpow_nhds_zero zero_lt_one
  simp only [rpow_one] at h
  have h' : Filter.Tendsto (fun x ↦ log x * x) (𝓝[<] 0) (𝓝 0) := tendsto_log_mul_nhds_zero_left
  rw [ContinuousAt, zero_mul]
  suffices Filter.Tendsto (fun x ↦ log x * x) (𝓝 0) (𝓝 0) by
    exact this.congr (fun x ↦ by rw [mul_comm])
  nth_rewrite 1 [← nhdsWithin_univ]
  have : (Set.univ : Set ℝ) = Set.Iio 0 ∪ Set.Ioi 0 ∪ {0} := by
    ext x
    simp only [Set.mem_univ, Set.Iio_union_Ioi, Set.union_singleton, Set.mem_compl_iff,
      Set.mem_singleton_iff, not_true, Set.mem_insert_iff, true_iff]
    exact em _
  rw [this, nhdsWithin_union, nhdsWithin_union]
  simp only [ge_iff_le, nhdsWithin_singleton, sup_le_iff, Filter.nonpos_iff, Filter.tendsto_sup]
  refine ⟨⟨h', h⟩, ?_⟩
  rw [Filter.tendsto_pure_left, mul_zero]
  intro s hs
  obtain ⟨t, hts, _, h_zero_mem⟩ := mem_nhds_iff.mp hs
  exact hts h_zero_mem

lemma differentiableOn_id_mul_log : DifferentiableOn ℝ (fun x ↦ x * log x) {0}ᶜ :=
  differentiable_id'.differentiableOn.mul differentiableOn_log

lemma deriv_id_mul_log {x : ℝ} (hx : x ≠ 0) : deriv (fun x ↦ x * log x) x = log x + 1 := by
  rw [deriv_mul differentiableAt_id' (differentiableAt_log hx)]
  simp only [deriv_id'', one_mul, deriv_log', ne_eq, add_right_inj]
  exact mul_inv_cancel hx

lemma deriv2_id_mul_log {x : ℝ} (hx : x ≠ 0) : deriv^[2] (fun x ↦ x * log x) x = x⁻¹ := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp.left_id,
    Function.comp_apply]
  suffices ∀ᶠ y in (𝓝 x), deriv (fun x ↦ x * log x) y = log y + 1 by
    refine (Filter.EventuallyEq.deriv_eq this).trans ?_
    rw [deriv_add_const, deriv_log x]
  suffices ∀ᶠ y in (𝓝 x), y ≠ 0 by
    filter_upwards [this] with y hy
    exact deriv_id_mul_log hy
  exact eventually_ne_nhds hx

lemma strictConvexOn_id_mul_log : StrictConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x ↦ x * log x) := by
  refine strictConvexOn_of_deriv2_pos (convex_Ici 0) (continuous_id_mul_log.continuousOn) ?_
  intro x hx
  simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at hx
  rw [deriv2_id_mul_log hx.ne']
  positivity

lemma convexOn_id_mul_log : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x ↦ x * log x) :=
  strictConvexOn_id_mul_log.convexOn

lemma id_mul_log_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ x * log x :=
  mul_nonneg (zero_le_one.trans hx) (log_nonneg hx)

@[measurability]
lemma measurable_id_mul_log : Measurable (fun x ↦ x * log x) :=
  measurable_id'.mul measurable_log

end Real

section aux_lemmas

-- todo: is this somewhere?
lemma integral_eq_sum {S E : Type*} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
     (μ : Measure S) [IsFiniteMeasure μ] (f : S → E) :
    ∫ x, f x ∂μ = ∑ x, (μ {x}).toReal • (f x) := by
  conv_lhs => rw [← Measure.sum_smul_dirac μ]
  have hf : Integrable f μ := integrable_of_fintype _ _
  have hf' : Integrable f (Measure.sum fun a ↦ μ {a} • Measure.dirac a) := by
    rwa [Measure.sum_smul_dirac μ]
  rw [integral_sum_measure hf']
  simp_rw [integral_smul_measure, integral_dirac]
  rw [tsum_fintype]

/-- `μ[|s]` is a finite measure whenever `μ` is finite. -/
instance cond_isFiniteMeasure {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [IsFiniteMeasure μ] (s : Set α) :
    IsFiniteMeasure (μ[|s]) := by
  constructor
  rw [ProbabilityTheory.cond]
  simp only [Measure.smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply, MeasurableSet.univ,
    Measure.restrict_apply, Set.univ_inter, smul_eq_mul]
  by_cases hμs : μ s = 0
  · simp [hμs]
  · refine ENNReal.mul_lt_top ?_ (measure_ne_top _ _)
    simp only [ne_eq, ENNReal.inv_eq_top]
    exact hμs

lemma cond_eq_zero_of_measure_zero {α : Type*} {_ : MeasurableSpace α} {μ : Measure α} {s : Set α}
    (hμs : μ s = 0) :
    μ[|s] = 0 := by
  have : μ.restrict s = 0 := by simp [hμs]
  simp [ProbabilityTheory.cond, this]

end aux_lemmas

section negIdMulLog

/-- The function `x ↦ - x * log x` from `ℝ` to `ℝ`. -/
noncomputable
def negIdMulLog (x : ℝ) : ℝ := - x * log x

@[simp]
lemma negIdMulLog_zero : negIdMulLog (0 : ℝ) = 0 := by simp [negIdMulLog]

@[simp]
lemma negIdMulLog_one : negIdMulLog (1 : ℝ) = 0 := by simp [negIdMulLog]

lemma negIdMulLog_eq_neg : negIdMulLog = fun x ↦ - (x * log x) := by simp [negIdMulLog]

lemma negIdMulLog_nonneg {x : ℝ} (h1 : 0 ≤ x) (h2 : x ≤ 1) : 0 ≤ negIdMulLog x := by
  rw [negIdMulLog, neg_mul_comm]
  apply mul_nonneg h1
  simp only [Left.nonneg_neg_iff]
  exact log_nonpos h1 h2

lemma concaveOn_negIdMulLog : ConcaveOn ℝ (Set.Ici (0 : ℝ)) negIdMulLog := by
  rw [negIdMulLog_eq_neg]
  exact convexOn_id_mul_log.neg

lemma h_jensen {S : Type*} [Fintype S] {w : S → ℝ} {p : S → ℝ} (h0 : ∀ s, 0 ≤ w s)
    (h1 : ∑ s, w s = 1) (hmem : ∀ s, 0 ≤ p s) :
    ∑ s, (w s) * negIdMulLog (p s) ≤ negIdMulLog (∑ s, (w s) * (p s)) := by
  refine ConcaveOn.le_map_sum concaveOn_negIdMulLog ?_ h1 ?_
  · simp [h0]
  · simp [hmem]

end negIdMulLog

end x_log_x






namespace ProbabilityTheory

variable {Ω S T : Type*} [mΩ : MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
  [Fintype S] [Fintype T] [MeasurableSpace S] [MeasurableSpace T]

section measureEntropy

variable {μ : Measure S}

/-- Entropy of a measure on a finite measurable space.

We normalize the measure by `(μ Set.univ)⁻¹` to extend the entropy definition to finite measures.
What we really want to do is deal with `μ=0` or `IsProbabilityMeasure μ`, but we don't have
a typeclass for that (we could create one though).
The added complexity in the expression is not an issue because if `μ` is a probability measure,
a call to `simp` will simplify `(μ Set.univ)⁻¹ • μ` to `μ`. -/
noncomputable
def measureEntropy (μ : Measure S) : ℝ := ∑ s, negIdMulLog (((μ Set.univ)⁻¹ • μ) {s}).toReal

@[simp]
lemma measureEntropy_zero : measureEntropy (0 : Measure S) = 0 := by
  simp [measureEntropy]

lemma measureEntropy_of_not_isFiniteMeasure (h : ¬ IsFiniteMeasure μ) :
    measureEntropy μ = 0 := by
  simp [measureEntropy, not_isFiniteMeasure_iff.mp h]

lemma measureEntropy_of_isProbabilityMeasure (μ : Measure S) [IsProbabilityMeasure μ] :
    measureEntropy μ = ∑ s, negIdMulLog (μ {s}).toReal := by
  simp [measureEntropy]

lemma measureEntropy_univ_smul : measureEntropy ((μ Set.univ)⁻¹ • μ) = measureEntropy μ := by
  by_cases hμ_fin : IsFiniteMeasure μ
  swap
  · rw [measureEntropy_of_not_isFiniteMeasure hμ_fin]
    rw [not_isFiniteMeasure_iff] at hμ_fin
    simp [hμ_fin]
  cases eq_zero_or_neZero μ with
  | inl hμ => simp [hμ]
  | inr hμ =>
    rw [measureEntropy]
    simp only [Measure.smul_toOuterMeasure, OuterMeasure.coe_smul, Pi.smul_apply, smul_eq_mul,
      ENNReal.toReal_mul]
    rw [ENNReal.inv_mul_cancel]
    · simp only [inv_one, ENNReal.one_toReal, one_mul]
      simp [measureEntropy]
    · simp [hμ.out]
    · exact measure_ne_top _ _

lemma measureEntropy_nonneg (μ : Measure S) : 0 ≤ measureEntropy μ := by
  by_cases hμ_fin : IsFiniteMeasure μ
  swap; · rw [measureEntropy_of_not_isFiniteMeasure hμ_fin]
  refine Finset.sum_nonneg (fun s _ ↦ negIdMulLog_nonneg ENNReal.toReal_nonneg ?_)
  refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
  rw [ENNReal.ofReal_one]
  cases eq_zero_or_neZero μ with
  | inl hμ => simp [hμ]
  | inr hμ => exact prob_le_one

lemma measureEntropy_le_card_aux (μ : Measure S) [IsProbabilityMeasure μ] :
    measureEntropy μ ≤ log (Fintype.card S) := by
  cases isEmpty_or_nonempty S with
  | inl h =>
    have : μ = 0 := Subsingleton.elim _ _
    simp [Fintype.card_eq_zero, this]
  | inr h =>
    set N := Fintype.card S with hN
    have : 0 < N := Fintype.card_pos
    rw [measureEntropy]
    simp only [measure_univ, inv_one, one_smul]
    sorry -- use h_jensen, see pfr repo

lemma measureEntropy_le_log_card (μ : Measure S) :
    measureEntropy μ ≤ log (Fintype.card S) := by
  have h_log_card_nonneg : 0 ≤ log (Fintype.card S) := by
    cases isEmpty_or_nonempty S with
    | inl h =>
      rw [Fintype.card_eq_zero]
      simp
    | inr h =>
      refine log_nonneg ?_
      simp only [Nat.one_le_cast]
      exact Fintype.card_pos
  cases eq_zero_or_neZero μ with
  | inl hμ =>
    simp only [hμ, measureEntropy_zero]
    exact h_log_card_nonneg
  | inr hμ =>
    by_cases hμ_fin : IsFiniteMeasure μ
    swap;
    · rw [measureEntropy_of_not_isFiniteMeasure hμ_fin]
      exact h_log_card_nonneg
    rw [← measureEntropy_univ_smul]
    exact measureEntropy_le_card_aux _

end measureEntropy

section entropy

variable {X : Ω → S}

/-- Entropy of a random variable with values in a finite measurable space. -/
noncomputable
def entropy (X : Ω → S) : ℝ := measureEntropy (volume.map X)

lemma entropy_nonneg (X : Ω → S) : 0 ≤ entropy X := measureEntropy_nonneg _

lemma entropy_le_log_card (X : Ω → S) : entropy X ≤ log (Fintype.card S) :=
  measureEntropy_le_log_card _

end entropy

section condEntropy

variable {X : Ω → S} {Y : Ω → T}

/-- Conditional entropy of a random variable w.r.t. another.
This is the expectation under the law of `Y` of the entropy of the law of `X` conditioned on the
event `Y = y`. -/
noncomputable
def condEntropy (X : Ω → S) (Y : Ω → T) : ℝ :=
  --∑ y, (volume.map Y {y}).toReal * measureEntropy ((volume[|Y ⁻¹' {y}]).map X)
  (volume.map Y)[fun y ↦ measureEntropy ((volume[|Y ⁻¹' {y}]).map X)]

lemma condEntropy_nonneg (X : Ω → S) (Y : Ω → T) : 0 ≤ condEntropy X Y :=
  integral_nonneg (fun _ ↦ measureEntropy_nonneg _)

lemma condEntropy_le_log_card (X : Ω → S) (Y : Ω → T) (hY : Measurable Y) :
    condEntropy X Y ≤ log (Fintype.card S) := by
  have : ∀ y, measureEntropy ((volume[|Y ⁻¹' {y}]).map X) ≤ log (Fintype.card S) :=
    fun y ↦ measureEntropy_le_log_card _
  refine (integral_mono_of_nonneg ?_ (integrable_const (log (Fintype.card S))) ?_).trans ?_
  · exact ae_of_all _ (fun _ ↦ measureEntropy_nonneg _)
  · exact ae_of_all _ this
  · have : IsProbabilityMeasure (volume.map Y) := isProbabilityMeasure_map hY.aemeasurable
    simp

lemma measureEntropy_cond_map (hX : Measurable X) (y : T) :
    measureEntropy ((volume[|Y ⁻¹' {y}]).map X)
      = ∑ x, negIdMulLog ((ℙ[|Y ⁻¹' {y}]).map X {x}).toReal := by
  by_cases hy : ℙ (Y ⁻¹' {y}) = 0
  · rw [cond_eq_zero_of_measure_zero hy]
    simp
  · have : IsProbabilityMeasure (volume[|Y ⁻¹' {y}]) := cond_isProbabilityMeasure _ hy
    have : IsProbabilityMeasure ((volume[|Y ⁻¹' {y}]).map X) :=
      isProbabilityMeasure_map hX.aemeasurable
    rw [measureEntropy]
    simp

lemma condEntropy_eq_sum [MeasurableSingletonClass T] (X : Ω → S) (Y : Ω → T) :
    condEntropy X Y
      = ∑ y, (volume.map Y {y}).toReal * measureEntropy ((volume[|Y ⁻¹' {y}]).map X) := by
  rw [condEntropy, integral_eq_sum]
  simp_rw [smul_eq_mul]

lemma condEntropy_eq_sum_sum [MeasurableSingletonClass T] (hX : Measurable X) (Y : Ω → T) :
    condEntropy X Y
      = ∑ y, ∑ x, (volume.map Y {y}).toReal * negIdMulLog ((ℙ[|Y ⁻¹' {y}]).map X {x}).toReal := by
  rw [condEntropy_eq_sum]
  congr with y
  rw [measureEntropy_cond_map hX, mul_comm, Finset.sum_mul]
  simp_rw [mul_comm (volume.map Y {y}).toReal]

lemma condEntropy_eq_sum_prod [MeasurableSingletonClass T] (hX : Measurable X) (Y : Ω → T) :
    condEntropy X Y = ∑ p : S × T,
      (volume.map Y {p.2}).toReal * negIdMulLog ((ℙ[|Y ⁻¹' {p.2}]).map X {p.1}).toReal := by
  rw [condEntropy_eq_sum_sum hX Y]
  have h_prod : (Finset.univ : Finset (S × T)) = (Finset.univ : Finset S) ×ˢ Finset.univ := rfl
  rw [h_prod, Finset.sum_product_right]

end condEntropy

section pair

variable {X : Ω → S} {Y : Ω → T}

lemma measure_prod_singleton_eq_mul [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (hX : Measurable X) (hY : Measurable Y) {p : S × T} :
    (volume.map (fun ω ↦ (X ω, Y ω)) {p}).toReal
      = (volume.map Y {p.2}).toReal * ((volume[|Y ⁻¹' {p.2}]).map X {p.1}).toReal := by
  have hp_prod : {p} = {p.1} ×ˢ {p.2} := by simp
  rw [Measure.map_apply (hX.prod_mk hY) (measurableSet_singleton p)]
  by_cases hpY : ℙ (Y ⁻¹' {p.2}) = 0
  · rw [cond_eq_zero_of_measure_zero hpY]
    simp only [aemeasurable_zero_measure, not_true, Measure.map_zero, Measure.zero_toOuterMeasure,
      OuterMeasure.coe_zero, Pi.zero_apply, ENNReal.zero_toReal, mul_zero]
    suffices (ℙ ((fun a ↦ (X a, Y a)) ⁻¹' ({p.1} ×ˢ {p.2}))).toReal = 0 by convert this
    rw [Set.mk_preimage_prod, ENNReal.toReal_eq_zero_iff]
    exact Or.inl (measure_mono_null (Set.inter_subset_right _ _) hpY)
  rw [Measure.map_apply hY (measurableSet_singleton p.2)]
  simp_rw [Measure.map_apply hX (measurableSet_singleton _)]
  simp_rw [cond_apply _ (hY (measurableSet_singleton _))]
  rw [ENNReal.toReal_mul, ← mul_assoc, ENNReal.toReal_inv, mul_inv_cancel, one_mul, hp_prod,
    Set.mk_preimage_prod, Set.inter_comm]
  rw [ENNReal.toReal_ne_zero]; exact ⟨hpY, measure_ne_top _ _⟩

lemma negIdMulLog_measure_prod_singleton [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (hX : Measurable X) (hY : Measurable Y) {p : S × T} :
    negIdMulLog (volume.map (fun ω ↦ (X ω, Y ω)) {p}).toReal
      = - ((volume[|Y ⁻¹' {p.2}]).map X {p.1}).toReal
          * (volume.map Y {p.2}).toReal* log (volume.map Y {p.2}).toReal
        - (volume.map Y {p.2}).toReal * ((volume[|Y ⁻¹' {p.2}]).map X {p.1}).toReal
          * log ((volume[|Y ⁻¹' {p.2}]).map X {p.1}).toReal := by
  rw [measure_prod_singleton_eq_mul hX hY]
  by_cases hpY : ℙ (Y ⁻¹' {p.2}) = 0
  · rw [cond_eq_zero_of_measure_zero hpY]
    simp
  by_cases hpX : (volume[|Y ⁻¹' {p.2}]).map X {p.1} = 0
  · simp [hpX]
  rw [negIdMulLog, log_mul]
  · ring
  · rw [ENNReal.toReal_ne_zero]
    refine ⟨?_, measure_ne_top _ _⟩
    rwa [Measure.map_apply hY (measurableSet_singleton _)]
  · rw [ENNReal.toReal_ne_zero]
    refine ⟨hpX, measure_ne_top _ _⟩

lemma chain_rule [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    (hX : Measurable X) (hY : Measurable Y) :
    entropy (fun ω ↦ (X ω, Y ω)) = entropy Y + condEntropy X Y := by
  have : IsProbabilityMeasure (volume.map Y) := isProbabilityMeasure_map hY.aemeasurable
  have : IsProbabilityMeasure (volume.map (fun ω ↦ (X ω, Y ω))) :=
    isProbabilityMeasure_map (hX.prod_mk hY).aemeasurable
  rw [entropy, measureEntropy_of_isProbabilityMeasure]
  simp_rw [negIdMulLog_measure_prod_singleton hX hY, sub_eq_add_neg, Finset.sum_add_distrib]
  congr
  · have h_prod : (Finset.univ : Finset (S × T)) = (Finset.univ : Finset S) ×ˢ Finset.univ := rfl
    rw [h_prod, Finset.sum_product_right, entropy, measureEntropy_of_isProbabilityMeasure]
    congr with y
    simp only [neg_mul, Finset.sum_neg_distrib]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    by_cases hy : ℙ (Y ⁻¹' {y}) = 0
    · simp [cond_eq_zero_of_measure_zero hy, Measure.map_apply hY, hy]
    have : IsProbabilityMeasure (volume[|Y ⁻¹' {y}]) := cond_isProbabilityMeasure _ hy
    suffices ∑ x : S, (Measure.map X (ℙ[|Y ⁻¹' {y}]) {x}).toReal = 1 by
      rw [this, one_mul, ← neg_mul, negIdMulLog]
    rw [← ENNReal.toReal_sum (fun _ _ ↦ measure_ne_top _ _), ENNReal.toReal_eq_one_iff]
    simp_rw [Measure.map_apply hX (measurableSet_singleton _)]
    rw [sum_measure_preimage_singleton _ (fun y _ ↦ hX (measurableSet_singleton y))]
    simp
  · rw [condEntropy_eq_sum_prod hX]
    congr with p
    rw [negIdMulLog]
    ring

end pair

end ProbabilityTheory
