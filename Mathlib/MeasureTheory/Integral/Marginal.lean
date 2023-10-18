/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue

/-!
# Marginals of multivariate functions
-/


open scoped Classical ENNReal
open Set Function Equiv Finset
set_option autoImplicit true

noncomputable section

-- not needed
-- theorem surjective_decode_iget (α : Type _) [Encodable α] [Inhabited α] :
--     Function.Surjective fun n => (Encodable.decode (α := α) n).iget := fun x =>
--   ⟨Encodable.encode x, by simp_rw [Encodable.encodek]⟩

-- move this, maybe next to `measurable_update` in `MeasureTheory.MeasurableSpace`
section Measurable
variable {δ : Type _} [DecidableEq δ] {π : δ → Type _} [∀ a : δ, MeasurableSpace (π a)]

-- unused
theorem measurable_update'  {a : δ} :
    Measurable (fun p : (∀ i, π i) × π a ↦ update p.1 a p.2) := by
  rw [measurable_pi_iff]; intro j
  dsimp [update]
  split_ifs with h
  · subst h
    dsimp
    exact measurable_snd
  · exact measurable_pi_iff.1 measurable_fst _

theorem measurable_update_left {a : δ} {x : π a} :
    Measurable (update · a x) := by
  rw [measurable_pi_iff]; intro j
  dsimp [update]
  split_ifs with h
  · subst h
    exact measurable_const
  · exact measurable_pi_apply j

theorem measurable_updateSet {s : Finset δ} {x : ∀ i, π i}  : Measurable (updateSet x s) := by
  simp_rw [updateSet, measurable_pi_iff]
  intro i
  by_cases h : i ∈ s <;> simp [h, measurable_pi_apply]

end Measurable

namespace MeasureTheory

section Marginal

variable {δ δ' : Type _} {π : δ → Type _} [∀ x, MeasurableSpace (π x)]
variable {μ : ∀ i, Measure (π i)} [∀ i, SigmaFinite (μ i)]
variable {s t : Finset δ} {f g : (∀ i, π i) → ℝ≥0∞} {x y : ∀ i, π i} {i : δ}

/-- Integrate `f(x₁,…,xₙ)` over all variables `xᵢ` where `i ∈ s`. Return a function in the
  remaining variables (it will be constant in the `xᵢ` for `i ∈ s`).
  This is the marginal distribution of all variables not in `s`. -/
def marginal (μ : ∀ i, Measure (π i)) (s : Finset δ) (f : (∀ i, π i) → ℝ≥0∞) (x : ∀ i, π i) :
    ℝ≥0∞ :=
  ∫⁻ y : ∀ i : s, π i, f (updateSet x s y) ∂Measure.pi fun i : s => μ i

-- Note: this notation is not a binder. This is more convenient since it returns a function.
notation "∫⋯∫_" s ", " f " ∂" μ:70 => marginal μ s f

notation "∫⋯∫_" s ", " f => marginal (fun _ ↦ volume) s f

variable (μ)

theorem _root_.Measurable.marginal (hf : Measurable f) : Measurable (∫⋯∫_s, f ∂μ) := by
  refine' Measurable.lintegral_prod_right _
  refine' hf.comp _
  rw [measurable_pi_iff]; intro i
  by_cases hi : i ∈ s
  · simp [hi, updateSet]
    exact measurable_pi_iff.1 measurable_snd _
  · simp [hi, updateSet]
    exact measurable_pi_iff.1 measurable_fst _

@[simp] theorem marginal_empty (f : (∀ i, π i) → ℝ≥0∞) : ∫⋯∫_∅, f ∂μ = f := by
  ext1 x
  simp_rw [marginal, Measure.pi_of_empty fun i : (∅ : Finset δ) => μ i]
  apply lintegral_dirac'
  exact Subsingleton.measurable

/-- The marginal distribution is independent of the variables in `s`. -/
-- todo: notation `∀ i ∉ s, ...`
theorem marginal_congr {x y : ∀ i, π i} (f : (∀ i, π i) → ℝ≥0∞)
    (h : ∀ (i) (_ : i ∉ s), x i = y i) :
    (∫⋯∫_s, f ∂μ) x = (∫⋯∫_s, f ∂μ) y := by
  dsimp [marginal, updateSet]; rcongr; exact h _ ‹_›

theorem marginal_update_of_mem [DecidableEq δ] {i : δ} (hi : i ∈ s)
    (f : (∀ i, π i) → ℝ≥0∞) (x : ∀ i, π i) (y : π i) :
    (∫⋯∫_s, f ∂μ) (Function.update x i y) = (∫⋯∫_s, f ∂μ) x := by
  apply marginal_congr
  intro j hj
  have : j ≠ i := by rintro rfl; exact hj hi
  apply update_noteq this

theorem marginal_union [DecidableEq δ] (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f)
    (hst : Disjoint s t) : ∫⋯∫_s ∪ t, f ∂μ = ∫⋯∫_s, ∫⋯∫_t, f ∂μ ∂μ := by
  ext1 x
  set e₁ := (finsetUnionEquivSum s t hst).symm
  set e₂ := MeasurableEquiv.piCongrLeft (fun i : ↥(s ∪ t) => π i) e₁
  set e₃ := MeasurableEquiv.piSum fun b ↦ π (e₁ b)
  calc (∫⋯∫_s ∪ t, f ∂μ) x
      = ∫⁻ (y : (i : ↥(s ∪ t)) → π i), f (updateSet x (s ∪ t) y)
          ∂.pi fun i' : ↥(s ∪ t) ↦ μ i' := by rfl
    _ = ∫⁻ (y : (i : s ⊕ t) → π (e₁ i)), f (updateSet x (s ∪ t) (e₂ y))
          ∂.pi fun i' : s ⊕ t ↦ μ (e₁ i') := by
        simp_rw [← Measure.pi_map_left _ e₁, lintegral_map_equiv]
    _ = ∫⁻ (y : ((i : s) → π i) × ((j : t) → π j)), f (updateSet x (s ∪ t) (e₂ (e₃ y)))
          ∂(Measure.pi fun i : s ↦ μ i).prod (.pi fun j : t ↦ μ j) := by
        simp_rw [← Measure.pi_sum, lintegral_map_equiv]; rfl
    _ = ∫⁻ (y : (i : s) → π i), ∫⁻ (z : (j : t) → π j), f (updateSet x (s ∪ t) (e₂ (e₃ (y, z))))
          ∂.pi fun j : t ↦ μ j ∂.pi fun i : s ↦ μ i := by
        apply lintegral_prod
        apply Measurable.aemeasurable
        exact hf.comp <| measurable_updateSet.comp <| e₂.measurable.comp e₃.measurable
    _ = (∫⋯∫_s, ∫⋯∫_t, f ∂μ ∂μ) x := by
        simp_rw [marginal, updateSet_updateSet hst]
        rfl

theorem marginal_union' (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f) {s t : Finset δ}
    (hst : Disjoint s t) : ∫⋯∫_s ∪ t, f ∂μ = ∫⋯∫_t, ∫⋯∫_s, f ∂μ ∂μ := by
  rw [Finset.union_comm, marginal_union μ f hf hst.symm]

variable {μ}

theorem marginal_singleton [DecidableEq δ] (f : (∀ i, π i) → ℝ≥0∞) (i : δ) :
    ∫⋯∫_{i}, f ∂μ = fun x => ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i := by
  let α : Type _ := ({i} : Finset δ)
  let e := (MeasurableEquiv.piUnique fun j : α ↦ π j).symm
  ext1 x
  calc (∫⋯∫_{i}, f ∂μ) x
      = ∫⁻ (y : π (default : α)), f (updateSet x {i} (e y)) ∂μ (default : α) := by
        simp_rw [marginal, ← Measure.map_piUnique_symm, lintegral_map_equiv]
    _ = ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i := by simp [update_eq_updateSet]

/-- Peel off a single integral from a `marginal` integral at the beginning (compare with
`marginal_insert'`, which peels off an integral at the end). -/
theorem marginal_insert [DecidableEq δ] (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f) {i : δ}
    (hi : i ∉ s) (x : ∀ i, π i) :
    (∫⋯∫_insert i s, f ∂μ) x = ∫⁻ xᵢ, (∫⋯∫_s, f ∂μ) (Function.update x i xᵢ) ∂μ i := by
  rw [Finset.insert_eq, marginal_union μ f hf (Finset.disjoint_singleton_left.mpr hi),
    marginal_singleton]

/-- Peel off a single integral from a `marginal` integral at the beginning (compare with
`marginal_erase'`, which peels off an integral at the end). -/
theorem marginal_erase [DecidableEq δ] (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f) {i : δ}
    (hi : i ∈ s) (x : ∀ i, π i) :
    (∫⋯∫_s, f ∂μ) x = ∫⁻ xᵢ, (∫⋯∫_(erase s i), f ∂μ) (Function.update x i xᵢ) ∂μ i := by
  simpa [insert_erase hi] using marginal_insert _ hf (not_mem_erase i s) x

/-- Peel off a single integral from a `marginal` integral at the end (compare with
`marginal_insert`, which peels off an integral at the beginning). -/
theorem marginal_insert' [DecidableEq δ] (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f) {i : δ}
    (hi : i ∉ s) :
    ∫⋯∫_insert i s, f ∂μ = ∫⋯∫_s, (fun x ↦ ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i) ∂μ := by
  rw [Finset.insert_eq, Finset.union_comm,
    marginal_union (s := s) μ f hf (Finset.disjoint_singleton_right.mpr hi), marginal_singleton]

/-- Peel off a single integral from a `marginal` integral at the end (compare with
`marginal_erase`, which peels off an integral at the beginning). -/
theorem marginal_erase' [DecidableEq δ] (f : (∀ i, π i) → ℝ≥0∞) (hf : Measurable f) {i : δ}
    (hi : i ∈ s) :
    ∫⋯∫_s, f ∂μ = ∫⋯∫_(erase s i), (fun x ↦ ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i) ∂μ := by
  simpa [insert_erase hi] using marginal_insert' _ hf (not_mem_erase i s)

open Filter

@[gcongr]
theorem marginal_mono {f g : (∀ i, π i) → ℝ≥0∞} (hfg : f ≤ g) : ∫⋯∫_s, f ∂μ ≤ ∫⋯∫_s, g ∂μ :=
  fun _ => lintegral_mono fun _ => hfg _

@[simp] theorem marginal_univ [Fintype δ] {f : (∀ i, π i) → ℝ≥0∞} :
    ∫⋯∫_univ, f ∂μ = fun _ => ∫⁻ x, f x ∂Measure.pi μ := by
  let e : { j // j ∈ Finset.univ } ≃ δ := Equiv.subtypeUnivEquiv mem_univ
  ext1 x
  simp_rw [marginal, ← Measure.pi_map_left μ e, lintegral_map_equiv, updateSet]
  simp
  rfl

theorem lintegral_eq_marginal_univ [Fintype δ] {f : (∀ i, π i) → ℝ≥0∞} (x : ∀ i, π i) :
    ∫⁻ x, f x ∂Measure.pi μ = (∫⋯∫_univ, f ∂μ) x := by simp

theorem marginal_image [DecidableEq δ] {e : δ' → δ} (he : Injective e) (s : Finset δ')
    {f : (∀ i, π (e i)) → ℝ≥0∞} (hf : Measurable f) (x : ∀ i, π i) :
      (∫⋯∫_s.image e, f ∘ (· ∘' e) ∂μ) x = (∫⋯∫_s, f ∂μ ∘' e) (x ∘' e) := by
  have h : Measurable ((· ∘' e) : (∀ i, π i) → _) :=
    measurable_pi_iff.mpr <| λ i ↦ measurable_pi_apply (e i)
  induction s using Finset.induction generalizing x
  case empty => simp
  case insert i s hi ih =>
    rw [image_insert, marginal_insert _ (hf.comp h) (he.mem_finset_image.not.mpr hi),
      marginal_insert _ hf hi]
    simp_rw [ih, ← update_comp_eq_of_injective' x he]

theorem marginal_update_of_not_mem [DecidableEq δ] {i : δ}
    {f : (∀ i, π i) → ℝ≥0∞} (hf : Measurable f) (hi : i ∉ s) (x : ∀ i, π i) (y : π i) :
    (∫⋯∫_s, f ∂μ) (Function.update x i y) = (∫⋯∫_s, f ∘ (Function.update · i y) ∂μ) x := by
  induction s using Finset.induction generalizing x
  case empty => simp
  case insert i' s hi' ih =>
    rw [marginal_insert _ hf hi', marginal_insert _ (hf.comp measurable_update_left) hi']
    have hii' : i ≠ i' := mt (by rintro rfl; exact mem_insert_self i s) hi
    simp_rw [update_comm hii', ih (mt Finset.mem_insert_of_mem hi)]

theorem marginal_eq_of_subset {f g : (∀ i, π i) → ℝ≥0∞} (hst : s ⊆ t)
    (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫_s, f ∂μ = ∫⋯∫_s, g ∂μ) :
    ∫⋯∫_t, f ∂μ = ∫⋯∫_t, g ∂μ := by
  rw [← union_sdiff_of_subset hst, marginal_union' μ f hf disjoint_sdiff,
    marginal_union' μ g hg disjoint_sdiff, hfg]

theorem marginal_le_of_subset {f g : (∀ i, π i) → ℝ≥0∞} (hst : s ⊆ t)
    (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫_s, f ∂μ ≤ ∫⋯∫_s, g ∂μ) :
    ∫⋯∫_t, f ∂μ ≤ ∫⋯∫_t, g ∂μ := by
  rw [← union_sdiff_of_subset hst, marginal_union' μ f hf disjoint_sdiff,
    marginal_union' μ g hg disjoint_sdiff]
  exact marginal_mono hfg

theorem lintegral_eq_of_marginal_eq [Fintype δ] (s : Finset δ) {f g : (∀ i, π i) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫_s, f ∂μ = ∫⋯∫_s, g ∂μ) :
    ∫⁻ x, f x ∂Measure.pi μ = ∫⁻ x, g x ∂Measure.pi μ := by
  rcases isEmpty_or_nonempty (∀ i, π i) with h|⟨⟨x⟩⟩
  · simp_rw [lintegral_of_isEmpty]
  simp_rw [lintegral_eq_marginal_univ x, marginal_eq_of_subset (Finset.subset_univ s) hf hg hfg]

theorem lintegral_le_of_marginal_le [Fintype δ] (s : Finset δ) {f g : (∀ i, π i) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫_s, f ∂μ ≤ ∫⋯∫_s, g ∂μ) :
    ∫⁻ x, f x ∂Measure.pi μ ≤ ∫⁻ x, g x ∂Measure.pi μ := by
  rcases isEmpty_or_nonempty (∀ i, π i) with h|⟨⟨x⟩⟩
  · simp_rw [lintegral_of_isEmpty, le_rfl]
  simp_rw [lintegral_eq_marginal_univ x, marginal_le_of_subset (Finset.subset_univ s) hf hg hfg x]

end Marginal


section

/-! Compute some measures using marginal. -/

variable {α : Fin (n+1) → Type*} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
variable [∀ i, SigmaFinite (μ i)]

open Fin

@[simp]
theorem insertNth_dcomp_succAbove (i : Fin (n + 1)) (x : α i) (p : ∀ j, α (i.succAbove j)) :
    insertNth i x p ∘' i.succAbove = p :=
  funext (insertNth_apply_succAbove i x p)

@[simp]
theorem insertNth_apply_dcomp_succAbove (i : Fin (n + 1)) (x : α i) (z : ∀ i, α i) :
    insertNth i x (z ∘' i.succAbove) = update z i x := by
  ext j
  rcases eq_or_ne i j with rfl|hij
  · simp
  obtain ⟨j', rfl⟩ := exists_succAbove_eq_iff.mpr hij.symm
  simp [dcomp, hij.symm]

theorem insertNth_comp_dcomp_succAbove (i : Fin (n + 1)) (x : α i) :
    insertNth i x ∘ (· ∘' i.succAbove) = (update · i x) := by
  simp [comp]

theorem insertNth_eq_of_ne {i j : Fin (n + 1)} (h : i ≠ j) (x x' : α i)
    (p : ∀ j, α (i.succAbove j)) : insertNth i x p j = insertNth i x' p j := by
  obtain ⟨j', rfl⟩ := exists_succAbove_eq_iff.mpr h.symm
  simp

@[simp]
theorem update_insertNth {i : Fin (n + 1)} (x x' : α i) (p : ∀ j, α (i.succAbove j)) :
    update (insertNth i x p) i x' = insertNth i x' p := by
  ext j
  rcases eq_or_ne i j with rfl|hij
  · simp
  simp [hij.symm, insertNth_eq_of_ne hij x x']

theorem measurable_insertNth {i : Fin (n+1)} (x : α i) :
    Measurable (insertNth i x) := by
  refine measurable_pi_iff.mpr fun j ↦ ?_
  rcases eq_or_ne i j with rfl|hij
  · simp
  obtain ⟨j', rfl⟩ := exists_succAbove_eq_iff.mpr hij.symm
  simp [measurable_pi_apply]

/-- An example of a computation we can do with `marginal`. Working with `marginal` directly is
  probably easier than using this lemma, though. This is roughly `FUBINI_SIMPLE` from HOL Light,
  though this has weaker assumptions (HOL Light assumes that `s` is bounded in `ℝⁿ`).
  Note: we could generalize `i.succAbove : Fin n → Fin (n+1)` to an arbitrary injective map `ι → ι'`
  whose range misses one point. -/
theorem lintegral_measure_insertNth {s : Set (∀ i, α i)} (hs : MeasurableSet s) (i : Fin (n+1)) :
    ∫⁻ x, Measure.pi (μ ∘' i.succAbove) (insertNth i x ⁻¹' s) ∂μ i =
    Measure.pi μ s := by
  rcases isEmpty_or_nonempty (α i) with h|⟨⟨x⟩⟩
  · have : IsEmpty (∀ i, α i) := ⟨λ x ↦ h.elim <| x i⟩
    simp [lintegral_of_isEmpty, Measure.eq_zero_of_isEmpty]
  rcases isEmpty_or_nonempty (∀ j, α (i.succAbove j)) with h|⟨⟨y⟩⟩
  · have : IsEmpty (∀ i, α i) := ⟨λ x ↦ h.elim <| λ j ↦ x _⟩
    simp [Measure.eq_zero_of_isEmpty]
  have hi : i ∉ ({i}ᶜ : Finset _) := not_mem_compl.mpr <| mem_singleton_self i
  let z := insertNth i x y
  calc ∫⁻ x : α i, Measure.pi (μ ∘' succAbove i) (insertNth i x ⁻¹' s) ∂μ i
      = ∫⁻ x : α i, (∫⋯∫_.univ, indicator (insertNth i x ⁻¹' s) 1 ∂μ ∘' succAbove i) y ∂μ i := by
        simp_rw [← lintegral_indicator_one (measurable_insertNth _ hs),
          lintegral_eq_marginal_univ y]
    _ = ∫⁻ x : α i, (∫⋯∫_.univ, indicator (insertNth i x ⁻¹' s) 1 ∂μ ∘' succAbove i)
          (z ∘' i.succAbove) ∂μ i := by
        rw [← insertNth_dcomp_succAbove i x y]
    _ = ∫⁻ x : α i, (∫⋯∫_{i}ᶜ,
          indicator (insertNth i x ⁻¹' s) 1 ∘ (· ∘' succAbove i) ∂μ) z ∂μ i := by
        simp_rw [← λ x ↦ marginal_image succAbove_right_injective (μ := μ) .univ
          (f := indicator (insertNth i x ⁻¹' s) (1 : ((j : Fin n) → α (succAbove i j)) → ℝ≥0∞))
          (measurable_one.indicator (measurable_insertNth _ hs)) z, Fin.image_succAbove_univ]
    _ = ∫⁻ x : α i, (∫⋯∫_{i}ᶜ,
          indicator (insertNth i x ∘ (· ∘' succAbove i) ⁻¹' s) 1 ∂μ) z ∂μ i := by
        rfl
    _ = ∫⁻ x : α i, (∫⋯∫_{i}ᶜ,
          indicator ((Function.update · i x) ⁻¹' s) 1 ∂μ) z ∂μ i := by
        simp [comp]
    _ = (∫⋯∫_insert i {i}ᶜ, indicator s 1 ∂μ) z := by
        simp_rw [marginal_insert _ (measurable_one.indicator hs) hi,
          marginal_update_of_not_mem (measurable_one.indicator hs) hi]
        rfl
    _ = (∫⋯∫_.univ, indicator s 1 ∂μ) z := by simp
    _ = Measure.pi μ s := by rw [← lintegral_indicator_one hs, lintegral_eq_marginal_univ z]

end

section MeasureSpace

/-! Compute some measures using marginal. -/

variable {α : Fin (n+1) → Type*} [∀ i, MeasureSpace (α i)] [∀ i, SigmaFinite (volume (α := α i))]

open Fin

theorem lintegral_volume_insertNth {s : Set (∀ i, α i)} (hs : MeasurableSet s) (i : Fin (n+1)) :
    ∫⁻ x, volume (insertNth i x ⁻¹' s) = volume s :=
  lintegral_measure_insertNth (fun _ ↦ volume) hs i

end MeasureSpace

end MeasureTheory
