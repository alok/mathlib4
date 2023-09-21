/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Comp

#align_import analysis.calculus.fderiv.prod from "leanprover-community/mathlib"@"e354e865255654389cc46e6032160238df2e0f40"

/-!
# Derivative of the cartesian product of functions

For detailed documentation of the Fréchet derivative,
see the module docstring of `Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
cartesian products of functions, and functions into Pi-types.
-/


open Filter Asymptotics ContinuousLinearMap Set Metric

open Topology Classical NNReal Filter Asymptotics ENNReal

noncomputable section

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']

variable {f f₀ f₁ g : E → F}

variable {f' f₀' f₁' g' : E →L[𝕜] F}

variable (e : E →L[𝕜] F)

variable {x : E}

variable {s t : Set E}

variable {L L₁ L₂ : Filter E}

section CartesianProduct

/-! ### Derivative of the cartesian product of two functions -/


section Prod

variable {f₂ : E → G} {f₂' : E →L[𝕜] G}

protected lemma HasStrictFDerivAt.prod (hf₁ : HasStrictFDerivAt f₁ f₁' x)
    (hf₂ : HasStrictFDerivAt f₂ f₂' x) :
    HasStrictFDerivAt (fun x => (f₁ x, f₂ x)) (f₁'.prod f₂') x :=
  hf₁.prod_left hf₂
#align has_strict_fderiv_at.prod HasStrictFDerivAt.prod

lemma HasFDerivAtFilter.prod (hf₁ : HasFDerivAtFilter f₁ f₁' x L)
    (hf₂ : HasFDerivAtFilter f₂ f₂' x L) :
    HasFDerivAtFilter (fun x => (f₁ x, f₂ x)) (f₁'.prod f₂') x L :=
  hf₁.prod_left hf₂
#align has_fderiv_at_filter.prod HasFDerivAtFilter.prod

nonrec lemma HasFDerivWithinAt.prod (hf₁ : HasFDerivWithinAt f₁ f₁' s x)
    (hf₂ : HasFDerivWithinAt f₂ f₂' s x) :
    HasFDerivWithinAt (fun x => (f₁ x, f₂ x)) (f₁'.prod f₂') s x :=
  hf₁.prod hf₂
#align has_fderiv_within_at.prod HasFDerivWithinAt.prod

nonrec lemma HasFDerivAt.prod (hf₁ : HasFDerivAt f₁ f₁' x) (hf₂ : HasFDerivAt f₂ f₂' x) :
    HasFDerivAt (fun x => (f₁ x, f₂ x)) (f₁'.prod f₂') x :=
  hf₁.prod hf₂
#align has_fderiv_at.prod HasFDerivAt.prod

lemma hasFDerivAt_prod_mk_left (e₀ : E) (f₀ : F) :
    HasFDerivAt (fun e : E => (e, f₀)) (inl 𝕜 E F) e₀ :=
  (hasFDerivAt_id e₀).prod (hasFDerivAt_const f₀ e₀)
#align has_fderiv_at_prod_mk_left hasFDerivAt_prod_mk_left

lemma hasFDerivAt_prod_mk_right (e₀ : E) (f₀ : F) :
    HasFDerivAt (fun f : F => (e₀, f)) (inr 𝕜 E F) f₀ :=
  (hasFDerivAt_const e₀ f₀).prod (hasFDerivAt_id f₀)
#align has_fderiv_at_prod_mk_right hasFDerivAt_prod_mk_right

lemma DifferentiableWithinAt.prod (hf₁ : DifferentiableWithinAt 𝕜 f₁ s x)
    (hf₂ : DifferentiableWithinAt 𝕜 f₂ s x) :
    DifferentiableWithinAt 𝕜 (fun x : E => (f₁ x, f₂ x)) s x :=
  (hf₁.hasFDerivWithinAt.prod hf₂.hasFDerivWithinAt).differentiableWithinAt
#align differentiable_within_at.prod DifferentiableWithinAt.prod

@[simp]
lemma DifferentiableAt.prod (hf₁ : DifferentiableAt 𝕜 f₁ x) (hf₂ : DifferentiableAt 𝕜 f₂ x) :
    DifferentiableAt 𝕜 (fun x : E => (f₁ x, f₂ x)) x :=
  (hf₁.hasFDerivAt.prod hf₂.hasFDerivAt).differentiableAt
#align differentiable_at.prod DifferentiableAt.prod

lemma DifferentiableOn.prod (hf₁ : DifferentiableOn 𝕜 f₁ s) (hf₂ : DifferentiableOn 𝕜 f₂ s) :
    DifferentiableOn 𝕜 (fun x : E => (f₁ x, f₂ x)) s := fun x hx =>
  DifferentiableWithinAt.prod (hf₁ x hx) (hf₂ x hx)
#align differentiable_on.prod DifferentiableOn.prod

@[simp]
lemma Differentiable.prod (hf₁ : Differentiable 𝕜 f₁) (hf₂ : Differentiable 𝕜 f₂) :
    Differentiable 𝕜 fun x : E => (f₁ x, f₂ x) := fun x => DifferentiableAt.prod (hf₁ x) (hf₂ x)
#align differentiable.prod Differentiable.prod

lemma DifferentiableAt.fderiv_prod (hf₁ : DifferentiableAt 𝕜 f₁ x)
    (hf₂ : DifferentiableAt 𝕜 f₂ x) :
    fderiv 𝕜 (fun x : E => (f₁ x, f₂ x)) x = (fderiv 𝕜 f₁ x).prod (fderiv 𝕜 f₂ x) :=
  (hf₁.hasFDerivAt.prod hf₂.hasFDerivAt).fderiv
#align differentiable_at.fderiv_prod DifferentiableAt.fderiv_prod

lemma DifferentiableWithinAt.fderivWithin_prod (hf₁ : DifferentiableWithinAt 𝕜 f₁ s x)
    (hf₂ : DifferentiableWithinAt 𝕜 f₂ s x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x : E => (f₁ x, f₂ x)) s x =
      (fderivWithin 𝕜 f₁ s x).prod (fderivWithin 𝕜 f₂ s x) :=
  (hf₁.hasFDerivWithinAt.prod hf₂.hasFDerivWithinAt).fderivWithin hxs
#align differentiable_within_at.fderiv_within_prod DifferentiableWithinAt.fderivWithin_prod

end Prod

section Fst

variable {f₂ : E → F × G} {f₂' : E →L[𝕜] F × G} {p : E × F}

lemma hasStrictFDerivAt_fst : HasStrictFDerivAt (@Prod.fst E F) (fst 𝕜 E F) p :=
  (fst 𝕜 E F).hasStrictFDerivAt
#align has_strict_fderiv_at_fst hasStrictFDerivAt_fst

protected lemma HasStrictFDerivAt.fst (h : HasStrictFDerivAt f₂ f₂' x) :
    HasStrictFDerivAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') x :=
  hasStrictFDerivAt_fst.comp x h
#align has_strict_fderiv_at.fst HasStrictFDerivAt.fst

lemma hasFDerivAtFilter_fst {L : Filter (E × F)} :
    HasFDerivAtFilter (@Prod.fst E F) (fst 𝕜 E F) p L :=
  (fst 𝕜 E F).hasFDerivAtFilter
#align has_fderiv_at_filter_fst hasFDerivAtFilter_fst

protected lemma HasFDerivAtFilter.fst (h : HasFDerivAtFilter f₂ f₂' x L) :
    HasFDerivAtFilter (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') x L :=
  hasFDerivAtFilter_fst.comp x h tendsto_map
#align has_fderiv_at_filter.fst HasFDerivAtFilter.fst

lemma hasFDerivAt_fst : HasFDerivAt (@Prod.fst E F) (fst 𝕜 E F) p :=
  hasFDerivAtFilter_fst
#align has_fderiv_at_fst hasFDerivAt_fst

protected nonrec lemma HasFDerivAt.fst (h : HasFDerivAt f₂ f₂' x) :
    HasFDerivAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') x :=
  h.fst
#align has_fderiv_at.fst HasFDerivAt.fst

lemma hasFDerivWithinAt_fst {s : Set (E × F)} :
    HasFDerivWithinAt (@Prod.fst E F) (fst 𝕜 E F) s p :=
  hasFDerivAtFilter_fst
#align has_fderiv_within_at_fst hasFDerivWithinAt_fst

protected nonrec lemma HasFDerivWithinAt.fst (h : HasFDerivWithinAt f₂ f₂' s x) :
    HasFDerivWithinAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') s x :=
  h.fst
#align has_fderiv_within_at.fst HasFDerivWithinAt.fst

lemma differentiableAt_fst : DifferentiableAt 𝕜 Prod.fst p :=
  hasFDerivAt_fst.differentiableAt
#align differentiable_at_fst differentiableAt_fst

@[simp]
protected lemma DifferentiableAt.fst (h : DifferentiableAt 𝕜 f₂ x) :
    DifferentiableAt 𝕜 (fun x => (f₂ x).1) x :=
  differentiableAt_fst.comp x h
#align differentiable_at.fst DifferentiableAt.fst

lemma differentiable_fst : Differentiable 𝕜 (Prod.fst : E × F → E) := fun _ =>
  differentiableAt_fst
#align differentiable_fst differentiable_fst

@[simp]
protected lemma Differentiable.fst (h : Differentiable 𝕜 f₂) :
    Differentiable 𝕜 fun x => (f₂ x).1 :=
  differentiable_fst.comp h
#align differentiable.fst Differentiable.fst

lemma differentiableWithinAt_fst {s : Set (E × F)} : DifferentiableWithinAt 𝕜 Prod.fst s p :=
  differentiableAt_fst.differentiableWithinAt
#align differentiable_within_at_fst differentiableWithinAt_fst

protected lemma DifferentiableWithinAt.fst (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    DifferentiableWithinAt 𝕜 (fun x => (f₂ x).1) s x :=
  differentiableAt_fst.comp_differentiableWithinAt x h
#align differentiable_within_at.fst DifferentiableWithinAt.fst

lemma differentiableOn_fst {s : Set (E × F)} : DifferentiableOn 𝕜 Prod.fst s :=
  differentiable_fst.differentiableOn
#align differentiable_on_fst differentiableOn_fst

protected lemma DifferentiableOn.fst (h : DifferentiableOn 𝕜 f₂ s) :
    DifferentiableOn 𝕜 (fun x => (f₂ x).1) s :=
  differentiable_fst.comp_differentiableOn h
#align differentiable_on.fst DifferentiableOn.fst

lemma fderiv_fst : fderiv 𝕜 Prod.fst p = fst 𝕜 E F :=
  hasFDerivAt_fst.fderiv
#align fderiv_fst fderiv_fst

lemma fderiv.fst (h : DifferentiableAt 𝕜 f₂ x) :
    fderiv 𝕜 (fun x => (f₂ x).1) x = (fst 𝕜 F G).comp (fderiv 𝕜 f₂ x) :=
  h.hasFDerivAt.fst.fderiv
#align fderiv.fst fderiv.fst

lemma fderivWithin_fst {s : Set (E × F)} (hs : UniqueDiffWithinAt 𝕜 s p) :
    fderivWithin 𝕜 Prod.fst s p = fst 𝕜 E F :=
  hasFDerivWithinAt_fst.fderivWithin hs
#align fderiv_within_fst fderivWithin_fst

lemma fderivWithin.fst (hs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    fderivWithin 𝕜 (fun x => (f₂ x).1) s x = (fst 𝕜 F G).comp (fderivWithin 𝕜 f₂ s x) :=
  h.hasFDerivWithinAt.fst.fderivWithin hs
#align fderiv_within.fst fderivWithin.fst

end Fst

section Snd

variable {f₂ : E → F × G} {f₂' : E →L[𝕜] F × G} {p : E × F}

lemma hasStrictFDerivAt_snd : HasStrictFDerivAt (@Prod.snd E F) (snd 𝕜 E F) p :=
  (snd 𝕜 E F).hasStrictFDerivAt
#align has_strict_fderiv_at_snd hasStrictFDerivAt_snd

protected lemma HasStrictFDerivAt.snd (h : HasStrictFDerivAt f₂ f₂' x) :
    HasStrictFDerivAt (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') x :=
  hasStrictFDerivAt_snd.comp x h
#align has_strict_fderiv_at.snd HasStrictFDerivAt.snd

lemma hasFDerivAtFilter_snd {L : Filter (E × F)} :
    HasFDerivAtFilter (@Prod.snd E F) (snd 𝕜 E F) p L :=
  (snd 𝕜 E F).hasFDerivAtFilter
#align has_fderiv_at_filter_snd hasFDerivAtFilter_snd

protected lemma HasFDerivAtFilter.snd (h : HasFDerivAtFilter f₂ f₂' x L) :
    HasFDerivAtFilter (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') x L :=
  hasFDerivAtFilter_snd.comp x h tendsto_map
#align has_fderiv_at_filter.snd HasFDerivAtFilter.snd

lemma hasFDerivAt_snd : HasFDerivAt (@Prod.snd E F) (snd 𝕜 E F) p :=
  hasFDerivAtFilter_snd
#align has_fderiv_at_snd hasFDerivAt_snd

protected nonrec lemma HasFDerivAt.snd (h : HasFDerivAt f₂ f₂' x) :
    HasFDerivAt (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') x :=
  h.snd
#align has_fderiv_at.snd HasFDerivAt.snd

lemma hasFDerivWithinAt_snd {s : Set (E × F)} :
    HasFDerivWithinAt (@Prod.snd E F) (snd 𝕜 E F) s p :=
  hasFDerivAtFilter_snd
#align has_fderiv_within_at_snd hasFDerivWithinAt_snd

protected nonrec lemma HasFDerivWithinAt.snd (h : HasFDerivWithinAt f₂ f₂' s x) :
    HasFDerivWithinAt (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') s x :=
  h.snd
#align has_fderiv_within_at.snd HasFDerivWithinAt.snd

lemma differentiableAt_snd : DifferentiableAt 𝕜 Prod.snd p :=
  hasFDerivAt_snd.differentiableAt
#align differentiable_at_snd differentiableAt_snd

@[simp]
protected lemma DifferentiableAt.snd (h : DifferentiableAt 𝕜 f₂ x) :
    DifferentiableAt 𝕜 (fun x => (f₂ x).2) x :=
  differentiableAt_snd.comp x h
#align differentiable_at.snd DifferentiableAt.snd

lemma differentiable_snd : Differentiable 𝕜 (Prod.snd : E × F → F) := fun _ =>
  differentiableAt_snd
#align differentiable_snd differentiable_snd

@[simp]
protected lemma Differentiable.snd (h : Differentiable 𝕜 f₂) :
    Differentiable 𝕜 fun x => (f₂ x).2 :=
  differentiable_snd.comp h
#align differentiable.snd Differentiable.snd

lemma differentiableWithinAt_snd {s : Set (E × F)} : DifferentiableWithinAt 𝕜 Prod.snd s p :=
  differentiableAt_snd.differentiableWithinAt
#align differentiable_within_at_snd differentiableWithinAt_snd

protected lemma DifferentiableWithinAt.snd (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    DifferentiableWithinAt 𝕜 (fun x => (f₂ x).2) s x :=
  differentiableAt_snd.comp_differentiableWithinAt x h
#align differentiable_within_at.snd DifferentiableWithinAt.snd

lemma differentiableOn_snd {s : Set (E × F)} : DifferentiableOn 𝕜 Prod.snd s :=
  differentiable_snd.differentiableOn
#align differentiable_on_snd differentiableOn_snd

protected lemma DifferentiableOn.snd (h : DifferentiableOn 𝕜 f₂ s) :
    DifferentiableOn 𝕜 (fun x => (f₂ x).2) s :=
  differentiable_snd.comp_differentiableOn h
#align differentiable_on.snd DifferentiableOn.snd

lemma fderiv_snd : fderiv 𝕜 Prod.snd p = snd 𝕜 E F :=
  hasFDerivAt_snd.fderiv
#align fderiv_snd fderiv_snd

lemma fderiv.snd (h : DifferentiableAt 𝕜 f₂ x) :
    fderiv 𝕜 (fun x => (f₂ x).2) x = (snd 𝕜 F G).comp (fderiv 𝕜 f₂ x) :=
  h.hasFDerivAt.snd.fderiv
#align fderiv.snd fderiv.snd

lemma fderivWithin_snd {s : Set (E × F)} (hs : UniqueDiffWithinAt 𝕜 s p) :
    fderivWithin 𝕜 Prod.snd s p = snd 𝕜 E F :=
  hasFDerivWithinAt_snd.fderivWithin hs
#align fderiv_within_snd fderivWithin_snd

lemma fderivWithin.snd (hs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    fderivWithin 𝕜 (fun x => (f₂ x).2) s x = (snd 𝕜 F G).comp (fderivWithin 𝕜 f₂ s x) :=
  h.hasFDerivWithinAt.snd.fderivWithin hs
#align fderiv_within.snd fderivWithin.snd

end Snd

section Prod_map

variable {f₂ : G → G'} {f₂' : G →L[𝕜] G'} {y : G} (p : E × G)

protected lemma HasStrictFDerivAt.prodMap (hf : HasStrictFDerivAt f f' p.1)
    (hf₂ : HasStrictFDerivAt f₂ f₂' p.2) : HasStrictFDerivAt (Prod.map f f₂) (f'.prodMap f₂') p :=
  (hf.comp p hasStrictFDerivAt_fst).prod (hf₂.comp p hasStrictFDerivAt_snd)
#align has_strict_fderiv_at.prod_map HasStrictFDerivAt.prodMap

protected lemma HasFDerivAt.prodMap (hf : HasFDerivAt f f' p.1) (hf₂ : HasFDerivAt f₂ f₂' p.2) :
    HasFDerivAt (Prod.map f f₂) (f'.prodMap f₂') p :=
  (hf.comp p hasFDerivAt_fst).prod (hf₂.comp p hasFDerivAt_snd)
#align has_fderiv_at.prod_map HasFDerivAt.prodMap

@[simp]
protected lemma DifferentiableAt.prod_map (hf : DifferentiableAt 𝕜 f p.1)
    (hf₂ : DifferentiableAt 𝕜 f₂ p.2) : DifferentiableAt 𝕜 (fun p : E × G => (f p.1, f₂ p.2)) p :=
  (hf.comp p differentiableAt_fst).prod (hf₂.comp p differentiableAt_snd)
#align differentiable_at.prod_map DifferentiableAt.prod_map

end Prod_map

section Pi

/-!
### Derivatives of functions `f : E → Π i, F' i`

In this section we formulate `has*FDeriv*_pi` theorems as `iff`s, and provide two versions of each
theorem:

* the version without `'` deals with `φ : Π i, E → F' i` and `φ' : Π i, E →L[𝕜] F' i`
  and is designed to deduce differentiability of `fun x i ↦ φ i x` from differentiability
  of each `φ i`;
* the version with `'` deals with `Φ : E → Π i, F' i` and `Φ' : E →L[𝕜] Π i, F' i`
  and is designed to deduce differentiability of the components `fun x ↦ Φ x i` from
  differentiability of `Φ`.
-/


variable {ι : Type*} [Fintype ι] {F' : ι → Type*} [∀ i, NormedAddCommGroup (F' i)]
  [∀ i, NormedSpace 𝕜 (F' i)] {φ : ∀ i, E → F' i} {φ' : ∀ i, E →L[𝕜] F' i} {Φ : E → ∀ i, F' i}
  {Φ' : E →L[𝕜] ∀ i, F' i}

@[simp]
lemma hasStrictFDerivAt_pi' :
    HasStrictFDerivAt Φ Φ' x ↔ ∀ i, HasStrictFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x := by
  simp only [HasStrictFDerivAt, ContinuousLinearMap.coe_pi]
  exact isLittleO_pi
#align has_strict_fderiv_at_pi' hasStrictFDerivAt_pi'

@[simp 1100] -- porting note: increased priority to make lint happy
lemma hasStrictFDerivAt_pi :
    HasStrictFDerivAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') x ↔
      ∀ i, HasStrictFDerivAt (φ i) (φ' i) x :=
  hasStrictFDerivAt_pi'
#align has_strict_fderiv_at_pi hasStrictFDerivAt_pi

@[simp]
lemma hasFDerivAtFilter_pi' :
    HasFDerivAtFilter Φ Φ' x L ↔
      ∀ i, HasFDerivAtFilter (fun x => Φ x i) ((proj i).comp Φ') x L := by
  simp only [HasFDerivAtFilter, ContinuousLinearMap.coe_pi]
  exact isLittleO_pi
#align has_fderiv_at_filter_pi' hasFDerivAtFilter_pi'

lemma hasFDerivAtFilter_pi :
    HasFDerivAtFilter (fun x i => φ i x) (ContinuousLinearMap.pi φ') x L ↔
      ∀ i, HasFDerivAtFilter (φ i) (φ' i) x L :=
  hasFDerivAtFilter_pi'
#align has_fderiv_at_filter_pi hasFDerivAtFilter_pi

@[simp]
lemma hasFDerivAt_pi' :
    HasFDerivAt Φ Φ' x ↔ ∀ i, HasFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x :=
  hasFDerivAtFilter_pi'
#align has_fderiv_at_pi' hasFDerivAt_pi'

lemma hasFDerivAt_pi :
    HasFDerivAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') x ↔
      ∀ i, HasFDerivAt (φ i) (φ' i) x :=
  hasFDerivAtFilter_pi
#align has_fderiv_at_pi hasFDerivAt_pi

@[simp]
lemma hasFDerivWithinAt_pi' :
    HasFDerivWithinAt Φ Φ' s x ↔ ∀ i, HasFDerivWithinAt (fun x => Φ x i) ((proj i).comp Φ') s x :=
  hasFDerivAtFilter_pi'
#align has_fderiv_within_at_pi' hasFDerivWithinAt_pi'

lemma hasFDerivWithinAt_pi :
    HasFDerivWithinAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') s x ↔
      ∀ i, HasFDerivWithinAt (φ i) (φ' i) s x :=
  hasFDerivAtFilter_pi
#align has_fderiv_within_at_pi hasFDerivWithinAt_pi

@[simp]
lemma differentiableWithinAt_pi :
    DifferentiableWithinAt 𝕜 Φ s x ↔ ∀ i, DifferentiableWithinAt 𝕜 (fun x => Φ x i) s x :=
  ⟨fun h i => (hasFDerivWithinAt_pi'.1 h.hasFDerivWithinAt i).differentiableWithinAt, fun h =>
    (hasFDerivWithinAt_pi.2 fun i => (h i).hasFDerivWithinAt).differentiableWithinAt⟩
#align differentiable_within_at_pi differentiableWithinAt_pi

@[simp]
lemma differentiableAt_pi : DifferentiableAt 𝕜 Φ x ↔ ∀ i, DifferentiableAt 𝕜 (fun x => Φ x i) x :=
  ⟨fun h i => (hasFDerivAt_pi'.1 h.hasFDerivAt i).differentiableAt, fun h =>
    (hasFDerivAt_pi.2 fun i => (h i).hasFDerivAt).differentiableAt⟩
#align differentiable_at_pi differentiableAt_pi

lemma differentiableOn_pi : DifferentiableOn 𝕜 Φ s ↔ ∀ i, DifferentiableOn 𝕜 (fun x => Φ x i) s :=
  ⟨fun h i x hx => differentiableWithinAt_pi.1 (h x hx) i, fun h x hx =>
    differentiableWithinAt_pi.2 fun i => h i x hx⟩
#align differentiable_on_pi differentiableOn_pi

lemma differentiable_pi : Differentiable 𝕜 Φ ↔ ∀ i, Differentiable 𝕜 fun x => Φ x i :=
  ⟨fun h i x => differentiableAt_pi.1 (h x) i, fun h x => differentiableAt_pi.2 fun i => h i x⟩
#align differentiable_pi differentiable_pi

-- TODO: find out which version (`φ` or `Φ`) works better with `rw`/`simp`
lemma fderivWithin_pi (h : ∀ i, DifferentiableWithinAt 𝕜 (φ i) s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x i => φ i x) s x = pi fun i => fderivWithin 𝕜 (φ i) s x :=
  (hasFDerivWithinAt_pi.2 fun i => (h i).hasFDerivWithinAt).fderivWithin hs
#align fderiv_within_pi fderivWithin_pi

lemma fderiv_pi (h : ∀ i, DifferentiableAt 𝕜 (φ i) x) :
    fderiv 𝕜 (fun x i => φ i x) x = pi fun i => fderiv 𝕜 (φ i) x :=
  (hasFDerivAt_pi.2 fun i => (h i).hasFDerivAt).fderiv
#align fderiv_pi fderiv_pi

end Pi

end CartesianProduct

end
