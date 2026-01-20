/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
module

import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic

/-!
# Ultrapower (Ultrafilter-Generic)

This file defines the ultrafilter-generic ultrapower as a specialization of `Filter.Germ`.
It provides a small, neutral API that can later be used to decouple NSA from a specific
ultrafilter choice (such as `hyperfilter`).
-/

namespace Filter

/-- The ultrafilter-generic ultrapower of `alpha` indexed by `iota`. -/
abbrev Ultrapower (U : Ultrafilter iota) (alpha : Type*) : Type _ :=
  Germ (U : Filter iota) alpha

namespace Ultrapower

variable {iota : Type*} {U : Ultrafilter iota}
variable {alpha beta gamma : Type*}

/-- Constant embedding into an ultrapower. -/
noncomputable def ultraConst (a : alpha) : Ultrapower U alpha :=
  Germ.const a

/-- Coercion from the base type to its ultrapower via `ultraConst`. -/
noncomputable instance : Coe alpha (Ultrapower U alpha) where
  coe := ultraConst

/-- Standard (constant) embedding into an ultrapower. -/
abbrev std : alpha → Ultrapower U alpha := ultraConst

/-- Construct an ultrapower element from a sequence. -/
def ofSeq (f : iota → alpha) : Ultrapower U alpha := Germ.ofFun f

theorem ofSeq_surjective : Function.Surjective (fun f : iota → alpha => ofSeq f) :=
  Quot.exists_rep

@[elab_as_elim]
theorem inductionOn {P : Ultrapower U alpha → Prop} (x : Ultrapower U alpha)
    (h : ∀ f : iota → alpha, P (ofSeq f)) : P x :=
  Germ.inductionOn x h

/-- Map a function to the ultrapower. -/
def map (f : alpha -> beta) : Ultrapower U alpha -> Ultrapower U beta :=
  Germ.map f

/-- Map a binary function to the ultrapower. -/
noncomputable def map2 (f : alpha -> beta -> gamma) :
    Ultrapower U alpha -> Ultrapower U beta -> Ultrapower U gamma :=
  Germ.map₂ f

/-- Lift a predicate to the ultrapower. -/
def liftPred (P : alpha -> Prop) : Ultrapower U alpha -> Prop :=
  Germ.LiftPred P

/-- Lift a relation to the ultrapower. -/
def liftRel (R : alpha -> beta -> Prop) :
    Ultrapower U alpha -> Ultrapower U beta -> Prop :=
  Germ.LiftRel R

/-- Alias for `map`. -/
abbrev lift (f : alpha → beta) : Ultrapower U alpha → Ultrapower U beta := map f

/-- Alias for `map2`. -/
abbrev lift₂ (f : alpha → beta → gamma) :
    Ultrapower U alpha → Ultrapower U beta → Ultrapower U gamma := map2 f

/-- Legacy alias for `liftPred`. -/
abbrev mapPred := liftPred

/-- Legacy alias for `liftRel`. -/
abbrev mapRel := liftRel

/-- The ultrafilter on the base type represented by a point of the ultrapower. -/
noncomputable def ultrafilterOf (x : Ultrapower U alpha) : Ultrafilter alpha :=
  Ultrafilter.map (Classical.choose (Quot.exists_rep x)) U

@[simp]
theorem liftPred_ofSeq {P : alpha → Prop} (f : iota → alpha) :
    liftPred P (ofSeq f) ↔ ∀ᶠ i in (U : Filter iota), P (f i) :=
  Iff.rfl

@[simp]
theorem liftRel_ofSeq {R : alpha → beta → Prop} (f : iota → alpha) (g : iota → beta) :
    liftRel R (ofSeq f) (ofSeq g) ↔ ∀ᶠ i in (U : Filter iota), R (f i) (g i) :=
  Iff.rfl

@[simp]
theorem liftPred_std [NeBot (U : Filter iota)] {P : alpha → Prop} {a : alpha} :
    liftPred P (std a : Ultrapower U alpha) ↔ P a := by
  simpa [std, liftPred] using (Germ.liftPred_const_iff (l := (U : Filter iota)) (p := P) (x := a))

@[simp]
theorem liftRel_std [NeBot (U : Filter iota)] {R : alpha → beta → Prop} {a : alpha} {b : beta} :
    liftRel R (std a : Ultrapower U alpha) (std b) ↔ R a b := by
  simpa [std, liftRel] using
    (Germ.liftRel_const_iff (l := (U : Filter iota)) (r := R) (x := a) (y := b))

@[simp]
theorem lift_std (f : alpha → beta) (a : alpha) :
    lift f (std a : Ultrapower U alpha) = (std (f a) : Ultrapower U beta) := by
  simpa [std, lift, map] using (Germ.map_const (l := (U : Filter iota)) (a := a) (f := f))

theorem forall_ofSeq_iff (P : Ultrapower U alpha → Prop) :
    (∀ x : Ultrapower U alpha, P x) ↔ ∀ f : iota → alpha, P (ofSeq f) := by
  constructor
  · intro h f
    exact h (ofSeq f)
  · intro h x
    obtain ⟨f, rfl⟩ := ofSeq_surjective x
    exact h f

theorem exists_ofSeq_iff (P : Ultrapower U alpha → Prop) :
    (∃ x : Ultrapower U alpha, P x) ↔ ∃ f : iota → alpha, P (ofSeq f) := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨f, rfl⟩ := ofSeq_surjective x
    exact ⟨f, hx⟩
  · rintro ⟨f, hf⟩
    exact ⟨ofSeq f, hf⟩

theorem forall_std_iff [NeBot (U : Filter iota)] (P : alpha → Prop) :
    (∀ a : alpha, P a) ↔ (∀ x : Ultrapower U alpha, liftPred P x) := by
  constructor
  · intro h x
    obtain ⟨f, rfl⟩ := ofSeq_surjective x
    exact (Filter.Eventually.of_forall fun i => h (f i))
  · intro h a
    simpa using (h (std a))

/-- An element of an ultrapower is standard if it is the image of some `a : alpha`. -/
def IsStandard (x : Ultrapower U alpha) : Prop := ∃ a, x = std a

theorem IsStandard.of_std (a : alpha) : IsStandard (std a : Ultrapower U alpha) := ⟨a, rfl⟩

/-- Existential transfer (standard witnesses only). -/
theorem exists_std_iff [NeBot (U : Filter iota)] (P : alpha → Prop) :
    (∃ a : alpha, P a) ↔ (∃ x : Ultrapower U alpha, IsStandard x ∧ liftPred P x) := by
  constructor
  · intro ⟨a, ha⟩
    exact ⟨std a, IsStandard.of_std a, by simpa [ha]⟩
  · rintro ⟨x, hstd, hP⟩
    obtain ⟨a, rfl⟩ := hstd
    exact ⟨a, by simpa using hP⟩

end Ultrapower

end Filter
