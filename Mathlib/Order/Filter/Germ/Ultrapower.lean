/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
module

public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Order.Filter.Ultrafilter.Basic

/-!
# Ultrapower (Ultrafilter-Generic)

This file defines the ultrafilter-generic ultrapower as a specialization of `Filter.Germ`.
It provides a small, neutral API that can later be used to decouple NSA from a specific
ultrafilter choice (such as `nonstandardUltrafilter`).
-/

@[expose] public section

namespace Filter

/-- The ultrafilter-generic ultrapower of `alpha` indexed by `iota`. -/
abbrev Ultrapower {iota : Type*} (U : Ultrafilter iota) (alpha : Type*) : Type _ :=
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
noncomputable abbrev std : alpha → Ultrapower U alpha := ultraConst

/-- Construct an ultrapower element from a sequence. -/
def ofSeq (f : iota → alpha) : Ultrapower U alpha := Germ.ofFun f

theorem ofSeq_surjective : Function.Surjective (fun f : iota → alpha => ofSeq (U := U) f) := by
  intro x
  exact Quot.exists_rep x

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
noncomputable abbrev lift₂ (f : alpha → beta → gamma) :
    Ultrapower U alpha → Ultrapower U beta → Ultrapower U gamma := map2 f

/-- Legacy alias for `liftPred`. -/
abbrev mapPred (P : alpha → Prop) : Ultrapower U alpha → Prop := liftPred P

/-- Legacy alias for `liftRel`. -/
abbrev mapRel (R : alpha → beta → Prop) :
    Ultrapower U alpha → Ultrapower U beta → Prop := liftRel R

/-- The ultrafilter on the base type represented by a point of the ultrapower. -/
noncomputable def ultrafilterOf (x : Ultrapower U alpha) : Ultrafilter alpha :=
  Ultrafilter.map (Classical.choose (Quot.exists_rep x)) U

@[simp]
theorem liftPred_ofSeq {P : alpha → Prop} (f : iota → alpha) :
    liftPred (U := U) P (ofSeq (U := U) f) ↔ ∀ᶠ i in (U : Filter iota), P (f i) :=
  by
    simpa [liftPred, ofSeq] using
      (Germ.liftPred_coe (l := (U : Filter iota)) (p := P) (f := f))

@[simp]
theorem liftRel_ofSeq {R : alpha → beta → Prop} (f : iota → alpha) (g : iota → beta) :
    liftRel (U := U) R (ofSeq (U := U) f) (ofSeq (U := U) g) ↔
      ∀ᶠ i in (U : Filter iota), R (f i) (g i) :=
  by
    simpa [liftRel, ofSeq] using
      (Germ.liftRel_coe (l := (U : Filter iota)) (r := R) (f := f) (g := g))

@[simp]
theorem liftPred_std [NeBot (U : Filter iota)] {P : alpha → Prop} {a : alpha} :
    liftPred (U := U) P (std a : Ultrapower U alpha) ↔ P a := by
  simpa [std, ultraConst, liftPred] using
    (Germ.liftPred_const_iff (l := (U : Filter iota)) (p := P) (x := a))

@[simp]
theorem liftRel_std [NeBot (U : Filter iota)] {R : alpha → beta → Prop} {a : alpha} {b : beta} :
    liftRel (U := U) R (std a : Ultrapower U alpha) (std b) ↔ R a b := by
  simpa [std, ultraConst, liftRel] using
    (Germ.liftRel_const_iff (l := (U : Filter iota)) (r := R) (x := a) (y := b))

@[simp]
theorem lift_std (f : alpha → beta) (a : alpha) :
    lift (U := U) f (std a : Ultrapower U alpha) = (std (f a) : Ultrapower U beta) := by
  simpa [std, ultraConst, lift, map] using (Germ.map_const (l := (U : Filter iota)) (a := a) (f := f))

theorem forall_ofSeq_iff (P : Ultrapower U alpha → Prop) :
    (∀ x : Ultrapower U alpha, P x) ↔ ∀ f : iota → alpha, P (ofSeq (U := U) f) := by
  constructor
  · intro h f
    exact h (ofSeq f)
  · intro h x
    rcases ofSeq_surjective x with ⟨f, hf⟩
    simpa [hf] using h f

theorem exists_ofSeq_iff (P : Ultrapower U alpha → Prop) :
    (∃ x : Ultrapower U alpha, P x) ↔ ∃ f : iota → alpha, P (ofSeq (U := U) f) := by
  constructor
  · rintro ⟨x, hx⟩
    rcases ofSeq_surjective x with ⟨f, hf⟩
    refine ⟨f, ?_⟩
    simpa [hf.symm] using hx
  · rintro ⟨f, hf⟩
    exact ⟨ofSeq f, hf⟩

theorem forall_std_iff [NeBot (U : Filter iota)] (P : alpha → Prop) :
    (∀ a : alpha, P a) ↔ (∀ x : Ultrapower U alpha, liftPred (U := U) P x) := by
  constructor
  · intro h x
    rcases ofSeq_surjective x with ⟨f, hf⟩
    have h' : ∀ᶠ i in (U : Filter iota), P (f i) :=
      Filter.Eventually.of_forall fun i => h (f i)
    have hx : x = ofSeq (U := U) f := hf.symm
    simpa [hx, liftPred_ofSeq] using h'
  · intro h a
    simpa using (h (std a))

section LogicalConnectives

variable {P Q : alpha → Prop}

theorem liftPred_and (x : Ultrapower U alpha) :
    liftPred (U := U) (fun a => P a ∧ Q a) x ↔
      liftPred (U := U) P x ∧ liftPred (U := U) Q x := by
  rcases ofSeq_surjective x with ⟨f, hf⟩
  have hx : x = ofSeq (U := U) f := hf.symm
  simpa [hx, liftPred_ofSeq] using
    (eventually_and (f := (U : Filter iota)) (p := fun i => P (f i))
      (q := fun i => Q (f i)))

theorem liftPred_or (x : Ultrapower U alpha) :
    liftPred (U := U) (fun a => P a ∨ Q a) x ↔
      liftPred (U := U) P x ∨ liftPred (U := U) Q x := by
  rcases ofSeq_surjective x with ⟨f, hf⟩
  have hx : x = ofSeq (U := U) f := hf.symm
  simpa [hx, liftPred_ofSeq] using
    (Ultrafilter.eventually_or (f := U) (p := fun i => P (f i)) (q := fun i => Q (f i)))

theorem liftPred_not (x : Ultrapower U alpha) :
    liftPred (U := U) (fun a => ¬ P a) x ↔ ¬ liftPred (U := U) P x := by
  rcases ofSeq_surjective x with ⟨f, hf⟩
  have hx : x = ofSeq (U := U) f := hf.symm
  simpa [hx, liftPred_ofSeq] using
    (Ultrafilter.eventually_not (f := U) (p := fun i => P (f i)))

theorem liftPred_imp (x : Ultrapower U alpha) :
    liftPred (U := U) (fun a => P a → Q a) x ↔
      (liftPred (U := U) P x → liftPred (U := U) Q x) := by
  rw [show (fun a => P a → Q a) = (fun a => ¬ P a ∨ Q a) by ext; tauto]
  rw [liftPred_or, liftPred_not]
  tauto

theorem liftPred_exists_iff {Q : alpha → beta → Prop} {x : Ultrapower U alpha} :
    liftPred (U := U) (fun a => ∃ b, Q a b) x ↔
      ∃ y : Ultrapower U beta, liftRel (U := U) Q x y := by
  classical
  rcases ofSeq_surjective x with ⟨f, hf⟩
  have hx : x = ofSeq (U := U) f := hf.symm
  simp only [hx, liftPred_ofSeq]
  constructor
  · intro h
    have : Nonempty beta := by
      obtain ⟨n, hn⟩ := Filter.nonempty_of_mem h
      obtain ⟨b, _⟩ := hn
      exact ⟨b⟩
    let g (n : iota) : beta := if h : ∃ b, Q (f n) b then Classical.choose h else Classical.choice ‹_›
    refine ⟨ofSeq g, ?_⟩
    rw [liftRel_ofSeq]
    filter_upwards [h] with n hn
    have h_ex : ∃ b, Q (f n) b := hn
    simp [g, h_ex, dif_pos]
    exact Classical.choose_spec h_ex
  · rintro ⟨y, hy⟩
    rcases ofSeq_surjective y with ⟨g, hg⟩
    have hy' : ∀ᶠ n in (U : Filter iota), Q (f n) (g n) := by
      simpa [hg.symm, liftRel_ofSeq] using hy
    filter_upwards [hy'] with n hn
    exact ⟨g n, hn⟩

end LogicalConnectives

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
