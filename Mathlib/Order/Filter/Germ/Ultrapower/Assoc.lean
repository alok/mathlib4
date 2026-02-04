/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
module

public import Mathlib.Order.Filter.Germ.Ultrapower.Curry

/-!
# Associativity tools for ultrapowers

This file provides minimal infrastructure for reorganizing nested ultrapowers by using the
one-level curried equivalence, with simp lemmas for transfer and automation.
-/

@[expose] public section

namespace Filter

namespace Ultrapower

variable {ι κ : Type*} (U : Ultrafilter ι) (V : Ultrafilter κ)
variable {α β : Type*}

/-- Uncurry an ultrapower over the curried ultrafilter. -/
noncomputable abbrev uncurryEquiv :
    Ultrapower (U.curry V) α ≃ Ultrapower U (Ultrapower V α) :=
  ultrapowerCurryEquiv (U := U) (V := V) (α := α)

/-- Curry a nested ultrapower into a single ultrapower. -/
noncomputable abbrev curryUltrapowerEquiv :
    Ultrapower U (Ultrapower V α) ≃ Ultrapower (U.curry V) α :=
  (uncurryEquiv (U := U) (V := V) (α := α)).symm

@[simp] theorem uncurryEquiv_ofSeq (f : ι × κ → α) :
    uncurryEquiv (U := U) (V := V) (α := α) (ofSeq (U := U.curry V) f) =
      ofSeq (U := U) (fun i => ofSeq (U := V) (fun j => f (i, j))) := by
  rfl

@[simp] theorem uncurryEquiv_std (a : α) :
    uncurryEquiv (U := U) (V := V) (α := α) (std (U := U.curry V) a) =
      (std (U := U) (std (U := V) a) : Ultrapower U (Ultrapower V α)) := by
  rfl

theorem liftPred_uncurryEquiv (P : α → Prop) (x : Ultrapower (U.curry V) α) :
    liftPred (U := U.curry V) P x ↔
      liftPred (U := U) (fun y => liftPred (U := V) P y)
        (uncurryEquiv (U := U) (V := V) (α := α) x) := by
  refine Ultrapower.inductionOn (U := U.curry V) x ?_
  intro f
  simp [Filter.eventually_curry_iff]

theorem liftRel_uncurryEquiv (R : α → β → Prop)
    (x : Ultrapower (U.curry V) α) (y : Ultrapower (U.curry V) β) :
    liftRel (U := U.curry V) R x y ↔
      liftRel (U := U) (fun a b => liftRel (U := V) R a b)
        (uncurryEquiv (U := U) (V := V) (α := α) x)
        (uncurryEquiv (U := U) (V := V) (α := β) y) := by
  refine Ultrapower.inductionOn (U := U.curry V) x ?_
  intro f
  refine Ultrapower.inductionOn (U := U.curry V) y ?_
  intro g
  simp [Filter.eventually_curry_iff]

end Ultrapower

end Filter
