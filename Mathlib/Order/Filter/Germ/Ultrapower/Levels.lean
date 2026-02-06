/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
module

public import Mathlib.Order.Filter.Germ.Ultrapower.Assoc

/-!
# Ultrapower levels

This file introduces lightweight level wrappers for iterated ultrapowers.
It keeps the API close to `Ultrapower` while making two-level normalization
via curried ultrafilters explicit.
-/

@[expose] public section

namespace Filter

namespace Ultrapower

variable {ι κ : Type*} {U : Ultrafilter ι} {V : Ultrafilter κ}
variable {α : Type*}

/-- Level-1 ideal elements over `U`. -/
abbrev Level1 (U : Ultrafilter ι) (α : Type*) : Type _ := Ultrapower U α

/-- Level-2 ideal elements: an ultrapower of an ultrapower. -/
abbrev Level2 (U : Ultrafilter ι) (V : Ultrafilter κ) (α : Type*) : Type _ :=
  Ultrapower U (Ultrapower V α)

/-- Normalize a level-2 ultrapower into one ultrapower over a curried ultrafilter. -/
noncomputable abbrev level2ToCurried :
    Level2 U V α ≃ Ultrapower (U.curry V) α :=
  curryUltrapowerEquiv (U := U) (V := V) (α := α)

/-- Denormalize from the curried ultrapower back to level-2 form. -/
noncomputable abbrev curriedToLevel2 :
    Ultrapower (U.curry V) α ≃ Level2 U V α :=
  uncurryEquiv (U := U) (V := V) (α := α)

@[simp] theorem curriedToLevel2_ofSeq (f : ι × κ → α) :
    curriedToLevel2 (U := U) (V := V) (α := α) (ofSeq (U := U.curry V) f) =
      ofSeq (U := U) (fun i => ofSeq (U := V) (fun j => f (i, j))) :=
  uncurryEquiv_ofSeq (U := U) (V := V) (α := α) f

@[simp] theorem level2ToCurried_ofSeq (f : ι × κ → α) :
    level2ToCurried (U := U) (V := V) (α := α)
      (ofSeq (U := U) (fun i => ofSeq (U := V) (fun j => f (i, j)))) =
        ofSeq (U := U.curry V) f := by
  apply (curriedToLevel2 (U := U) (V := V) (α := α)).injective
  simp

end Ultrapower

end Filter
