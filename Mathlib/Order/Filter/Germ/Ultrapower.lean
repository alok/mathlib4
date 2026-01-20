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

/-- Map a function to the ultrapower. -/
def map (f : alpha -> beta) : Ultrapower U alpha -> Ultrapower U beta :=
  Germ.map f

/-- Map a binary function to the ultrapower. -/
noncomputable def map2 (f : alpha -> beta -> gamma) :
    Ultrapower U alpha -> Ultrapower U beta -> Ultrapower U gamma :=
  Germ.map₂ f

/-- Lift a predicate to the ultrapower. -/
def mapPred (P : alpha -> Prop) : Ultrapower U alpha -> Prop :=
  Germ.LiftPred P

/-- Lift a relation to the ultrapower. -/
def mapRel (R : alpha -> beta -> Prop) :
    Ultrapower U alpha -> Ultrapower U beta -> Prop :=
  Germ.LiftRel R

/-- The ultrafilter on the base type represented by a point of the ultrapower. -/
noncomputable def ultrafilterOf (x : Ultrapower U alpha) : Ultrafilter alpha :=
  Ultrafilter.map (Classical.choose (Quot.exists_rep x)) U

end Ultrapower

end Filter
