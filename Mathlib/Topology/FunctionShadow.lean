/-
Copyright (c) 2024 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
module

public import Mathlib.Order.Filter.Germ.Star
public import Mathlib.Topology.NonstandardAnalysis

/-!
# Shadow of Internal Functions

This file defines the shadow (standard part) of internal functions in nonstandard analysis.

## Main Definitions

* `Hyper.app`: Application of an internal function to a hyperreal.
* `Hyper.HasShadow`: Predicate indicating that an internal function maps standard points to near-standard points.
* `Hyper.Shadow`: The standard function corresponding to an internal function.

-/

open Filter Topology Set
open scoped NonstandardAnalysis

namespace Hyper

variable {ι : Type*} [Infinite ι] {α β : Type*}

/-- Application of an internal function `f : * (α → β)` to a hyperreal `x : * α`. -/
def app (f : Hyper ι (α → β)) (x : Hyper ι α) : Hyper ι β :=
  Germ.map₂ (fun g y => g y) f x

scoped[NonstandardAnalysis] infixr:90 " ⋆ " => Hyper.app

theorem app_std (f : α → β) (x : α) : (std f : Hyper ι (α → β)) ⋆ (std x : Hyper ι α) = std (f x) :=
  rfl

/-- An internal function `f` has a shadow if it maps every standard point to a near-standard point.
This is equivalent to saying `f` is S-continuous at every standard point. -/
def HasShadow [TopologicalSpace β] (f : Hyper ι (α → β)) : Prop :=
  ∀ x : α, ∃ y_st : β, (f ⋆ (std x : Hyper ι α)) ≈ y_st

/-- The shadow of an internal function `f`.
It is the standard function `g : α → β` such that `g(x) = st(f(*x))`.
If `f` does not have a shadow at `x`, the value is unspecified (garbage). -/
noncomputable def Shadow [TopologicalSpace β] [Nonempty β] (f : Hyper ι (α → β)) (x : α) : β :=
  st (f ⋆ (std x : Hyper ι α))

theorem shadow_def [TopologicalSpace β] [Nonempty β] (f : Hyper ι (α → β)) (x : α) :
    Shadow f x = st (f ⋆ (std x : Hyper ι α)) :=
  rfl

theorem shadow_std_fun [TopologicalSpace β] [T2Space β] [Nonempty β] (f : α → β) :
    Shadow (std f : Hyper ι (α → β)) = f := by
  ext x
  rw [shadow_def, app_std]
  exact st_std (f x)

end Hyper
