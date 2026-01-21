/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
module

import Mathlib.Order.Filter.Germ.Ultrapower
import Mathlib.Order.Filter.Germ.Star

/-!
# Saturation for Ultrapowers

This file packages saturation hypotheses for ultrafilter-generic ultrapowers
behind a typeclass. This hides cardinal bookkeeping in user-facing statements.
-/

namespace Filter

/-- `Saturated U kappa` means that the ultrapower over `U` realizes any finitely
consistent family of predicates indexed by `kappa`. -/
class Saturated (U : Ultrafilter iota) (kappa : Type*) : Prop :=
  (sat :
    forall {alpha : Type*} {P : kappa -> alpha -> Prop},
      (forall F : Finset kappa, exists x : Ultrapower U alpha,
        forall k, Membership.mem k F -> Ultrapower.liftPred (P k) x) ->
      exists x : Ultrapower U alpha, forall k : kappa, Ultrapower.liftPred (P k) x)

/-- Abbreviation for countable saturation. -/
abbrev CountablySaturated (U : Ultrafilter iota) : Prop := Saturated U Nat

/-- The chosen nonstandard ultrafilter gives saturation once `kappa` embeds into the index type. -/
instance nonstandardUltrafilter_saturated (iota : Type*) [RegularIndex iota] (kappa : Type*)
    [Nonempty (Embedding kappa iota)] :
    Saturated (nonstandardUltrafilter iota) kappa := by
  classical
  refine Saturated.mk ?_
  intro alpha P hfin
  cases (inferInstance : Nonempty (Embedding kappa iota)) with
  | intro e =>
    have hfin' :
        forall F : Finset kappa, exists x : Hyper iota alpha,
          forall k, Membership.mem k F -> Hyper.liftPred (P k) x := by
      simpa [Filter.Ultrapower, Ultrapower.liftPred, Hyper.liftPred] using hfin
    cases Hyper.cardinal_saturation (iota := iota) (kappa := kappa) e hfin' with
    | intro x hx =>
      refine Exists.intro x ?_
      intro k
      simpa [Filter.Ultrapower, Ultrapower.liftPred, Hyper.liftPred] using hx k

end Filter
