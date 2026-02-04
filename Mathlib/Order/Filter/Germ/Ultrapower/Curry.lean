/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
module

public import Mathlib.Order.Filter.Germ.Ultrapower
public import Mathlib.Order.Filter.Germ.Curry
public import Mathlib.Order.Filter.Ultrafilter.Curry

/-!
# Curried ultrapowers

This file packages the one-level equivalence between iterated ultrapowers and germs over the
curried filter.
-/

@[expose] public section

namespace Filter

namespace Ultrapower

variable {ι κ α : Type*} (U : Ultrafilter ι) (V : Ultrafilter κ)

/-- Germs over the curried filter correspond to iterated ultrapowers. -/
noncomputable def curryEquiv :
    Germ ((U : Filter ι).curry (V : Filter κ)) α ≃
      Ultrapower U (Ultrapower V α) :=
  Germ.curryEquiv (l := (U : Filter ι)) (m := (V : Filter κ)) α

/-- Ultrapowers over the curried ultrafilter correspond to iterated ultrapowers. -/
noncomputable def ultrapowerCurryEquiv :
    Ultrapower (U.curry V) α ≃ Ultrapower U (Ultrapower V α) := by
  simpa [Ultrafilter.coe_curry] using (curryEquiv (U := U) (V := V) (α := α))

end Ultrapower

end Filter
