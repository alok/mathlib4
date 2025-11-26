/-
Copyright (c) 2024 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Mathlib.Order.Filter.Germ.Basic

/-!
# Bridge between Germ and Product

This file establishes the equivalence between `Filter.Germ l β` and
`Filter.Product l (fun _ => β)`. This bridge allows us to connect the
hypernatural/hyperrational constructions (built on `Germ`) with the
model-theoretic ultraproduct framework (built on `Product`).

## Main definitions

* `Filter.Germ.prodEquiv`: The equivalence between `Germ l β` and `Product l (fun _ => β)`

## Main results

* The equivalence respects the quotient structure
-/

namespace Filter

variable {α β : Type*} {l : Filter α}

/-- The setoid on `α → β` underlying `Germ l β` is the same as the setoid on
`(a : α) → β` underlying `Product l (fun _ => β)` when we view `α → β` as `(a : α) → β`. -/
theorem germSetoid_eq_productSetoid_const :
    (germSetoid l β).r = (productSetoid l (fun _ : α => β)).r := rfl

/-- An equivalence between `Germ l β` and `Product l (fun _ => β)`.

This bridge connects the `Germ`-based hypernatural construction with the
`Product`-based ultraproduct construction from model theory. -/
def Germ.prodEquiv : Germ l β ≃ Product l (fun _ : α => β) :=
  Quotient.congr (Equiv.refl _) (fun _ _ => Iff.rfl)

namespace Germ

@[simp]
theorem prodEquiv_ofFun (f : α → β) :
    prodEquiv (ofFun f : Germ l β) = (f : Product l (fun _ => β)) := rfl

@[simp]
theorem prodEquiv_symm_coe (f : α → β) :
    prodEquiv.symm (f : Product l (fun _ => β)) = (ofFun f : Germ l β) := rfl

/-- Coercion commutes with the product equivalence. -/
theorem prodEquiv_coe (f : α → β) :
    prodEquiv (f : Germ l β) = (f : Product l (fun _ => β)) := rfl

end Germ

end Filter
