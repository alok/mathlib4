/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
module

public import Mathlib.Order.Filter.Germ.Ultrapower

/-!
# Dynamic-static bridges for ultrapowers

This file packages generic equivalences between:

* dynamic sequence statements (`∀ᶠ i, ...` along an ultrafilter), and
* static ideal-element statements (`liftPred` / `liftRel` on ultrapowers).
-/

@[expose] public section

namespace Filter

namespace Ultrapower

variable {ι : Type*} {U : Ultrafilter ι}
variable {α β : Type*}

theorem liftPred_iff_eventually (P : α → Prop) (f : ι → α) :
    liftPred (U := U) P (ofSeq (U := U) f) ↔ ∀ᶠ i in (U : Filter ι), P (f i) :=
  liftPred_ofSeq (U := U) (P := P) f

theorem liftRel_iff_eventually (R : α → β → Prop) (f : ι → α) (g : ι → β) :
    liftRel (U := U) R (ofSeq (U := U) f) (ofSeq (U := U) g) ↔
      ∀ᶠ i in (U : Filter ι), R (f i) (g i) :=
  liftRel_ofSeq (U := U) (R := R) f g

theorem liftPred_iff_eventually_of_rep (P : α → Prop) {x : Ultrapower U α}
    {f : ι → α} (hx : x = ofSeq (U := U) f) :
    liftPred (U := U) P x ↔ ∀ᶠ i in (U : Filter ι), P (f i) :=
  liftPred_iff_eventually_of_eq (U := U) (P := P) hx

theorem liftRel_iff_eventually_of_rep (R : α → β → Prop)
    {x : Ultrapower U α} {y : Ultrapower U β} {f : ι → α} {g : ι → β}
    (hx : x = ofSeq (U := U) f) (hy : y = ofSeq (U := U) g) :
    liftRel (U := U) R x y ↔ ∀ᶠ i in (U : Filter ι), R (f i) (g i) :=
  liftRel_iff_eventually_of_eq (U := U) (R := R) hx hy

theorem forall_liftPred_iff_forall_eventually (P : α → Prop) :
    (∀ x : Ultrapower U α, liftPred (U := U) P x) ↔
      ∀ f : ι → α, ∀ᶠ i in (U : Filter ι), P (f i) := by
  rw [forall_ofSeq_iff]
  simp [liftPred_ofSeq]

theorem exists_liftPred_iff_exists_eventually (P : α → Prop) :
    (∃ x : Ultrapower U α, liftPred (U := U) P x) ↔
      ∃ f : ι → α, ∀ᶠ i in (U : Filter ι), P (f i) := by
  rw [exists_ofSeq_iff]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, (liftPred_ofSeq (U := U) (P := P) f).1 hf⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, (liftPred_ofSeq (U := U) (P := P) f).2 hf⟩

theorem forall_liftRel_iff_forall_eventually (R : α → β → Prop) :
    (∀ x : Ultrapower U α, ∀ y : Ultrapower U β, liftRel (U := U) R x y) ↔
      ∀ f : ι → α, ∀ g : ι → β, ∀ᶠ i in (U : Filter ι), R (f i) (g i) := by
  constructor
  · intro h f g
    exact (liftRel_ofSeq (U := U) (R := R) f g).1 (h (ofSeq (U := U) f) (ofSeq (U := U) g))
  · intro h x y
    rcases ofSeq_surjective (U := U) x with ⟨f, rfl⟩
    rcases ofSeq_surjective (U := U) y with ⟨g, rfl⟩
    exact (liftRel_ofSeq (U := U) (R := R) f g).2 (h f g)

end Ultrapower

end Filter
