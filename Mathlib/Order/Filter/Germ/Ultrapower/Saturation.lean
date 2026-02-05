/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
module

public import Mathlib.Order.Filter.Germ.Ultrapower
public import Mathlib.Order.Filter.Ultrafilter.Nonstandard
public import Mathlib.Data.Finset.Preimage
public import Mathlib.Logic.Embedding.Basic

/-!
# Saturation for Ultrapowers

This file packages saturation hypotheses for ultrafilter-generic ultrapowers
behind a typeclass. This hides cardinal bookkeeping in user-facing statements.
-/

@[expose] public section

universe u v

namespace Filter

variable {iota : Type u}

/-- `Saturated U kappa` means that the ultrapower over `U` realizes any finitely
consistent family of predicates indexed by `kappa`. -/
class Saturated (U : Ultrafilter iota) (kappa : Type v) : Prop where
  sat :
    ∀ {alpha : Type v} {P : kappa → alpha → Prop},
      (∀ F : Finset kappa, ∃ x : Ultrapower U alpha,
        ∀ k ∈ F, Ultrapower.liftPred (U := U) (P k) x) →
      ∃ x : Ultrapower U alpha, ∀ k : kappa, Ultrapower.liftPred (U := U) (P k) x

/-- Abbreviation for countable saturation. -/
abbrev CountablySaturated (U : Ultrafilter iota) : Prop := Saturated U Nat

namespace Ultrapower

variable {iota : Type u} {U : Ultrafilter iota} {kappa : Type v}

/-- Saturation for an arbitrary ultrafilter with a regularizing family. -/
theorem cardinal_saturation (e : kappa ↪ iota) {alpha : Type v} {P : kappa → alpha → Prop}
    [RegularizingFamily U]
    (hfin : ∀ F : Finset kappa, ∃ x : Ultrapower U alpha,
      ∀ k ∈ F, Ultrapower.liftPred (U := U) (P k) x) :
    ∃ x : Ultrapower U alpha, ∀ k : kappa, Ultrapower.liftPred (U := U) (P k) x := by
  classical
  let E := RegularizingFamily.family (U := U)
  have h_exists : ∀ i, ∃ a : alpha, ∀ k, e k ∈ E i → P k a := by
    intro i
    let K_i : Finset kappa := (E i).preimage e e.injective.injOn
    obtain ⟨x, hx⟩ := hfin K_i
    rcases Ultrapower.ofSeq_surjective x with ⟨u, hu⟩
    have hx' : ∀ k ∈ K_i, Ultrapower.liftPred (U := U) (P k) (Ultrapower.ofSeq (U := U) u) := by
      simpa [hu] using hx
    let Y := {j | ∀ k ∈ K_i, P k (u j)}
    have hY : Y ∈ (U : Filter iota) := by
      change ∀ᶠ j in (U : Filter iota), ∀ k ∈ K_i, P k (u j)
      refine (Finset.eventually_all (I := K_i)).2 ?_
      intro k hk
      specialize hx' k hk
      rwa [Ultrapower.liftPred_ofSeq] at hx'
    obtain ⟨j, hj⟩ := Filter.nonempty_of_mem hY
    refine ⟨u j, ?_⟩
    intro k hke
    have hk : k ∈ K_i := Finset.mem_preimage.mpr hke
    exact hj k hk
  choose f hf using h_exists
  refine ⟨Ultrapower.ofSeq (U := U) f, ?_⟩
  intro k
  change ∀ᶠ i in (U : Filter iota), P k (f i)
  let W_k := {i | e k ∈ E i}
  have hW : W_k ∈ (U : Filter iota) := by
    simpa [W_k, E] using (RegularizingFamily.family_mem (U := U) (a := e k))
  apply Filter.mem_of_superset hW
  intro i hi
  exact hf i k hi

end Ultrapower

/-- Any ultrafilter equipped with a regularizing family is saturated once `kappa` embeds
into the index type. -/
instance ultrafilter_saturated (U : Ultrafilter iota) [RegularizingFamily U]
    (kappa : Type*)
    [Nonempty (kappa ↪ iota)] :
    Saturated U kappa := by
  classical
  refine Saturated.mk ?_
  intro alpha P hfin
  cases (inferInstance : Nonempty (kappa ↪ iota)) with
  | intro e =>
    exact Ultrapower.cardinal_saturation (U := U) (kappa := kappa) e hfin

end Filter
