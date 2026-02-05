/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
module

public import Mathlib.Order.Filter.Germ.Ultrapower
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Star and monad for ultrapowers

This file defines the star map and near-standardness for ultrapower-generic germs,
relying only on an arbitrary ultrafilter `U`.
-/

@[expose] public section

namespace Filter

namespace Ultrapower

variable {iota : Type*} {U : Ultrafilter iota}
variable {α β : Type*}

/-- The star map sends a set `s` to its ultrapower extension. -/
def star (s : Set α) : Set (Ultrapower U α) :=
  {x | liftPred (U := U) (· ∈ s) x}

theorem mem_star_iff (s : Set α) (x : Ultrapower U α) :
    x ∈ star (U := U) s ↔ liftPred (U := U) (· ∈ s) x := Iff.rfl

theorem star_empty : star (U := U) (∅ : Set α) = (∅ : Set (Ultrapower U α)) := by
  ext x
  rw [mem_star_iff, Set.mem_empty_iff_false]
  induction x using Ultrapower.inductionOn (U := U) with
  | h f =>
    rw [liftPred_ofSeq]
    simp [Set.mem_empty_iff_false, Filter.eventually_false_iff_eq_bot, U.neBot.ne]

theorem star_univ : star (U := U) (Set.univ : Set α) = (Set.univ : Set (Ultrapower U α)) := by
  ext x
  induction x using Ultrapower.inductionOn (U := U) with
  | h f =>
    simp [star, liftPred_ofSeq]

theorem star_union (s t : Set α) :
    star (U := U) (s ∪ t) = star (U := U) s ∪ star (U := U) t := by
  ext x
  induction x using Ultrapower.inductionOn (U := U) with
  | h f =>
    simp [star, liftPred_ofSeq, Ultrafilter.eventually_or, Set.mem_union]

theorem star_inter (s t : Set α) :
    star (U := U) (s ∩ t) = star (U := U) s ∩ star (U := U) t := by
  ext x
  induction x using Ultrapower.inductionOn (U := U) with
  | h f =>
    simp [star, liftPred_ofSeq, Filter.eventually_and, Set.mem_inter_iff]

theorem star_compl (s : Set α) : star (U := U) (sᶜ) = (star (U := U) s)ᶜ := by
  ext x
  induction x using Ultrapower.inductionOn (U := U) with
  | h f =>
    change
      liftPred (U := U) (· ∈ sᶜ) (ofSeq (U := U) f) ↔
        ¬ liftPred (U := U) (· ∈ s) (ofSeq (U := U) f)
    rw [liftPred_ofSeq, liftPred_ofSeq]
    have hnot := (Ultrafilter.eventually_not (f := U) (p := fun i => f i ∈ s))
    exact hnot

/-- The monadic filter operation: the intersection of stars of all elements of `l`. -/
def monadic (l : Filter α) : Set (Ultrapower U α) :=
  ⋂ S ∈ l, star (U := U) S

theorem mem_monadic_iff (l : Filter α) (x : Ultrapower U α) :
    x ∈ monadic (U := U) l ↔ ∀ S ∈ l, x ∈ star (U := U) S :=
  Set.mem_iInter₂

theorem monadic_le {l₁ l₂ : Filter α} (h : l₁ ≤ l₂) :
    monadic (U := U) l₁ ⊆ monadic (U := U) l₂ :=
  Set.biInter_subset_biInter_left h

theorem monadic_principal (s : Set α) :
    monadic (U := U) (Filter.principal s) = (star (U := U) s : Set (Ultrapower U α)) := by
  ext x
  constructor
  · intro hx
    have hx' := (mem_monadic_iff (U := U) (l := Filter.principal s) (x := x)).1 hx
    exact hx' s (by intro _ hs; exact hs)
  · intro hx
    refine (mem_monadic_iff (U := U) (l := Filter.principal s) (x := x)).2 ?_
    intro S hS
    rw [mem_star_iff] at hx ⊢
    induction x using Ultrapower.inductionOn (U := U) with
    | h f =>
      simp only [liftPred_ofSeq] at hx ⊢
      filter_upwards [hx] with i hi
      exact hS hi

theorem monadic_iInf {ι' : Type*} {f : ι' → Filter α} :
    monadic (U := U) (⨅ i, f i) = ⋂ i, monadic (U := U) (f i) := by
  ext x
  constructor
  · intro hx
    refine (Set.mem_iInter).2 ?_
    intro i
    apply (mem_monadic_iff (U := U) (l := f i) (x := x)).2
    intro S hS
    have hx' := (mem_monadic_iff (U := U) (l := ⨅ i, f i) (x := x)).1 hx
    exact hx' S (Filter.mem_iInf_of_mem i hS)
  · intro hx
    apply (mem_monadic_iff (U := U) (l := ⨅ i, f i) (x := x)).2
    intro S hS
    rcases (Filter.mem_iInf (s := f) (U := S)).1 hS with ⟨I, hIfin, V, hV, rfl⟩
    classical
    have h_mem : ∀ i : I, x ∈ star (U := U) (V i) := by
      intro i
      have hx_i : x ∈ monadic (U := U) (f i) := by
        simpa using (Set.mem_iInter.1 hx i)
      exact (mem_monadic_iff (U := U) (l := f i) (x := x)).1 hx_i (V i) (hV i)
    have h_star_inter :
        x ∈ star (U := U) (⋂ i : I, V i) := by
      have h_star_inter_finset :
          ∀ s : Finset I,
            (∀ i ∈ s, x ∈ star (U := U) (V i)) →
              x ∈ star (U := U) (⋂ i ∈ s, V i) := by
        classical
        refine Finset.induction ?base ?step
        · intro _; simp [star_univ]
        · intro a s ha hs hmem
          have ha_mem : x ∈ star (U := U) (V a) := hmem a (by simp [ha])
          have hs_mem : x ∈ star (U := U) (⋂ i ∈ s, V i) := hs (by
            intro i hi
            exact hmem i (by simp [hi]))
          have hx_mem : x ∈ star (U := U) (V a ∩ ⋂ i ∈ s, V i) := by
            simpa [star_inter, Set.mem_inter_iff] using And.intro ha_mem hs_mem
          simpa [Finset.set_biInter_insert, ha] using hx_mem
      haveI := hIfin.fintype
      have h_univ :
          (⋂ i ∈ (Finset.univ : Finset I), V i) = ⋂ i : I, V i := by
        ext y; simp [Finset.mem_univ]
      have hx_univ := h_star_inter_finset (Finset.univ : Finset I) (by
        intro i hi
        simpa using h_mem i)
      simpa [h_univ] using hx_univ
    simpa using h_star_inter

section Topology

variable [TopologicalSpace α]

/-- The monad of a filter `F`: points in the star of every set of `F`. -/
def monad (F : Filter α) : Set (Ultrapower U α) :=
  {x | ∀ S ∈ F, liftPred (U := U) (· ∈ S) x}

/-- A point is near standard to `y` if it lies in the monad of `𝓝 y`. -/
def IsNearStandard (x : Ultrapower U α) (y : α) : Prop :=
  x ∈ monad (U := U) (nhds y)

theorem isNearStandard_def (x : Ultrapower U α) (y : α) :
    IsNearStandard (U := U) x y ↔ ∀ S ∈ nhds y, x ∈ star (U := U) S := by
  simp [IsNearStandard, monad, star]

theorem IsNearStandard.unique [T2Space α] {x : Ultrapower U α} {r s : α}
    (hr : IsNearStandard (U := U) x r) (hs : IsNearStandard (U := U) x s) : r = s := by
  by_contra hne
  obtain ⟨f, rfl⟩ := ofSeq_surjective (U := U) x
  obtain ⟨S, T, hS, hT, hST⟩ := t2_separation_nhds hne
  have hxS : ∀ᶠ i in (U : Filter iota), f i ∈ S := by
    simpa [IsNearStandard, monad, liftPred_ofSeq] using (hr S hS)
  have hxT : ∀ᶠ i in (U : Filter iota), f i ∈ T := by
    simpa [IsNearStandard, monad, liftPred_ofSeq] using (hs T hT)
  have hx_inter : ∀ᶠ i in (U : Filter iota), f i ∈ S ∩ T := hxS.and hxT
  have h_empty : S ∩ T = ∅ := Set.disjoint_iff_inter_eq_empty.mp hST
  simp [h_empty, Filter.eventually_false_iff_eq_bot, U.neBot.ne] at hx_inter

/-- The standard part is unique in any Hausdorff space. -/
theorem st_unique [T2Space α] {x : Ultrapower U α} {r s : α}
    (hr : IsNearStandard (U := U) x r) (hs : IsNearStandard (U := U) x s) : r = s :=
  hr.unique hs

/-- The standard part of a near-standard element (topological definition). -/
noncomputable def st [Nonempty α] (x : Ultrapower U α) : α :=
  Classical.epsilon (fun a => IsNearStandard (U := U) x a)

lemma st_eq_of_isNearStandard [T2Space α] [Nonempty α]
    (x : Ultrapower U α) (y : α) (h : IsNearStandard (U := U) x y) : st (U := U) x = y := by
  apply IsNearStandard.unique (U := U) (Classical.epsilon_spec ⟨y, h⟩) h

end Topology

end Ultrapower

end Filter
