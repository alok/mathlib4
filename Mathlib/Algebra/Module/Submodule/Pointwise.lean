/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.GroupTheory.Subgroup.Pointwise
import Mathlib.LinearAlgebra.Span
import Mathlib.LinearAlgebra.Finsupp

#align_import algebra.module.submodule.pointwise from "leanprover-community/mathlib"@"48085f140e684306f9e7da907cd5932056d1aded"

/-! # Pointwise instances on `Submodule`s

This file provides:

* `Submodule.pointwiseNeg`

and the actions

* `Submodule.pointwiseDistribMulAction`
* `Submodule.pointwiseMulActionWithZero`

which matches the action of `Set.mulActionSet`.

These actions are available in the `Pointwise` locale.

## Implementation notes

Most of the lemmas in this file are direct copies of lemmas from
`GroupTheory/Submonoid/Pointwise.lean`.
-/


variable {α : Type*} {R : Type*} {M : Type*}

open Pointwise

namespace Submodule

section Neg

section Semiring

variable [Semiring R] [AddCommGroup M] [Module R M]

/-- The submodule with every element negated. Note if `R` is a ring and not just a semiring, this
is a no-op, as shown by `Submodule.neg_eq_self`.

Recall that When `R` is the semiring corresponding to the nonnegative elements of `R'`,
`Submodule R' M` is the type of cones of `M`. This instance reflects such cones about `0`.

This is available as an instance in the `Pointwise` locale. -/
protected def pointwiseNeg : Neg (Submodule R M)
    where neg p :=
    { -p.toAddSubmonoid with
      carrier := -(p : Set M)
      smul_mem' := fun r m hm => Set.mem_neg.2 <| smul_neg r m ▸ p.smul_mem r <| Set.mem_neg.1 hm }
#align submodule.has_pointwise_neg Submodule.pointwiseNeg

scoped[Pointwise] attribute [instance] Submodule.pointwiseNeg

open Pointwise

@[simp]
theorem coe_set_neg (S : Submodule R M) : ↑(-S) = -(S : Set M) :=
  rfl
#align submodule.coe_set_neg Submodule.coe_set_neg

@[simp]
theorem neg_toAddSubmonoid (S : Submodule R M) : (-S).toAddSubmonoid = -S.toAddSubmonoid :=
  rfl
#align submodule.neg_to_add_submonoid Submodule.neg_toAddSubmonoid

@[simp]
theorem mem_neg {g : M} {S : Submodule R M} : g ∈ -S ↔ -g ∈ S :=
  Iff.rfl
#align submodule.mem_neg Submodule.mem_neg

/-- `Submodule.pointwiseNeg` is involutive.

This is available as an instance in the `Pointwise` locale. -/
protected def involutivePointwiseNeg : InvolutiveNeg (Submodule R M)
    where
  neg := Neg.neg
  neg_neg _S := SetLike.coe_injective <| neg_neg _
#align submodule.has_involutive_pointwise_neg Submodule.involutivePointwiseNeg

scoped[Pointwise] attribute [instance] Submodule.involutivePointwiseNeg

@[simp]
theorem neg_le_neg (S T : Submodule R M) : -S ≤ -T ↔ S ≤ T :=
  SetLike.coe_subset_coe.symm.trans Set.neg_subset_neg
#align submodule.neg_le_neg Submodule.neg_le_neg

theorem neg_le (S T : Submodule R M) : -S ≤ T ↔ S ≤ -T :=
  SetLike.coe_subset_coe.symm.trans Set.neg_subset
#align submodule.neg_le Submodule.neg_le

/-- `Submodule.pointwiseNeg` as an order isomorphism. -/
def negOrderIso : Submodule R M ≃o Submodule R M
    where
  toEquiv := Equiv.neg _
  map_rel_iff' := @neg_le_neg _ _ _ _ _
#align submodule.neg_order_iso Submodule.negOrderIso

theorem closure_neg (s : Set M) : span R (-s) = -span R s := by
  apply le_antisymm
  · rw [span_le, coe_set_neg, ← Set.neg_subset, neg_neg]
    exact subset_span
  · rw [neg_le, span_le, coe_set_neg, ← Set.neg_subset]
    exact subset_span
#align submodule.closure_neg Submodule.closure_neg

@[simp]
theorem neg_inf (S T : Submodule R M) : -(S ⊓ T) = -S ⊓ -T :=
  SetLike.coe_injective Set.inter_neg
#align submodule.neg_inf Submodule.neg_inf

@[simp]
theorem neg_sup (S T : Submodule R M) : -(S ⊔ T) = -S ⊔ -T :=
  (negOrderIso : Submodule R M ≃o Submodule R M).map_sup S T
#align submodule.neg_sup Submodule.neg_sup

@[simp]
theorem neg_bot : -(⊥ : Submodule R M) = ⊥ :=
  SetLike.coe_injective <| (Set.neg_singleton 0).trans <| congr_arg _ neg_zero
#align submodule.neg_bot Submodule.neg_bot

@[simp]
theorem neg_top : -(⊤ : Submodule R M) = ⊤ :=
  SetLike.coe_injective <| Set.neg_univ
#align submodule.neg_top Submodule.neg_top

@[simp]
theorem neg_iInf {ι : Sort*} (S : ι → Submodule R M) : (-⨅ i, S i) = ⨅ i, -S i :=
  (negOrderIso : Submodule R M ≃o Submodule R M).map_iInf _
#align submodule.neg_infi Submodule.neg_iInf

@[simp]
theorem neg_iSup {ι : Sort*} (S : ι → Submodule R M) : (-⨆ i, S i) = ⨆ i, -S i :=
  (negOrderIso : Submodule R M ≃o Submodule R M).map_iSup _
#align submodule.neg_supr Submodule.neg_iSup

end Semiring

open Pointwise

@[simp]
theorem neg_eq_self [Ring R] [AddCommGroup M] [Module R M] (p : Submodule R M) : -p = p :=
  ext fun _ => p.neg_mem_iff
#align submodule.neg_eq_self Submodule.neg_eq_self

end Neg

variable [Semiring R] [AddCommMonoid M] [Module R M]

instance pointwiseAddCommMonoid : AddCommMonoid (Submodule R M)
    where
  add := (· ⊔ ·)
  add_assoc _ _ _ := sup_assoc
  zero := ⊥
  zero_add _ := bot_sup_eq
  add_zero _ := sup_bot_eq
  add_comm _ _ := sup_comm
#align submodule.pointwise_add_comm_monoid Submodule.pointwiseAddCommMonoid

@[simp]
theorem add_eq_sup (p q : Submodule R M) : p + q = p ⊔ q :=
  rfl
#align submodule.add_eq_sup Submodule.add_eq_sup

@[simp]
theorem zero_eq_bot : (0 : Submodule R M) = ⊥ :=
  rfl
#align submodule.zero_eq_bot Submodule.zero_eq_bot

instance : CanonicallyOrderedAddMonoid (Submodule R M) :=
  { Submodule.pointwiseAddCommMonoid,
    Submodule.completeLattice with
    zero := 0
    bot := ⊥
    add := (· + ·)
    add_le_add_left := fun _a _b => sup_le_sup_left
    exists_add_of_le := @fun _a b h => ⟨b, (sup_eq_right.2 h).symm⟩
    le_self_add := fun _a _b => le_sup_left }

section

variable [Monoid α] [DistribMulAction α M] [SMulCommClass α R M]

/-- The action on a submodule corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale. -/
protected def pointwiseDistribMulAction : DistribMulAction α (Submodule R M)
    where
  smul a S := S.map (DistribMulAction.toLinearMap R M a : M →ₗ[R] M)
  one_smul S :=
    (congr_arg (fun f : Module.End R M => S.map f) (LinearMap.ext <| one_smul α)).trans S.map_id
  mul_smul _a₁ _a₂ S :=
    (congr_arg (fun f : Module.End R M => S.map f) (LinearMap.ext <| mul_smul _ _)).trans
      (S.map_comp _ _)
  smul_zero _a := map_bot _
  smul_add _a _S₁ _S₂ := map_sup _ _ _
#align submodule.pointwise_distrib_mul_action Submodule.pointwiseDistribMulAction

scoped[Pointwise] attribute [instance] Submodule.pointwiseDistribMulAction

open Pointwise

@[simp]
theorem coe_pointwise_smul (a : α) (S : Submodule R M) : ↑(a • S) = a • (S : Set M) :=
  rfl
#align submodule.coe_pointwise_smul Submodule.coe_pointwise_smul

@[simp]
theorem pointwise_smul_toAddSubmonoid (a : α) (S : Submodule R M) :
    (a • S).toAddSubmonoid = a • S.toAddSubmonoid :=
  rfl
#align submodule.pointwise_smul_to_add_submonoid Submodule.pointwise_smul_toAddSubmonoid

@[simp]
theorem pointwise_smul_toAddSubgroup {R M : Type*} [Ring R] [AddCommGroup M] [DistribMulAction α M]
    [Module R M] [SMulCommClass α R M] (a : α) (S : Submodule R M) :
    (a • S).toAddSubgroup = a • S.toAddSubgroup :=
  rfl
#align submodule.pointwise_smul_to_add_subgroup Submodule.pointwise_smul_toAddSubgroup

theorem smul_mem_pointwise_smul (m : M) (a : α) (S : Submodule R M) : m ∈ S → a • m ∈ a • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set M))
#align submodule.smul_mem_pointwise_smul Submodule.smul_mem_pointwise_smul

/-- See also `Submodule.smul_bot`. -/
@[simp]
theorem smul_bot' (a : α) : a • (⊥ : Submodule R M) = ⊥ :=
  map_bot _
#align submodule.smul_bot' Submodule.smul_bot'

/-- See also `Submodule.smul_sup`. -/
theorem smul_sup' (a : α) (S T : Submodule R M) : a • (S ⊔ T) = a • S ⊔ a • T :=
  map_sup _ _ _
#align submodule.smul_sup' Submodule.smul_sup'

theorem smul_span (a : α) (s : Set M) : a • span R s = span R (a • s) :=
  map_span _ _
#align submodule.smul_span Submodule.smul_span

theorem span_smul (a : α) (s : Set M) : span R (a • s) = a • span R s :=
  Eq.symm (span_image _).symm
#align submodule.span_smul Submodule.span_smul

instance pointwiseCentralScalar [DistribMulAction αᵐᵒᵖ M] [SMulCommClass αᵐᵒᵖ R M]
    [IsCentralScalar α M] : IsCentralScalar α (Submodule R M) :=
  ⟨fun _a S => (congr_arg fun f : Module.End R M => S.map f) <| LinearMap.ext <| op_smul_eq_smul _⟩
#align submodule.pointwise_central_scalar Submodule.pointwiseCentralScalar

@[simp]
theorem smul_le_self_of_tower {α : Type*} [Semiring α] [Module α R] [Module α M]
    [SMulCommClass α R M] [IsScalarTower α R M] (a : α) (S : Submodule R M) : a • S ≤ S := by
  rintro y ⟨x, hx, rfl⟩
  exact smul_of_tower_mem _ a hx
#align submodule.smul_le_self_of_tower Submodule.smul_le_self_of_tower

end

section

variable [Semiring α] [Module α M] [SMulCommClass α R M]

/-- The action on a submodule corresponding to applying the action to every element.

This is available as an instance in the `Pointwise` locale.

This is a stronger version of `Submodule.pointwiseDistribMulAction`. Note that `add_smul` does
not hold so this cannot be stated as a `Module`. -/
protected def pointwiseMulActionWithZero : MulActionWithZero α (Submodule R M) :=
  { Submodule.pointwiseDistribMulAction with
    zero_smul := fun S =>
      (congr_arg (fun f : M →ₗ[R] M => S.map f) (LinearMap.ext <| zero_smul α)).trans S.map_zero }
#align submodule.pointwise_mul_action_with_zero Submodule.pointwiseMulActionWithZero

scoped[Pointwise] attribute [instance] Submodule.pointwiseMulActionWithZero

end

section

variable [Semiring R] [AddCommMonoid M] [Module R M]

/--
let `S ⊆ R` be a set and `N ≤ M` be a submodule, then `S • N` is the smallest submodule containing
all `r • n` where `r ∈ S` and `n ∈ N`.
-/
protected def pointwiseSetSMulSubmodule : HSMul (Set R) (Submodule R M) (Submodule R M) where
  hSMul s N := sInf { p | ∀ ⦃r : R⦄ ⦃n : M⦄, r ∈ s → n ∈ N → r • n ∈ p }

scoped[Pointwise] attribute [instance] Submodule.pointwiseSetSMulSubmodule

variable (s : Set R) (N : Submodule R M)

lemma mem_set_smul_submodule_def (x : M) :
  x ∈ s • N ↔
  x ∈ sInf { p : Submodule R M | ∀ ⦃r : R⦄ {n : M}, r ∈ s → n ∈ N → r • n ∈ p } := Iff.rfl

lemma set_smul_submodule_le (p : Submodule R M)
  (closed_under_smul : ∀ ⦃r : R⦄ ⦃n : M⦄, r ∈ s → n ∈ N → r • n ∈ p) :
  s • N ≤ p :=
sInf_le closed_under_smul

lemma set_smul_submodule_eq_of_le (p : Submodule R M)
  (closed_under_smul : ∀ ⦃r : R⦄ ⦃n : M⦄, r ∈ s → n ∈ N → r • n ∈ p)
  (le : p ≤ s • N) :
  s • N = p :=
le_antisymm (set_smul_submodule_le s N p closed_under_smul) le

lemma set_smul_submodule_inductionOn {prop : M → Prop} (x : M)
  (hx : x ∈ s • N)
  (smul₀ : ∀ ⦃r : R⦄ ⦃n : M⦄, r ∈ s → n ∈ N → prop (r • n))
  (smul₁ : ∀ (r : R) ⦃m : M⦄, prop m → prop (r • m))
  (add : ∀ ⦃m₁ m₂ : M⦄, prop m₁ → prop m₂ → prop (m₁ + m₂))
  (zero : prop 0) :
  prop x :=
set_smul_submodule_le s N {
  carrier := {m : M | prop m}
  add_mem' := λ {x y} ↦ @add x y
  zero_mem' := zero
  smul_mem' := smul₁
} smul₀ hx

lemma set_smul_submodule_eq [SMulCommClass R R N] :
    s • N =
    Submodule.map
      (N.subtype.comp (Finsupp.lsum R λ (r : R) ↦ ⟨⟨(r • .), smul_add r⟩, λ (r' : R) (m : N) ↦ by dsimp; rw [smul_comm]⟩))
      (Finsupp.supported N R s) := by
  classical
  apply set_smul_submodule_eq_of_le
  · intro r n hr hn
    exact ⟨Finsupp.single r ⟨n, hn⟩, Finsupp.single_mem_supported _ _ hr, by simp⟩

  · intro x hx
    obtain ⟨c, hc, rfl⟩ := hx
    simp only [LinearMap.coe_comp, coeSubtype, Finsupp.coe_lsum, Finsupp.sum, LinearMap.coe_mk,
      AddHom.coe_mk, Function.comp_apply, AddSubmonoid.coe_finset_sum, coe_toAddSubmonoid,
      SetLike.val_smul]
    refine Submodule.sum_mem (p := s • N) (t := c.support) ?_ _ ⟨s • N, ?_⟩
    · rintro r hr
      rw [mem_set_smul_submodule_def, Submodule.mem_sInf]
      rintro p hp
      exact hp (hc hr) (c r).2
    · ext x : 1
      simp only [Set.mem_iInter, SetLike.mem_coe]
      fconstructor
      · refine λ h ↦ h λ r n hr hn ↦ ?_
        rw [mem_set_smul_submodule_def, mem_sInf]
        exact λ p hp ↦ hp hr hn
      · exact λ h _ ↦ h

lemma mem_set_smul_submodule (x : M) [SMulCommClass R R N] :
    x ∈ s • N ↔ ∃ (c : R →₀ N), (c.support : Set R) ⊆ s ∧ x = c.sum λ r m ↦ r • m := by
  fconstructor
  · intros h
    rw [set_smul_submodule_eq] at h
    obtain ⟨c, hc, rfl⟩ := h
    exact ⟨c, hc, rfl⟩

  · rw [mem_set_smul_submodule_def, Submodule.mem_sInf]
    rintro ⟨c, hc1, rfl⟩ p hp
    simp only [Finsupp.sum, AddSubmonoid.coe_finset_sum, coe_toAddSubmonoid, SetLike.val_smul]
    exact Submodule.sum_mem _ λ r hr ↦ hp (hc1 hr) (c _).2

@[simp] lemma mem_empty_smul_submodule (x : M) : x ∈ (∅ : Set R) • N ↔ x = 0 := by
  fconstructor
  · intro hx
    rw [mem_set_smul_submodule_def, Submodule.mem_sInf] at hx
    exact hx ⊥ (λ r _ hr ↦ hr.elim)
  · rintro rfl; exact Submodule.zero_mem _

lemma singleton_set_smul_submodule_eq [SMulCommClass R R M] (r : R) :
    ({r} : Set R) • N = (r • N : Submodule R M) := by
  apply set_smul_submodule_eq_of_le
  · rintro r m rfl hm; exact ⟨m, hm, rfl⟩
  · rintro _ ⟨m, hm, rfl⟩
    rw [mem_set_smul_submodule_def, Submodule.mem_sInf]
    intro p hp; exact hp rfl hm

lemma mem_singleton_set_smul_submodule [SMulCommClass R R M] (r : R) (x : M) :
    x ∈ ({r} : Set R) • N ↔ ∃ (m : M), m ∈ N ∧ x = r • m := by
  rw [singleton_set_smul_submodule_eq]
  change x ∈ (r • N : Set M) ↔ _
  rw [coe_pointwise_smul]
  fconstructor <;>
  · rintro ⟨m, hm, rfl⟩; exact ⟨m, hm, rfl⟩

end

end Submodule
