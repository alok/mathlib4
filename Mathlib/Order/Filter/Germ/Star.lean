/-
Copyright (c) 2024 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.Ultrafilter.Hyperfilter
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Monoid.Basic
import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs

/-!
# The Hyper Operation for Nonstandard Extensions

This file defines the hyper operation that maps standard objects to their nonstandard
(hyper)extensions via ultraproducts.

## Main definitions

* `Hyper ι α` - The nonstandard extension of `α` over index type `ι`, defined as
  `Filter.Germ (hyperfilter ι) α`
* `Hyper.std` - The standard embedding `α → Hyper ι α`
* `Hyper.lift` - Lifts a function `α → β` to `Hyper ι α → Hyper ι β`
* `Hyper.lift₂` - Lifts a binary function
* `Hyper.liftPred` - Lifts a predicate `α → Prop` to `Hyper ι α → Prop`
* `Hyper.liftRel` - Lifts a relation `α → β → Prop`

## The Transfer Principle

The transfer principle states that first-order properties transfer between standard
and nonstandard worlds. This is implemented via:

* `Hyper.liftPred_std` : `liftPred P (std a) ↔ P a`
* `Hyper.liftRel_std` : `liftRel R (std a) (std b) ↔ R a b`
* `Hyper.forall_std_iff` : `(∀ a, P a) ↔ (∀ x, liftPred P x)`

## References

* Robinson, A. "Non-standard Analysis"
* Nelson, E. "Internal Set Theory: A New Approach to Nonstandard Analysis"
-/

open Filter

variable {ι κ : Type*} [Infinite ι] {α β γ : Type*}

/-! ## The Hyper Type -/

/-- The nonstandard extension of `α` over index type `ι`.
This is the ultraproduct `∏_U α` where `U` is the hyperfilter on `ι`. -/
def Hyper (ι : Type*) [Infinite ι] (α : Type*) : Type _ :=
  Germ (hyperfilter ι : Filter ι) α

namespace Hyper

/-! ## Standard Embedding -/

/-- The standard embedding of `α` into its nonstandard extension.
Maps `a : α` to the constant germ `[n ↦ a]`. -/
noncomputable def std (a : α) : Hyper ι α := Germ.const a

/-- Coercion from α to its nonstandard extension. -/
noncomputable instance : Coe α (Hyper ι α) where
  coe := std

theorem std_def (a : α) : (std a : Hyper ι α) = Germ.const a := rfl

theorem std_injective : Function.Injective (std : α → Hyper ι α) :=
  fun _ _ h => Germ.const_inj.mp h

@[simp]
theorem std_inj {a b : α} : (std a : Hyper ι α) = std b ↔ a = b := Germ.const_inj

/-! ## Sequence Representation -/

/-- Construct a nonstandard element from a sequence. -/
noncomputable def ofSeq (f : ι → α) : Hyper ι α := Germ.ofFun f

/-- Every nonstandard element can be represented by a sequence.
This is the surjectivity of the quotient map. -/
theorem ofSeq_surjective : Function.Surjective (ofSeq : (ι → α) → Hyper ι α) :=
  Quot.exists_rep

/-- Alias for the representation theorem. -/
theorem exists_seq_rep (x : Hyper ι α) : ∃ f : ι → α, ofSeq f = x :=
  ofSeq_surjective x

/-- Two sequences give the same nonstandard element iff they agree almost everywhere. -/
theorem ofSeq_eq_ofSeq {f g : ι → α} :
    (ofSeq f : Hyper ι α) = ofSeq g ↔ ∀ᶠ n in hyperfilter ι, f n = g n :=
  Germ.coe_eq

/-- `std a` is the constant sequence `fun _ => a`. -/
theorem std_eq_ofSeq_const (a : α) : (std a : Hyper ι α) = ofSeq (fun _ => a) := rfl

/-! ## Lifting Functions -/

/-- Lift a unary function to the nonstandard extension.
`lift f` applies `f` pointwise to representatives. -/
noncomputable def lift (f : α → β) : Hyper ι α → Hyper ι β := Germ.map f

@[simp]
theorem lift_std (f : α → β) (a : α) : lift f (std a : Hyper ι α) = std (f a) := by
  simp [lift, std, Germ.map_const]

theorem lift_ofSeq (f : α → β) (s : ι → α) : lift f (ofSeq s : Hyper ι α) = ofSeq (f ∘ s) :=
  Germ.map_coe f s

/-- `lift` respects function composition. -/
@[simp]
theorem lift_comp (f : β → γ) (g : α → β) :
    lift f ∘ lift g = (lift (f ∘ g) : Hyper ι α → Hyper ι γ) := by
  ext x
  obtain ⟨s, rfl⟩ := ofSeq_surjective x
  simp only [Function.comp_apply, lift_ofSeq]
  rfl

/-- `lift` on identity is identity. -/
@[simp]
theorem lift_id : lift id = (id : Hyper ι α → Hyper ι α) := Germ.map_id

/-- Lift a binary function to the nonstandard extension. -/
noncomputable def lift₂ (f : α → β → γ) : Hyper ι α → Hyper ι β → Hyper ι γ := Germ.map₂ f

@[simp]
theorem lift₂_std (f : α → β → γ) (a : α) (b : β) :
    lift₂ f (std a : Hyper ι α) (std b) = std (f a b) := by
  simp [lift₂, std, Germ.map₂_const]

theorem lift₂_ofSeq (f : α → β → γ) (s : ι → α) (t : ι → β) :
    lift₂ f (ofSeq s : Hyper ι α) (ofSeq t) = ofSeq (fun n => f (s n) (t n)) :=
  Germ.map₂_coe f s t

/-! ## Lifting Predicates and Relations -/

/-- Lift a predicate to the nonstandard extension.
`liftPred P x` holds if `P` holds for almost all representatives of `x`. -/
def liftPred (P : α → Prop) : Hyper ι α → Prop := Germ.LiftPred P

/-- The key transfer property: a standard predicate on a standard element
equals the original predicate. -/
@[simp]
theorem liftPred_std (P : α → Prop) (a : α) : liftPred P (std a : Hyper ι α) ↔ P a :=
  Germ.liftPred_const_iff

theorem liftPred_ofSeq (P : α → Prop) (f : ι → α) :
    liftPred P (ofSeq f : Hyper ι α) ↔ ∀ᶠ n in hyperfilter ι, P (f n) :=
  Germ.liftPred_coe

/-- Lift a binary relation to the nonstandard extension. -/
def liftRel (R : α → β → Prop) : Hyper ι α → Hyper ι β → Prop := Germ.LiftRel R

/-- Transfer for relations: on standard elements, the lifted relation equals the original. -/
@[simp]
theorem liftRel_std (R : α → β → Prop) (a : α) (b : β) :
    liftRel R (std a : Hyper ι α) (std b) ↔ R a b :=
  Germ.liftRel_const_iff

theorem liftRel_ofSeq (R : α → β → Prop) (f : ι → α) (g : ι → β) :
    liftRel R (ofSeq f : Hyper ι α) (ofSeq g) ↔ ∀ᶠ n in hyperfilter ι, R (f n) (g n) :=
  Germ.liftRel_coe

/-! ## Transfer Principle -/

/-- **Transfer Principle for Universal Quantification**:
A predicate holds for all standard elements iff the lifted predicate holds for all
nonstandard elements. -/
theorem forall_std_iff (P : α → Prop) : (∀ a : α, P a) ↔ (∀ x : Hyper ι α, liftPred P x) := by
  constructor
  · intro h x
    obtain ⟨f, rfl⟩ := ofSeq_surjective x
    rw [liftPred_ofSeq]
    exact Eventually.of_forall (fun n => h (f n))
  · intro h a
    simpa using h (std a)

/-- **Transfer Principle for Existential Quantification** (forward direction):
If a standard element satisfies `P`, then some nonstandard element satisfies `liftPred P`. -/
theorem exists_star_of_exists (P : α → Prop) (h : ∃ a : α, P a) :
    ∃ x : Hyper ι α, liftPred P x := by
  obtain ⟨a, ha⟩ := h
  exact ⟨std a, by simp [ha]⟩

/-! ## Logical Connectives Transfer -/

section LogicalConnectives

variable {P Q : α → Prop}

/-- Conjunction transfers through `liftPred`. -/
theorem liftPred_and (x : Hyper ι α) :
    liftPred (fun a => P a ∧ Q a) x ↔ liftPred P x ∧ liftPred Q x := by
  obtain ⟨f, rfl⟩ := ofSeq_surjective x
  simp only [liftPred_ofSeq]
  exact eventually_and

/-- Disjunction transfers through `liftPred` (using ultrafilter property). -/
theorem liftPred_or (x : Hyper ι α) :
    liftPred (fun a => P a ∨ Q a) x ↔ liftPred P x ∨ liftPred Q x := by
  obtain ⟨f, rfl⟩ := ofSeq_surjective x
  simp only [liftPred_ofSeq]
  exact Ultrafilter.eventually_or

/-- Negation transfers through `liftPred` (using ultrafilter property). -/
theorem liftPred_not (x : Hyper ι α) :
    liftPred (fun a => ¬P a) x ↔ ¬liftPred P x := by
  obtain ⟨f, rfl⟩ := ofSeq_surjective x
  simp only [liftPred_ofSeq]
  exact Ultrafilter.eventually_not

/-- Implication transfers through `liftPred`. -/
theorem liftPred_imp (x : Hyper ι α) :
    liftPred (fun a => P a → Q a) x ↔ (liftPred P x → liftPred Q x) := by
  rw [show (fun a => P a → Q a) = (fun a => ¬P a ∨ Q a) by ext; tauto]
  rw [liftPred_or, liftPred_not]
  tauto

/-- Existential quantification transfers through `liftPred` to `liftRel`. -/
theorem liftPred_exists_iff {Q : α → β → Prop} {x : Hyper ι α} :
    liftPred (fun a => ∃ b, Q a b) x ↔ ∃ y : Hyper ι β, liftRel Q x y := by
  classical
  obtain ⟨f, rfl⟩ := ofSeq_surjective x
  simp only [liftPred_ofSeq]
  constructor
  · intro h
    have : Nonempty β := by
      obtain ⟨n, hn⟩ := Filter.nonempty_of_mem h
      obtain ⟨b, _⟩ := hn
      exact ⟨b⟩
    let g (n : ι) : β := if h : ∃ b, Q (f n) b then Classical.choose h else Classical.choice ‹_›
    use ofSeq g
    rw [liftRel_ofSeq]
    filter_upwards [h] with n hn
    have h_ex : ∃ b, Q (f n) b := hn
    simp only [g]
    rw [dif_pos h_ex]
    exact Classical.choose_spec h_ex
  · rintro ⟨y, hy⟩
    obtain ⟨g, rfl⟩ := ofSeq_surjective y
    rw [liftRel_ofSeq] at hy
    filter_upwards [hy] with n hn
    exact ⟨g n, hn⟩

end LogicalConnectives

/-! ## Algebraic Operations -/

section Algebra

noncomputable instance [Zero α] : Zero (Hyper ι α) := ⟨std 0⟩
noncomputable instance [One α] : One (Hyper ι α) := ⟨std 1⟩
noncomputable instance [Add α] : Add (Hyper ι α) := ⟨lift₂ (· + ·)⟩
noncomputable instance [Mul α] : Mul (Hyper ι α) := ⟨lift₂ (· * ·)⟩
noncomputable instance [Neg α] : Neg (Hyper ι α) := ⟨lift (- ·)⟩
noncomputable instance [Sub α] : Sub (Hyper ι α) := ⟨lift₂ (· - ·)⟩
noncomputable instance [Inv α] : Inv (Hyper ι α) := ⟨lift (·⁻¹)⟩
noncomputable instance [Div α] : Div (Hyper ι α) := ⟨lift₂ (· / ·)⟩

@[simp] theorem std_zero [Zero α] : (std 0 : Hyper ι α) = 0 := rfl
@[simp] theorem std_one [One α] : (std 1 : Hyper ι α) = 1 := rfl

@[simp]
theorem std_add [Add α] (a b : α) : (std (a + b) : Hyper ι α) = std a + std b := by
  simp [HAdd.hAdd, Add.add, lift₂_std]

@[simp]
theorem std_mul [Mul α] (a b : α) : (std (a * b) : Hyper ι α) = std a * std b := by
  simp [HMul.hMul, Mul.mul, lift₂_std]

@[simp]
theorem std_neg [Neg α] (a : α) : (std (-a) : Hyper ι α) = -std a := by
  simp [Neg.neg, lift_std]

@[simp]
theorem std_sub [Sub α] (a b : α) : (std (a - b) : Hyper ι α) = std a - std b := by
  simp [HSub.hSub, Sub.sub, lift₂_std]

@[simp]
theorem std_inv [Inv α] (a : α) : (std a⁻¹ : Hyper ι α) = (std a)⁻¹ := by
  simp [Inv.inv, lift_std]

@[simp]
theorem std_div [Div α] (a b : α) : (std (a / b) : Hyper ι α) = std a / std b := by
  simp [HDiv.hDiv, Div.div, lift₂_std]

end Algebra

/-! ## Order Operations -/

section Order

open Filter

noncomputable instance [LE α] : LE (Hyper ι α) := Filter.Germ.instLE
noncomputable instance instLTHyper [LT α] : LT (Hyper ι α) := ⟨liftRel (· < ·)⟩

noncomputable instance instPreorderHyper [Preorder α] : Preorder (Hyper ι α) :=
  { Filter.Germ.instLE, instLTHyper with
    le_refl := fun x => Germ.inductionOn x fun _ => Eventually.of_forall fun _ => le_refl _
    le_trans := fun x y z =>
      Germ.inductionOn₃ x y z fun _ _ _ h1 h2 => h2.mp (h1.mono fun _ => le_trans)
    lt_iff_le_not_ge := fun x y => by
      induction x using Germ.inductionOn with | h f =>
      induction y using Germ.inductionOn with | h g =>
      change (∀ᶠ i in hyperfilter ι, f i < g i) ↔
        (∀ᶠ i in hyperfilter ι, f i ≤ g i) ∧ ¬(∀ᶠ i in hyperfilter ι, g i ≤ f i)
      simp only [lt_iff_le_not_ge]
      rw [Filter.eventually_and]
      apply and_congr_right
      intro _
      rw [Ultrafilter.eventually_not] }

noncomputable instance [AddCommMonoid α] : AddCommMonoid (Hyper ι α) :=
  Filter.Germ.instAddCommMonoid

noncomputable instance [AddCommGroup α] : AddCommGroup (Hyper ι α) :=
  Filter.Germ.instAddCommGroup

noncomputable instance instPartialOrderHyper [PartialOrder α] : PartialOrder (Hyper ι α) :=
  { instPreorderHyper with
    le_antisymm := fun x y => Germ.inductionOn₂ x y fun _ _ h1 h2 =>
      Germ.coe_eq.2 <| (h1.and h2).mono fun _ h => le_antisymm h.1 h.2 }

noncomputable instance [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] :
    IsOrderedAddMonoid (Hyper ι α) :=
  { inferInstanceAs (AddCommMonoid (Hyper ι α)),
    (instPartialOrderHyper : PartialOrder (Hyper ι α)) with
    add_le_add_left := fun x y h z =>
      Germ.inductionOn₃ x y z (fun f g k H => by
        rw [Germ.coe_le] at H
        exact Germ.coe_le.2 (H.mono fun i hi => add_le_add_left hi (k i))) h }

@[simp]
theorem std_le [LE α] (a b : α) : (std a : Hyper ι α) ≤ std b ↔ a ≤ b := liftRel_std _ _ _

@[simp]
theorem std_lt [LT α] (a b : α) : (std a : Hyper ι α) < std b ↔ a < b := liftRel_std _ _ _

theorem ofSeq_le_ofSeq [LE α] (f g : ι → α) :
    (ofSeq f : Hyper ι α) ≤ ofSeq g ↔ ∀ᶠ i in hyperfilter ι, f i ≤ g i :=
  Germ.coe_le

theorem ofSeq_lt_ofSeq [LT α] (f g : ι → α) :
    (ofSeq f : Hyper ι α) < ofSeq g ↔ ∀ᶠ i in hyperfilter ι, f i < g i :=
  Germ.liftRel_coe

/-- The `<` relation on `Hyper` is defined as `liftRel`. -/
theorem lt_def [LT α] (x y : Hyper ι α) : x < y ↔ liftRel (· < ·) x y := Iff.rfl

theorem liftRel_const_coe {R : α → α → Prop} {c : α} {f : ι → α} :
    liftRel R (std c) (ofSeq f) ↔ ∀ᶠ i in hyperfilter ι, R c (f i) :=
  Iff.rfl

/-- `std a < ofSeq f` iff `a < f n` for almost all `n`. -/
theorem std_lt_ofSeq [LT α] (x : α) (f : ι → α) :
    (std x : Hyper ι α) < ofSeq f ↔ ∀ᶠ i in hyperfilter ι, x < f i := by
  rw [lt_def]
  exact liftRel_const_coe

end Order

/-! ## Internal Set Theory (IST) Axioms

Edward Nelson's Internal Set Theory provides three axiom schemas:
- **Transfer (T)**: First-order properties transfer between standard and nonstandard worlds
- **Idealization (I)**: Saturation principle relating finite/standard quantification
- **Standardization (S)**: Every internal set has a standard subset

In our ultraproduct setting, we can prove versions of these principles.
The key application is overflow/underflow for sequences.
-/

section IST

/-! ### The Standard Predicate -/

/-- An element of `Hyper ι α` is standard if it is the image of some `a : α`. -/
def IsStandard (x : Hyper ι α) : Prop := ∃ a, x = std a

theorem IsStandard.of_std (a : α) : IsStandard (std a : Hyper ι α) := ⟨a, rfl⟩

theorem IsStandard.inv [Inv α] {x : Hyper ι α} (hx : IsStandard x) : IsStandard (x⁻¹) := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨a⁻¹, std_inv a⟩

theorem IsStandard.div [Div α] {x y : Hyper ι α} (hx : IsStandard x) (hy : IsStandard y) :
    IsStandard (x / y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a / b, std_div a b⟩

/-! ### Transfer Principle (T)

The transfer principle states that first-order properties transfer between standard
and nonstandard worlds. We already have `forall_std_iff` as the main transfer theorem.
Here we add more variants. -/

/-- **Transfer (T)**: Existential transfer (full version). -/
theorem exists_std_iff (P : α → Prop) :
    (∃ a : α, P a) ↔ (∃ x : Hyper ι α, IsStandard x ∧ liftPred P x) := by
  constructor
  · intro ⟨a, ha⟩
    exact ⟨std a, IsStandard.of_std a, by simp [ha]⟩
  · intro ⟨x, hstd, hP⟩
    obtain ⟨a, rfl⟩ := hstd
    exact ⟨a, by simpa using hP⟩

/-! ### Finiteness and Infinitesimals -/

/-- An element of `Hyper ι α` is finite if it is bounded by standard elements. -/
def IsFinite [Preorder α] (x : Hyper ι α) : Prop :=
  ∃ a b : α, std a ≤ x ∧ x ≤ std b

/-- An element of `Hyper ι α` is infinite if it is not finite. -/
def IsInfinite [Preorder α] (x : Hyper ι α) : Prop := ¬ IsFinite x

/-- An element is positive infinite if it is greater than all standard elements. -/
def IsInfinitePos [Preorder α] (x : Hyper ι α) : Prop := ∀ a : α, std a < x

/-- An element is negative infinite if it is smaller than all standard elements. -/
def IsInfiniteNeg [Preorder α] (x : Hyper ι α) : Prop := ∀ a : α, x < std a

theorem IsStandard.isFinite [Preorder α] {x : Hyper ι α} (h : IsStandard x) : IsFinite x := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨a, a, le_refl _, le_refl _⟩

theorem IsFinite.add [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] {x y : Hyper ι α}
    (hx : IsFinite x) (hy : IsFinite y) : IsFinite (x + y) := by
  obtain ⟨a1, b1, ha1, hb1⟩ := hx
  obtain ⟨a2, b2, ha2, hb2⟩ := hy
  refine ⟨a1 + a2, b1 + b2, ?_, ?_⟩
  · exact add_le_add ha1 ha2
  · exact add_le_add hb1 hb2

theorem IsFinite.neg [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] {x : Hyper ι α}
    (hx : IsFinite x) : IsFinite (-x) := by
  obtain ⟨a, b, ha, hb⟩ := hx
  refine ⟨-b, -a, ?_, ?_⟩
  · exact neg_le_neg hb
  · exact neg_le_neg ha

theorem IsFinite.sub [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] {x y : Hyper ι α}
    (hx : IsFinite x) (hy : IsFinite y) : IsFinite (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

theorem IsInfinitePos.isInfinite [Preorder α] {x : Hyper ι α} (h : IsInfinitePos x) :
    IsInfinite x := by
  intro hfin
  obtain ⟨_, b, _, hb⟩ := hfin
  have : std b < std b := lt_of_lt_of_le (h b) hb
  exact lt_irrefl _ this

/-- Transfer for binary relations. -/
theorem forall_forall_std_iff (R : α → β → Prop) :
    (∀ a : α, ∀ b : β, R a b) ↔ (∀ x : Hyper ι α, ∀ y : Hyper ι β, liftRel R x y) := by
  constructor
  · intro h x y
    obtain ⟨f, rfl⟩ := ofSeq_surjective x
    obtain ⟨g, rfl⟩ := ofSeq_surjective y
    rw [liftRel_ofSeq]
    exact Eventually.of_forall (fun n => h (f n) (g n))
  · intro h a b
    simpa using h (std a) (std b)

/-! ### Idealization Principle (I) - Overflow and Underflow

The Idealization axiom in IST states: For any internal formula φ,
  (∀ finite F, ∃ y, ∀ x ∈ F, φ(x,y)) ↔ (∃ y, ∀ˢᵗ x, φ(x,y))

In our ultraproduct setting, this manifests as overflow and underflow principles. -/

/-- **Overflow Principle**: If a property holds for all standard naturals,
there exists a nonstandard element for which it also holds.
This is a key consequence of the ultrafilter being nonprincipal. -/
theorem overflow {P : ℕ → Prop} (hP : ∀ n : ℕ, P n) :
    ∀ x : Hyper ℕ ℕ, liftPred P x := by
  rw [← forall_std_iff]
  exact hP

/-- **Existence of Infinite Elements**: There exist nonstandard elements
greater than all standard elements. -/
theorem exists_infinite_nat : ∃ ω : Hyper ℕ ℕ, ∀ n : ℕ, std n < ω := by
  use ofSeq id
  intro n
  rw [std_lt_ofSeq]
  apply Filter.mem_hyperfilter_of_finite_compl
  simp only [Set.compl_setOf, not_lt]
  exact Set.finite_le_nat n

/-- An infinite hypernatural - the equivalence class of the identity sequence. -/
noncomputable def omega : Hyper ℕ ℕ := ofSeq id

theorem omega_gt_std (n : ℕ) : std n < omega := by
  rw [omega, std_lt_ofSeq]
  apply Filter.mem_hyperfilter_of_finite_compl
  simp only [Set.compl_setOf, not_lt]
  exact Set.finite_le_nat n

/-- **Underflow Principle** (for predicates on sequences):
If P holds for an infinite element, it holds for arbitrarily large standard elements.
This is the contrapositive of: if P fails for all large enough n, it fails for infinite elements. -/
theorem underflow {P : ℕ → Prop} {ω : Hyper ℕ ℕ} (hω : ∀ n : ℕ, std n < ω)
    (hP : liftPred P ω) : ∀ n : ℕ, ∃ m : ℕ, m ≥ n ∧ P m := by
  intro n
  -- ω is represented by some sequence f
  obtain ⟨f, rfl⟩ := ofSeq_surjective ω
  -- P holds almost everywhere for f
  rw [liftPred_ofSeq] at hP
  -- f(k) > n for almost all k (since ω > std n)
  have hgt : ∀ᶠ k in hyperfilter ℕ, n < f k := by
    specialize hω n
    rw [std_lt_ofSeq] at hω
    exact hω
  -- Both conditions hold eventually
  have := hP.and hgt
  obtain ⟨k, hPk, hgk⟩ := this.exists
  exact ⟨f k, Nat.le_of_lt hgk, hPk⟩

/-! ### Standardization Principle (S)

The full Standardization axiom requires set-theoretic machinery.
Here we provide a version for predicates on standard elements. -/

/-- **Standardization for Predicates**: The standard part of a predicate on `Hyper ι α`
restricted to standard elements can be pulled back to `α`. -/
theorem standardization (P : Hyper ι α → Prop) :
    ∃ Q : α → Prop, ∀ a : α, Q a ↔ P (std a) :=
  ⟨fun a => P (std a), fun _ => Iff.rfl⟩

/-- Standard part extraction for predicates. -/
def standardPart (P : Hyper ι α → Prop) : α → Prop := fun a => P (std a)

@[simp]
theorem standardPart_apply (P : Hyper ι α → Prop) (a : α) :
    standardPart P a = P (std a) := rfl

theorem standardPart_liftPred (P : α → Prop) :
    standardPart (liftPred P : Hyper ι α → Prop) = P := by
  ext a
  simp [standardPart, liftPred_std]

/-! ### Generic Idealization (for any Infinite index type)

The following principles work for any infinite index type `ι`, not just `ℕ`. -/

/-- Generic overflow: if P holds for all standard elements, it holds for all hyper-elements. -/
theorem overflow_generic {P : α → Prop} (hP : ∀ a : α, P a) :
    ∀ x : Hyper ι α, liftPred P x := by
  rw [← forall_std_iff]
  exact hP

/-- There exist nonstandard elements in `Hyper ι ι` greater than all standard elements.
This is the generic version showing `Hyper ι ι` has "infinite" elements.
Requires `LocallyFiniteOrderBot` to ensure `Set.Iic a` is finite. -/
theorem exists_infinite [LinearOrder ι] [LocallyFiniteOrderBot ι] :
    ∃ ω : Hyper ι ι, ∀ a : ι, std a < ω := by
  use ofSeq id
  intro a
  rw [std_lt_ofSeq]
  apply Filter.mem_hyperfilter_of_finite_compl
  simp only [Set.compl_setOf, not_lt]
  exact Set.finite_Iic a

/-- The generic omega element for any linearly ordered infinite index type. -/
noncomputable def omega' [LinearOrder ι] : Hyper ι ι := ofSeq id

theorem omega'_gt_std [LinearOrder ι] [LocallyFiniteOrderBot ι] (a : ι) :
    std a < (omega' : Hyper ι ι) := by
  rw [omega', std_lt_ofSeq]
  apply Filter.mem_hyperfilter_of_finite_compl
  simp only [Set.compl_setOf, not_lt]
  exact Set.finite_Iic a

/-! ### Consequences of IST for Analysis

These lemmas show how IST principles apply to analysis on `Hyper ι α`. -/

/-- If a property holds "eventually" in the hyperfilter sense, it is consistent
with the standard world. -/
theorem liftPred_of_eventually {P : α → Prop} (f : ι → α) (h : ∀ᶠ n in hyperfilter ι, P (f n)) :
    liftPred P (ofSeq f : Hyper ι α) := by
  rw [liftPred_ofSeq]
  exact h

/-- The contrapositive of overflow: if not all hyper-elements satisfy P,
then some standard element fails P. -/
theorem not_forall_liftPred_iff {P : α → Prop} :
    ¬(∀ x : Hyper ι α, liftPred P x) ↔ ∃ a : α, ¬P a := by
  rw [← forall_std_iff]
  push_neg
  rfl

end IST

/-! ## Nonstandard Characterizations

These definitions and lemmas provide the key nonstandard analysis concepts. -/

section NonstandardAnalysis

/-- `omega` is positive infinite. -/
theorem omega_isInfinitePos : IsInfinitePos (omega : Hyper ℕ ℕ) := omega_gt_std

/-- Standard elements are finite. -/
theorem IsFinite.std [Preorder α] (a : α) : IsFinite (std a : Hyper ι α) :=
  (IsStandard.of_std a).isFinite

end NonstandardAnalysis

/-! ## Countable Saturation

For `Hyper ℕ α` (ultraproducts indexed by `ℕ`), we have countable saturation:
if every finite subfamily of a countable family of internal predicates has a common witness,
then the entire family has a common witness.

This is proved via diagonalization: we construct a sequence that eventually satisfies
each predicate by taking diagonal elements from witnesses for finite prefixes.
-/

section Saturation

/-- **Countable Saturation** for `Hyper ℕ α`:
If every finite subset of predicates `{P 0, P 1, ..., P k}` has a common witness in `Hyper ℕ α`,
then the entire countable family `{P n : n ∈ ℕ}` has a common witness.

This is a key property that unlocks "backward" directions in NSA theorems,
allowing us to go from "monad membership for all elements" back to standard topological
properties. -/
theorem countable_saturation {α : Type*} {P : ℕ → α → Prop}
    (hfin : ∀ F : Finset ℕ, ∃ x : Hyper ℕ α, ∀ n ∈ F, liftPred (P n) x) :
    ∃ x : Hyper ℕ α, ∀ n : ℕ, liftPred (P n) x := by
  -- For each finite prefix [0..k], choose a witness and a representing sequence
  have hwit : ∀ k : ℕ, ∃ f : ℕ → α, ∀ n ≤ k, ∀ᶠ i in hyperfilter ℕ, P n (f i) := by
    intro k
    obtain ⟨x, hx⟩ := hfin (Finset.range (k + 1))
    obtain ⟨f, rfl⟩ := ofSeq_surjective x
    use f
    intro n hn
    have hn' : n ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hn)
    exact (liftPred_ofSeq (P n) f).mp (hx n hn')
  choose f hf using hwit
  -- For each k, the set {i : ∀ n ≤ k, P n (f k i)} is in the hyperfilter
  -- Since hyperfilter ⊇ cofinite on ℕ, this set is infinite; pick M_k ≥ k from it
  have hgood : ∀ k : ℕ, ∃ M : ℕ, M ≥ k ∧ ∀ n ≤ k, P n (f k M) := by
    intro k
    -- The intersection of finitely many hyperfilter sets is in the hyperfilter
    -- Use Finset.range (k + 1) = {0, 1, ..., k}
    have hall : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), ∀ n ∈ Finset.range (k + 1), P n (f k i) := by
      rw [Finset.eventually_all]
      intro n hn
      rw [Finset.mem_range] at hn
      exact hf k n (Nat.lt_succ_iff.mp hn)
    -- Also {i : i ≥ k} is in hyperfilter (cofinite ⊆ hyperfilter)
    have hge : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), i ≥ k := by
      apply Filter.mem_of_superset (Filter.mem_hyperfilter_of_finite_compl _)
      · intro i hi; exact hi
      · convert Set.finite_lt_nat k using 1
        ext i
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
    -- Convert hall to the ≤ form
    have hall' : ∀ᶠ i in (hyperfilter ℕ : Filter ℕ), ∀ n ≤ k, P n (f k i) := by
      apply hall.mono
      intro i hi n hn
      exact hi n (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
    -- The conjunction is in the hyperfilter, hence nonempty
    have hboth := hall'.and hge
    exact hboth.exists.imp fun M ⟨h1, h2⟩ => ⟨h2, h1⟩
  choose M hM using hgood
  -- Define diagonal sequence: g(k) = f_k(M_k)
  let g : ℕ → α := fun k => f k (M k)
  use ofSeq g
  -- Show that for any n, eventually P n (g k) holds
  intro n
  rw [liftPred_ofSeq]
  -- For k ≥ n: g(k) = f_k(M_k), and since k ≥ n, the witness f_k works for P n
  apply Filter.mem_hyperfilter_of_finite_compl
  -- {k : ¬ P n (g k)} ⊆ {0, 1, ..., n-1}
  have hsub : {k : ℕ | ¬P n (g k)} ⊆ {k : ℕ | k < n} := by
    intro k hk
    simp only [Set.mem_setOf_eq] at hk ⊢
    by_contra hge
    simp only [not_lt] at hge
    -- k ≥ n, so f_k satisfies P n at M_k (since M_k is a "good" index for f_k)
    have hPn : P n (f k (M k)) := (hM k).2 n hge
    exact hk hPn
  exact Set.Finite.subset (Set.finite_lt_nat n) hsub

/-- Variant of countable saturation with `Finset.range` -/
theorem countable_saturation' {α : Type*} [Nonempty α] {P : ℕ → α → Prop}
    (hfin : ∀ k : ℕ, ∃ x : Hyper ℕ α, ∀ n < k, liftPred (P n) x) :
    ∃ x : Hyper ℕ α, ∀ n : ℕ, liftPred (P n) x := by
  apply countable_saturation
  intro F
  by_cases hF : F.Nonempty
  · obtain ⟨x, hx⟩ := hfin (F.sup id + 1)
    use x
    intro n hn
    apply hx
    calc n ≤ F.sup id := Finset.le_sup (f := id) hn
      _ < F.sup id + 1 := Nat.lt_succ_self _
  · -- F is empty, any witness works
    simp only [Finset.not_nonempty_iff_eq_empty] at hF
    subst hF
    use std (Classical.ofNonempty)
    simp

/-- **κ-Saturation** for `Hyper ι α`:

The ultraproduct `Hyper ι α` is `(#ι)⁺`-saturated. This means: for any type `κ` with
`#κ ≤ #ι`, if every finite subset of predicates indexed by `κ` has a common witness,
then the entire family has a common witness.

This generalizes `countable_saturation` from `ℕ` to arbitrary small index types.
The condition `#κ ≤ #ι` ensures we can embed `κ` into `ι` for the diagonal argument.

**Mathematical Note**: Classically, an ultraproduct over index set `I` is `|I|⁺`-saturated,
meaning it satisfies the saturation property for families of size `< |I|⁺ = (|I|).succ`.
The condition `#κ ≤ #ι` is equivalent to `#κ < (#ι)⁺`. -/
theorem cardinal_saturation (e : κ ↪ ι) {α : Type*} {P : κ → α → Prop}
    (hfin : ∀ F : Finset κ, ∃ x : Hyper ι α, ∀ k ∈ F, liftPred (P k) x) :
    ∃ x : Hyper ι α, ∀ k : κ, liftPred (P k) x := by
  -- Use the regularity of the hyperfilter
  let E := hyperfilterBijection ι
  -- For each i, we find an element satisfying the required predicates
  have h_exists : ∀ i, ∃ a : α, ∀ k, e k ∈ E i → P k a := by
    intro i
    let K_i : Finset κ := (E i).preimage e e.injective.injOn
    obtain ⟨x, hx⟩ := hfin K_i
    obtain ⟨u, rfl⟩ := Hyper.ofSeq_surjective x
    let Y := {j | ∀ k ∈ K_i, P k (u j)}
    have hY : Y ∈ hyperfilter ι := by
      change ∀ᶠ j in hyperfilter ι, ∀ k ∈ K_i, P k (u j)
      rw [Finset.eventually_all]
      intro k hk
      have hk' : k ∈ K_i := Finset.mem_coe.mp hk
      specialize hx k hk'
      rw [Hyper.liftPred_ofSeq] at hx
      exact hx
    obtain ⟨j, hj⟩ := Filter.nonempty_of_mem hY
    use u j
    intro k hke
    have hk : k ∈ K_i := Finset.mem_preimage.mpr hke
    exact hj k hk

  choose f hf using h_exists

  use Hyper.ofSeq f
  intro k
  rw [Hyper.liftPred_ofSeq]
  let W_k := {i | e k ∈ E i}
  have hW : W_k ∈ hyperfilter ι := by
    have : W_k = {i | i ∈ {j | e k ∈ E j}} := rfl
    rw [this]
    have : hyperfilter ι ≤ hyperfilterRegularizer ι :=
      le_trans (Ultrafilter.of_le _) inf_le_left
    apply this
    apply Filter.mem_generate_of_mem
    use e k
    rfl
  apply Filter.mem_of_superset hW
  intro i hi
  exact hf i k hi

end Saturation

/-! ## NSA Notation

We introduce intuitive notation for nonstandard analysis that hides the ultrafilter machinery.
All notation is scoped to `NonstandardAnalysis`.

* `★a` - standard embedding of `a` into the hyperextension (`std a`)
* `f ★` - lift of function `f` to hyperextension (`lift f`)
* `x ⦦★ P` - `x` satisfies the lifted predicate `P` (`liftPred P x`)
* `x ∈★ S` - `x` is in the star of set `S` (`liftPred (· ∈ S) x`)

The symbol `★` (U+2605 BLACK STAR) is chosen to avoid conflict with the Hodge star `⋆` (U+22C6).
-/
section Notation

set_option quotPrecheck false in
/-- Standard embedding: `★a` means `std a` -/
scoped[NonstandardAnalysis] prefix:max "★" => Hyper.std

set_option quotPrecheck false in
/-- Function lifting: `f★` means `lift f` -/
scoped[NonstandardAnalysis] notation:max f "★" => Hyper.lift f

set_option quotPrecheck false in
/-- Predicate satisfaction: `x ⦦★ P` means `liftPred P x` -/
scoped[NonstandardAnalysis] notation:50 x " ⦦★ " P:51 => Hyper.liftPred P x

set_option quotPrecheck false in
/-- Set membership in star: `x ∈★ S` means `liftPred (· ∈ S) x` -/
scoped[NonstandardAnalysis] notation:50 x " ∈★ " S:51 => Hyper.liftPred (· ∈ S) x

set_option quotPrecheck false in
/-- Sequence construction: `⟦f⟧` means `ofSeq f` -/
scoped[NonstandardAnalysis] notation:max "⟦" f "⟧" => Hyper.ofSeq f

end Notation

end Hyper
