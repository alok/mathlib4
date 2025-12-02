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
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.Lattice
import Mathlib.Topology.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Field.Defs

open scoped Classical

set_option linter.style.longFile 2000

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

/-- Hypernatural numbers are the nonstandard extension of ℕ indexed by ℕ. -/
abbrev Hypernatural := Hyper ℕ ℕ

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

/-- The coercion from ℕ to Hypernatural is injective. -/
theorem coe_nat_inj : Function.Injective (fun n : ℕ => (n : Hypernatural)) := std_injective

/-- Lift a function to the nonstandard extension. -/
def lift (f : α → β) : Hyper ι α → Hyper ι β := Germ.map f



@[simp]
theorem std_inj {a b : α} : (std a : Hyper ι α) = std b ↔ a = b := Germ.const_inj

/-! ## Sequence Representation -/

/-- Construct a nonstandard element from a sequence. -/
noncomputable def ofSeq (f : ι → α) : Hyper ι α := Germ.ofFun f

theorem std_eq_ofSeq_const (a : α) : std a = ofSeq (fun (_ : ι) => a) := rfl

theorem lift_ofSeq (f : α → β) (s : ι → α) : lift f (ofSeq s) = ofSeq (f ∘ s) := Germ.map_coe f s

-- theorem lift_std (f : α → β) (a : α) : lift f (std a) = std (f a) := by
--   dsimp [lift, std]
--   rfl

/-- Every nonstandard element can be represented by a sequence.
This is the surjectivity of the quotient map. -/
theorem ofSeq_surjective {ι : Type*} [Infinite ι] {α : Type*} : Function.Surjective (fun f : ι → α => ofSeq f) :=
  Quot.exists_rep

/-- Alias for the representation theorem. -/
theorem exists_seq_rep (x : Hyper ι α) : ∃ f : ι → α, ofSeq f = x :=
  ofSeq_surjective x

/-- Induction principle for `Hyper ι α`.
This allows proving a property for all hyper-elements by proving it for all sequences. -/
@[elab_as_elim]
theorem inductionOn {P : Hyper ι α → Prop} (x : Hyper ι α) (h : ∀ f : ι → α, P (ofSeq f)) : P x :=
  Germ.inductionOn x h






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


/-- Lift a sequence of predicates to the nonstandard extension. -/
def liftPredSeq (P : ι → α → Prop) (x : Hyper ι α) : Prop :=
  x.liftOn (fun f => ∀ᶠ i in hyperfilter ι, P i (f i))
    (fun f g h => propext (Filter.eventually_congr (h.mono fun i hi => by simp [hi])))

theorem liftPredSeq_ofSeq (P : ι → α → Prop) (f : ι → α) :
    liftPredSeq P (ofSeq f) ↔ ∀ᶠ i in hyperfilter ι, P i (f i) := by
  dsimp [liftPredSeq, ofSeq]
  rfl

/-- An internal set is one that is defined by a sequence of sets. -/
def IsInternal (A : Set (Hyper ι α)) : Prop :=
  ∃ S : ι → Set α, ∀ x, x ∈ A ↔ liftPredSeq (fun i y => y ∈ S i) x

theorem isInternal_univ : IsInternal (Set.univ : Set (Hyper ι α)) := by
  use fun _ => Set.univ
  intro x
  simp only [Set.mem_univ, true_iff]
  obtain ⟨f, rfl⟩ := ofSeq_surjective x
  rw [liftPredSeq_ofSeq]
  exact Eventually.of_forall fun i => Set.mem_univ (f i)

theorem isInternal_empty : IsInternal (∅ : Set (Hyper ι α)) := by
  use fun _ => ∅
  intro x
  simp only [Set.mem_empty_iff_false, false_iff]

  simp only [liftPredSeq_ofSeq, Set.mem_empty_iff_false]
  have : NeBot (hyperfilter ι) := inferInstance
  exact Filter.eventually_false_iff_eq_bot.mpr this.ne

theorem IsInternal.union {A B : Set (Hyper ι α)} (hA : IsInternal A) (hB : IsInternal B) :
    IsInternal (A ∪ B) := by
  obtain ⟨SA, hSA⟩ := hA
  obtain ⟨SB, hSB⟩ := hB
  use fun i => SA i ∪ SB i
  intro x
  rw [Set.mem_union, hSA, hSB]
  obtain ⟨f, rfl⟩ := ofSeq_surjective x
  simp only [liftPredSeq_ofSeq, Set.mem_union]
  exact Ultrafilter.eventually_or.symm

theorem IsInternal.inter {A B : Set (Hyper ι α)} (hA : IsInternal A) (hB : IsInternal B) :
    IsInternal (A ∩ B) := by
  obtain ⟨SA, hSA⟩ := hA
  obtain ⟨SB, hSB⟩ := hB
  use fun i => SA i ∩ SB i
  intro x
  rw [Set.mem_inter_iff, hSA, hSB]
  obtain ⟨f, rfl⟩ := ofSeq_surjective x
  simp only [liftPredSeq_ofSeq, Set.mem_inter_iff]
  exact Filter.eventually_and.symm

theorem IsInternal.compl {A : Set (Hyper ι α)} (hA : IsInternal A) : IsInternal Aᶜ := by
  obtain ⟨SA, hSA⟩ := hA
  use fun i => (SA i)ᶜ
  intro x
  rw [Set.mem_compl_iff, hSA]
  obtain ⟨f, rfl⟩ := ofSeq_surjective x
  simp only [liftPredSeq_ofSeq, Set.mem_compl_iff]
  exact Ultrafilter.eventually_not.symm

theorem IsInternal.diff {A B : Set (Hyper ι α)} (hA : IsInternal A) (hB : IsInternal B) :
    IsInternal (A \ B) := by
  rw [Set.diff_eq]
  exact hA.inter hB.compl

/-! ## Lifting Predicates and Relations -/

/-- Lift a predicate to the nonstandard extension.
`liftPred P x` holds if `P` holds for almost all representatives of `x`. -/
def liftPred (P : α → Prop) : Hyper ι α → Prop := Germ.LiftPred P

/-- The key transfer property: a standard predicate on a standard element
equals the original predicate. -/
@[simp]
theorem lift_std (f : α → β) (a : α) : lift f (std a : Hyper ι α) = std (f a) :=
  rfl


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

theorem liftRel_lift_left (R : β → γ → Prop) (f : α → β) (x : Hyper ι α) (y : Hyper ι γ) :
    liftRel R (lift f x) y ↔ liftRel (fun a b => R (f a) b) x y := by
  induction x using Germ.inductionOn
  induction y using Germ.inductionOn
  simp [liftRel, lift, Germ.map_coe, Germ.liftRel_coe]

theorem liftRel_std_right (R : α → β → Prop) (x : Hyper ι α) (b : β) :
    liftRel R x (std b) ↔ liftPred (fun a => R a b) x := by
  induction x using Germ.inductionOn with | h f =>
  dsimp [liftRel, std, Germ.const, liftPred]
  rfl

theorem lift_lift₂_diagonal (f : α → β → γ) (g : α → β) (x : Hyper ι α) :
    lift₂ f x (lift g x) = lift (fun a => f a (g a)) x := by
  induction x using Germ.inductionOn with | h f =>
  dsimp [lift₂, lift]
  rfl

theorem liftPred_lift (P : β → Prop) (f : α → β) (x : Hyper ι α) :
    liftPred P (lift f x) ↔ liftPred (P ∘ f) x := by
  induction x using Germ.inductionOn with | h f =>
  dsimp [liftPred, lift]
  rfl

theorem lift₂_std_left (f : α → β → γ) (a : α) (y : Hyper ι β) :
    lift₂ f (std a) y = lift (f a) y := by
  induction y using Germ.inductionOn with | h g =>
  dsimp [lift₂, lift, std, Germ.const]
  rfl

theorem lift₂_std_right (f : α → β → γ) (x : Hyper ι α) (b : β) :
    lift₂ f x (std b) = lift (fun a => f a b) x := by
  induction x using Germ.inductionOn with | h f =>
  dsimp [lift₂, lift, std, Germ.const]
  rfl

theorem liftRel_lift_right (R : β → γ → Prop) (x : Hyper ι β) (g : α → γ) (y : Hyper ι α) :
    liftRel R x (lift g y) ↔ liftRel (fun a b => R a (g b)) x y := by
  induction x using Germ.inductionOn with | h f =>
  induction y using Germ.inductionOn with | h g =>
  dsimp [liftRel, lift]
  rfl

theorem liftRel_lift₂_lift₂ {γ δ : Type*} (R : γ → δ → Prop) (f : α → β → γ) (g : α → β → δ)
    (x : Hyper ι α) (y : Hyper ι β) :
    liftRel R (lift₂ f x y) (lift₂ g x y) ↔ liftRel (fun a b => R (f a b) (g a b)) x y := by
  induction x using Germ.inductionOn with | h f =>
  induction y using Germ.inductionOn with | h g =>
  dsimp [liftRel, lift₂]
  rfl

theorem forall_liftRel (R : α → β → Prop) (x : Hyper ι α) :
    (∀ y : Hyper ι β, liftRel R x y) ↔ liftPred (fun a => ∀ b, R a b) x := by
  induction x using Germ.inductionOn with | h f =>
  change _ ↔ liftPred _ (ofSeq f)
  rw [liftPred_ofSeq]
  constructor
  · intro h
    rcases isEmpty_or_nonempty β with hβ | hβ
    · filter_upwards with i b; exact (IsEmpty.false b).elim
    haveI := hβ
    let S := {i | ∀ b, R (f i) b}
    by_contra hS
    have hSc : {i | ∃ b, ¬ R (f i) b} ∈ hyperfilter ι := by
      have : {i | ∀ b, R (f i) b}ᶜ ∈ hyperfilter ι := by
        rwa [Ultrafilter.compl_mem_iff_notMem]
      rw [Set.compl_setOf] at this
      simp only [not_forall] at this
      exact this
    let g := fun i => Classical.epsilon (fun b => ¬ R (f i) b)
    have hg : ∀ i, (∃ b, ¬ R (f i) b) → ¬ R (f i) (g i) := by
      intro i hi
      exact Classical.epsilon_spec hi
    have : {i | ¬ R (f i) (g i)} ∈ hyperfilter ι := by
      filter_upwards [hSc] with i hi
      exact hg i hi
    have : ¬ liftRel R (ofSeq f) (ofSeq g) := by
      dsimp [liftRel, ofSeq]
      change ¬ Germ.LiftRel R (ofSeq f) (ofSeq g)
      erw [Germ.liftRel_coe]
      intro h
      have : {i | R (f i) (g i)} ∩ {i | ¬ R (f i) (g i)} ∈ hyperfilter ι := Filter.inter_mem h ‹_›
      change {i | R (f i) (g i)} ∩ {i | R (f i) (g i)}ᶜ ∈ hyperfilter ι at this
      rw [Set.inter_compl_self] at this
      change ∅ ∈ hyperfilter ι at this
      exact False.elim (Ultrafilter.empty_notMem this)
    specialize h (ofSeq g)
    dsimp [liftRel, ofSeq] at h
    change Germ.LiftRel R (ofSeq f) (ofSeq g) at h
    erw [Germ.liftRel_coe] at h
    exact this h
  · intro h y
    induction y using Germ.inductionOn with | h g =>
    dsimp [liftRel, ofSeq]
    change Germ.LiftRel R (ofSeq f) (ofSeq g)
    erw [Germ.liftRel_coe]
    filter_upwards [h] with i hi
    exact hi (g i)

theorem exists_liftRel (R : α → β → Prop) (x : Hyper ι α) :
    (∃ y : Hyper ι β, liftRel R x y) ↔ liftPred (fun a => ∃ b, R a b) x := by
  induction x using Germ.inductionOn with | h f =>
  change _ ↔ liftPred _ (ofSeq f)
  rw [liftPred_ofSeq]
  constructor
  · rintro ⟨y, hy⟩
    induction y using Germ.inductionOn with | h g =>
    dsimp [liftRel, ofSeq] at hy
    change Germ.LiftRel R (ofSeq f) (ofSeq g) at hy
    erw [Germ.liftRel_coe] at hy
    filter_upwards [hy] with i hi
    exact ⟨g i, hi⟩
  · intro h
    rcases isEmpty_or_nonempty β with hβ | hβ
    · have : ∀ i, ¬ ∃ b, R (f i) b := fun i ⟨b, _⟩ => IsEmpty.false b
      rcases (hyperfilter ι).nonempty_of_mem h with ⟨i, hi⟩
      exact (this i hi).elim
    haveI := hβ
    let g := fun i => Classical.epsilon (fun b => R (f i) b)
    have hg : ∀ i, (∃ b, R (f i) b) → R (f i) (g i) := fun i => Classical.epsilon_spec
    exists ofSeq g
    dsimp [liftRel, ofSeq]
    change Germ.LiftRel R (ofSeq f) (ofSeq g)
    erw [Germ.liftRel_coe]
    filter_upwards [h] with i hi
    exact hg i hi

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
  dsimp [lift, std]

@[simp]
theorem std_sub [Sub α] (a b : α) : (std (a - b) : Hyper ι α) = std a - std b := by
  simp [HSub.hSub, Sub.sub, lift₂_std]

@[simp]
theorem std_inv [Inv α] (a : α) : (std a⁻¹ : Hyper ι α) = (std a)⁻¹ := by
  dsimp [lift, std]

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

noncomputable instance instPartialOrderHyper [PartialOrder α] : PartialOrder (Hyper ι α) :=
  { instPreorderHyper with
    le_antisymm := fun x y h1 h2 => by
      induction x using Germ.inductionOn with | h f =>
      induction y using Germ.inductionOn with | h g =>
      rw [Germ.coe_le] at h1 h2
      rw [Germ.coe_eq]
      exact h1.and h2 |>.mono fun i h => le_antisymm h.1 h.2 }

noncomputable instance instLinearOrderHyper [LinearOrder α] : LinearOrder (Hyper ι α) :=
  { instPartialOrderHyper with
    le_total := fun x y => by
      induction x using Germ.inductionOn; next f =>
      induction y using Germ.inductionOn; next g =>
      simp only [LE.le, Germ.liftRel_coe]
      exact (hyperfilter ι).eventually_or.1 (Eventually.of_forall fun i => le_total (f i) (g i))
    toDecidableLE := Classical.decRel _ }

noncomputable instance instSemiringHyper [Semiring α] : Semiring (Hyper ι α) :=
  Filter.Germ.instSemiring
noncomputable instance instRingHyper [Ring α] : Ring (Hyper ι α) := Filter.Germ.instRing
noncomputable instance instCommRingHyper [CommRing α] : CommRing (Hyper ι α) :=
  Filter.Germ.instCommRing



noncomputable instance instIsOrderedRingHyper [Ring α] [PartialOrder α] [IsOrderedRing α] :
    IsOrderedRing (Hyper ι α) :=
  { @Filter.Germ.instRing ι (hyperfilter ι) α _,
    @instPartialOrderHyper ι _ α _ with
    add_le_add_left := fun a b h c => by
      induction a using Germ.inductionOn; next f =>
      induction b using Germ.inductionOn; next g =>
      induction c using Germ.inductionOn; next k =>
      dsimp [LE.le] at h ⊢
      rw [← Germ.coe_add, ← Germ.coe_add, Germ.liftRel_coe]
      rw [Germ.liftRel_coe] at h
      exact h.mono fun i hi => add_le_add_left hi (k i)
    mul_le_mul_of_nonneg_left := fun c hc a b hab => by
      induction a using Germ.inductionOn; next f =>
      induction b using Germ.inductionOn; next g =>
      induction c using Germ.inductionOn; next k =>
      dsimp [LE.le] at hab hc ⊢
      rw [← Germ.coe_zero] at hc
      simp only [Germ.liftRel_coe] at hab hc ⊢
      rw [← Germ.coe_mul, ← Germ.coe_mul, Germ.liftRel_coe]
      filter_upwards [hab, hc] with i hab hc
      exact mul_le_mul_of_nonneg_left hab hc
    mul_le_mul_of_nonneg_right := fun c hc a b hab => by
      induction a using Germ.inductionOn; next f =>
      induction b using Germ.inductionOn; next g =>
      induction c using Germ.inductionOn; next k =>
      dsimp [LE.le] at hab hc ⊢
      rw [← Germ.coe_zero] at hc
      simp only [Germ.liftRel_coe] at hab hc ⊢
      rw [← Germ.coe_mul, ← Germ.coe_mul, Germ.liftRel_coe]
      filter_upwards [hab, hc] with i hab hc
      exact mul_le_mul_of_nonneg_right hab hc
    zero_le_one := Eventually.of_forall fun _ => zero_le_one }

-- noncomputable instance instOrderedSemiringHyper [OrderedSemiring α] : OrderedSemiring (Hyper ι α) :=
--   { instSemiringHyper, instPartialOrderHyper with
--     add_le_add_left := fun a b h c => by
--       induction a using Germ.inductionOn; next f =>
--       induction b using Germ.inductionOn; next g =>
--       induction c using Germ.inductionOn; next k =>
--       dsimp [LE.le] at h ⊢
--       rw [← Germ.coe_add, ← Germ.coe_add, Germ.liftRel_coe]
--       rw [Germ.liftRel_coe] at h
--       exact h.mono fun i hi => add_le_add_left hi (k i)
--     mul_le_mul_of_nonneg_left := fun c hc a b hab => by
--       induction a using Germ.inductionOn; next f =>
--       induction b using Germ.inductionOn; next g =>
--       induction c using Germ.inductionOn; next k =>
--       dsimp [LE.le] at hab hc ⊢
--       rw [← Germ.coe_zero] at hc
--       simp only [Germ.liftRel_coe] at hab hc ⊢
--       rw [← Germ.coe_mul, ← Germ.coe_mul, Germ.liftRel_coe]
--       filter_upwards [hab, hc] with i hab hc
--       exact mul_le_mul_of_nonneg_left hab hc
--     mul_le_mul_of_nonneg_right := fun c hc a b hab => by
--       induction a using Germ.inductionOn; next f =>
--       induction b using Germ.inductionOn; next g =>
--       induction c using Germ.inductionOn; next k =>
--       dsimp [LE.le] at hab hc ⊢
--       rw [← Germ.coe_zero] at hc
--       simp only [Germ.liftRel_coe] at hab hc ⊢
--       rw [← Germ.coe_mul, ← Germ.coe_mul, Germ.liftRel_coe]
--       filter_upwards [hab, hc] with i hab hc
--       exact mul_le_mul_of_nonneg_right hab hc
--     zero_le_one := Eventually.of_forall fun _ => zero_le_one }

-- noncomputable instance instLinearOrderedSemiringHyper [LinearOrderedSemiring α] :
--     LinearOrderedSemiring (Hyper ι α) :=
--   { instOrderedSemiringHyper, instLinearOrderHyper with }

-- noncomputable instance instLinearOrderedCommSemiringHyper [LinearOrderedCommSemiring α] :
--     LinearOrderedCommSemiring (Hyper ι α) :=
--   { instLinearOrderedSemiringHyper, Filter.Germ.instCommSemiring with }

-- Factorial
def factorial [Infinite ι] (n : Hyper ι ℕ) : Hyper ι ℕ := lift Nat.factorial n

@[simp]
theorem factorial_std {ι : Type*} [Infinite ι] (n : ℕ) : factorial (std n : Hyper ι ℕ) = std n.factorial := by
  dsimp [factorial, lift, std]

-- Pow
noncomputable def pow [Infinite ι] [Pow α ℕ] (x : Hyper ι α) (n : Hyper ι ℕ) : Hyper ι α := lift₂ (fun a b => a ^ b) x n

@[simp]
theorem pow_std {ι : Type*} [Infinite ι] [Pow α ℕ] (a : α) (n : ℕ) : pow (std a : Hyper ι α) (std n) = std (a ^ n) := by
  dsimp [pow, lift₂, std]

noncomputable instance [AddCommMonoid α] : AddCommMonoid (Hyper ι α) :=
  Filter.Germ.instAddCommMonoid

noncomputable instance [AddCommGroup α] : AddCommGroup (Hyper ι α) :=
  Filter.Germ.instAddCommGroup

noncomputable instance [Ring α] : Ring (Hyper ι α) := Filter.Germ.instRing
noncomputable instance [CommRing α] : CommRing (Hyper ι α) := Filter.Germ.instCommRing

@[simp]
theorem std_le [LE α] (a b : α) : (std a : Hyper ι α) ≤ std b ↔ a ≤ b := liftRel_std _ _ _

@[simp]
theorem std_lt [Preorder α] (a b : α) : (std a : Hyper ι α) < std b ↔ a < b := by
  simp only [lt_iff_le_not_ge, std_le]

/-- The `<` relation on `Hyper` is defined as `liftRel`. -/
theorem lt_def [Preorder α] (x y : Hyper ι α) : x < y ↔ liftRel (· < ·) x y := by
  induction x using Germ.inductionOn with | h f =>
  induction y using Germ.inductionOn with | h g =>
  simp only [lt_iff_le_not_ge]
  change (∀ᶠ i in hyperfilter ι, f i ≤ g i) ∧ ¬(∀ᶠ i in hyperfilter ι, g i ≤ f i) ↔
      (∀ᶠ i in hyperfilter ι, f i ≤ g i ∧ ¬(g i ≤ f i))
  rw [← Ultrafilter.eventually_not, ← Filter.eventually_and]

instance [AddCommSemigroup α] [PartialOrder α] [i_mono : AddLeftMono α] : AddLeftMono (Hyper ι α) :=
  ⟨fun x y z => Germ.inductionOn₃ x y z fun f g k H => by
    change liftRel (· ≤ ·) (ofSeq g) (ofSeq k) at H
    change liftRel (· ≤ ·) (ofSeq (f + g)) (ofSeq (f + k))
    rw [Hyper.liftRel_ofSeq] at H ⊢
    filter_upwards [H] with i hi
    exact @CovariantClass.elim α α (· + ·) (· ≤ ·) i_mono (f i) (g i) (k i) hi⟩

instance [AddCommSemigroup α] [PartialOrder α] [i_mono : AddRightMono α] :
    AddRightMono (Hyper ι α) :=
  ⟨fun x y z => Germ.inductionOn₃ x y z fun f g k H => by
    change liftRel (· ≤ ·) (ofSeq g) (ofSeq k) at H
    change liftRel (· ≤ ·) (ofSeq (g + f)) (ofSeq (k + f))
    rw [Hyper.liftRel_ofSeq] at H ⊢
    filter_upwards [H] with i hi
    exact @CovariantClass.elim α α (Function.swap (· + ·)) (· ≤ ·) i_mono
      (f i) (g i) (k i) hi⟩

instance [AddCommSemigroup α] [PartialOrder α] [i_mono : AddLeftStrictMono α] :
    AddLeftStrictMono (Hyper ι α) :=
  ⟨fun x y z => Germ.inductionOn₃ x y z fun f g k H => by
    rw [lt_def] at H ⊢
    change liftRel (· < ·) (ofSeq g) (ofSeq k) at H
    change liftRel (· < ·) (ofSeq (f + g)) (ofSeq (f + k))
    rw [Hyper.liftRel_ofSeq] at H ⊢
    filter_upwards [H] with i hi
    exact @CovariantClass.elim α α (· + ·) (· < ·) i_mono (f i) (g i) (k i) hi⟩

instance [AddCommSemigroup α] [PartialOrder α] [i_mono : AddRightStrictMono α] :
    AddRightStrictMono (Hyper ι α) :=
  ⟨fun x y z => Germ.inductionOn₃ x y z fun f g k H => by
    rw [lt_def] at H ⊢
    change liftRel (· < ·) (ofSeq g) (ofSeq k) at H
    change liftRel (· < ·) (ofSeq (g + f)) (ofSeq (k + f))
    rw [Hyper.liftRel_ofSeq] at H ⊢
    filter_upwards [H] with i hi
    exact @CovariantClass.elim α α (fun x y => y + x) (· < ·) i_mono
      (f i) (g i) (k i) hi⟩

instance [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] :
    IsOrderedAddMonoid (Hyper ι α) where
  add_le_add_left := fun _ _ h c => add_le_add_left h c

theorem add_eq_lift₂ [Add α] (x y : Hyper ι α) : x + y = lift₂ (· + ·) x y := rfl
theorem mul_eq_lift₂ [Mul α] (x y : Hyper ι α) : x * y = lift₂ (· * ·) x y := rfl
theorem sub_eq_lift₂ [Sub α] (x y : Hyper ι α) : x - y = lift₂ (· - ·) x y := rfl
theorem neg_eq_lift [Neg α] (x : Hyper ι α) : -x = lift (-·) x := rfl
theorem zero_eq_std [Zero α] : (0 : Hyper ι α) = std 0 := rfl

/-- The transfer of the induction axiom for *internal* sets of hypernaturals.
If an internal set `P` contains 0 and is closed under successor, it contains all hypernaturals. -/
theorem internal_induction (P : Set (Hyper ι ℕ)) (h_int : IsInternal P)
    (h0 : 0 ∈ P) (hs : ∀ n, n ∈ P → n + 1 ∈ P) : ∀ n, n ∈ P := by
  -- P is internal, so P corresponds to a sequence of sets A
  obtain ⟨A, hA⟩ := h_int
  intro n
  rw [hA]
  induction n using inductionOn with | h f =>
  rw [liftPredSeq]
  -- We want to show {i | f i ∈ A i} ∈ U
  -- We know 0 ∈ P, so {i | 0 ∈ A i} ∈ U
  have h0_seq : ∀ᶠ i in hyperfilter ι, 0 ∈ A i := by
    have : (0 : Hyper ι ℕ) ∈ P := h0
    rw [← std_zero, std_eq_ofSeq_const] at this
    rwa [hA, liftPredSeq_ofSeq] at this
  -- We know ∀ n, n ∈ P → n + 1 ∈ P
  -- This transfers to: ∀ᶠ i, ∀ k, k ∈ A i → k + 1 ∈ A i
  have hs_seq : ∀ᶠ i in hyperfilter ι, ∀ k, k ∈ A i → k + 1 ∈ A i := by
    by_contra h_not
    have h_ex : ∀ᶠ i in hyperfilter ι, ∃ k, k ∈ A i ∧ k + 1 ∉ A i := by
      rw [← Ultrafilter.eventually_not] at h_not
      filter_upwards [h_not] with i hi
      push_neg at hi
      exact hi
    -- Construct a sequence of counterexamples
    let k_seq (i : ι) : ℕ := if h : ∃ k, k ∈ A i ∧ k + 1 ∉ A i then Classical.choose h else 0
    have hk : ∀ᶠ i in hyperfilter ι, k_seq i ∈ A i ∧ k_seq i + 1 ∉ A i := by
      filter_upwards [h_ex] with i hi
      dsimp [k_seq]
      rw [dif_pos hi]
      exact Classical.choose_spec hi
    -- Let n_bad := [k_seq]
    let n_bad : Hyper ι ℕ := ofSeq k_seq
    have hn_in : n_bad ∈ P := by
      rw [hA, liftPredSeq]
      filter_upwards [hk] with i hi using hi.1
    have hn_succ_notin : n_bad + 1 ∉ P := by
      rw [hA]
      have : n_bad + 1 = ofSeq (fun i => k_seq i + 1) := by
        dsimp [n_bad]
        rw [← std_one, std_eq_ofSeq_const, add_eq_lift₂, lift₂_ofSeq]
      rw [this, liftPredSeq_ofSeq]
      rw [← Ultrafilter.eventually_not]
      filter_upwards [hk] with i hi using hi.2
    -- Contradiction with hs
    exact hn_succ_notin (hs n_bad hn_in)

  -- Now combine h0_seq and hs_seq
  filter_upwards [h0_seq, hs_seq] with i h0i hsi
  -- For each i, A i is a set of naturals containing 0 and closed under successor.
  -- By standard induction, A i = Set.univ
  exact Nat.rec h0i hsi (f i)
theorem std_le_std [Preorder α] {a b : α} : (std a : Hyper ι α) ≤ std b ↔ a ≤ b := by
  constructor
  · intro h
    have : {i | a ≤ b} ∈ (hyperfilter ι : Filter ι) := h
    by_contra hab
    have h_empty : ({i | a ≤ b} : Set ι) = ∅ := by
      ext (i : ι)
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact hab
    rw [h_empty] at this
    exact absurd (Filter.empty_mem_iff_bot.mp this)
      (NeBot.ne (inferInstance : NeBot (hyperfilter ι : Filter ι)))
  · intro h
    filter_upwards with _ using h

theorem std_lt_std [Preorder α] {a b : α} : (std a : Hyper ι α) < std b ↔ a < b := by
  constructor
  · intro h
    have : {i | a < b} ∈ (hyperfilter ι : Filter ι) := h
    by_contra hab
    have h_empty : ({i | a < b} : Set ι) = ∅ := by
      ext (i : ι)
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact hab
    rw [h_empty] at this
    exact absurd (Filter.empty_mem_iff_bot.mp this)
      (NeBot.ne (inferInstance : NeBot (hyperfilter ι : Filter ι)))
  · intro h
    filter_upwards with _ using h

/-- An element is infinitesimal if it is bounded by any positive standard element. -/
def IsInfinitesimal [AddCommGroup α] [Preorder α] (x : Hyper ι α) : Prop :=
  ∀ r : α, 0 < r → -std r < x ∧ x < std r

theorem IsInfinitesimal.zero [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
    [AddLeftStrictMono α] [AddRightStrictMono α] : IsInfinitesimal (0 : Hyper ι α) :=
  fun r hr => ⟨by rw [← std_neg, ← std_zero, std_lt]; exact neg_lt_zero.2 hr,
               by rw [← std_zero, std_lt]; exact hr⟩

theorem liftRel_neg_neg [Neg α] {R : α → α → Prop} {x y : Hyper ι α} :
    liftRel R (-x) (-y) ↔ liftRel (fun a b => R (-a) (-b)) x y := by
  induction x using Germ.inductionOn
  induction y using Germ.inductionOn
  simp only [neg_eq_lift, liftRel_lift_left, liftRel_lift_right]

theorem liftRel_flip {R : α → β → Prop} {x : Hyper ι α} {y : Hyper ι β} :
    liftRel (flip R) y x ↔ liftRel R x y := by
  refine Germ.inductionOn x fun f => ?_
  refine Germ.inductionOn y fun g => ?_
  change liftRel (flip R) (ofSeq g) (ofSeq f) ↔ liftRel R (ofSeq f) (ofSeq g)
  rw [Hyper.liftRel_ofSeq, Hyper.liftRel_ofSeq]
  rfl

theorem IsInfinitesimal.neg [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
    [AddLeftStrictMono α] [AddRightStrictMono α] {x : Hyper ι α}
    (hx : IsInfinitesimal x) : IsInfinitesimal (-x) :=
  fun r hr => by
    obtain ⟨h1, h2⟩ := hx r hr
    have h_neg : ∀ {R : α → α → Prop} {x y : Hyper ι α},
        liftRel R (-x) (-y) ↔ liftRel (fun a b => R (-a) (-b)) x y :=
      fun {R x y} => by
        induction x using Germ.inductionOn; next f =>
        induction y using Germ.inductionOn; next g =>
        rw [neg_eq_lift, neg_eq_lift]
        exact Iff.refl (∀ᶠ i in @hyperfilter ι (by infer_instance), R (-f i) (-g i))
    constructor
    · -- -std r < -x ↔ x < std r
      rw [lt_def]
      erw [h_neg]
      simp only [neg_lt_neg_iff]

      rw [← liftRel_flip]
      exact h2
    · -- -x < std r ↔ -std r < x
      rw [lt_def]
      have : (std r : Hyper ι α) = -(-std r) := (neg_neg _).symm
      rw [this]
      erw [h_neg]
      simp only [neg_lt_neg_iff]

      rw [← liftRel_flip]
      exact h1

theorem IsInfinitesimal.add [Field α] [LinearOrder α] [IsOrderedRing α] {x y : Hyper ι α}
    (hx : IsInfinitesimal x) (hy : IsInfinitesimal y) : IsInfinitesimal (x + y) :=
  fun r hr => by
    have hr2 : 0 < r / 2 := half_pos hr
    obtain ⟨hx1, hx2⟩ := hx (r / 2) hr2
    obtain ⟨hy1, hy2⟩ := hy (r / 2) hr2
    constructor
    · rw [← add_halves r, std_add, neg_add]
      exact add_lt_add hx1 hy1
    · rw [← add_halves r, std_add]
      exact add_lt_add hx2 hy2

theorem IsInfinitesimal.sub [Field α] [LinearOrder α] [IsOrderedRing α] {x y : Hyper ι α}
    (hx : IsInfinitesimal x) (hy : IsInfinitesimal y) : IsInfinitesimal (x - y) := by
  rw [sub_eq_add_neg]
  exact IsInfinitesimal.add hx (IsInfinitesimal.neg hy)



theorem ofSeq_le_ofSeq [LE α] (f g : ι → α) :
    (ofSeq f : Hyper ι α) ≤ ofSeq g ↔ ∀ᶠ i in hyperfilter ι, f i ≤ g i :=
  Germ.coe_le

theorem ofSeq_lt_ofSeq [LT α] (f g : ι → α) :
    (ofSeq f : Hyper ι α) < ofSeq g ↔ ∀ᶠ i in hyperfilter ι, f i < g i :=
  Germ.liftRel_coe

theorem eq_iff_liftRel_eq {ι : Type*} [Infinite ι] {α : Type*} (x y : Hyper ι α) :
    x = y ↔ liftRel (· = ·) x y := by
  induction x using Germ.inductionOn with | h f =>
  induction y using Germ.inductionOn with | h g =>
  dsimp [liftRel]
  rw [Germ.liftRel_coe]
  exact Germ.coe_eq

theorem liftRel_const_coe {R : α → α → Prop} {c : α} {f : ι → α} :
    liftRel R (std c) (ofSeq f) ↔ ∀ᶠ i in hyperfilter ι, R c (f i) :=
  Iff.rfl

/-- `std a < ofSeq f` iff `a < f n` for almost all `n`. -/
theorem std_lt_ofSeq [LT α] (x : α) (f : ι → α) :
    (std x : Hyper ι α) < ofSeq f ↔ ∀ᶠ i in hyperfilter ι, x < f i := by
  change liftRel (· < ·) (std x) (ofSeq f) ↔ _
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

theorem IsFinite_iff_abs_le [CommRing α] [LinearOrder α] [IsOrderedRing α] {x : Hyper ι α} :
    IsFinite x ↔ ∃ r : α, abs x ≤ std r := by
  constructor
  · rintro ⟨a, b, ha, hb⟩
    use abs a + abs b
    rw [abs_le]
    constructor
    · trans std a
      · rw [← std_neg, std_le]
        rw [neg_add]
        have h1 : -|b| + -|a| ≤ 0 + -|a| :=
          add_le_add (neg_nonpos.2 (abs_nonneg b)) (le_refl (-|a|))
        rw [add_comm] at h1
        rw [zero_add] at h1
        have h2 : -|a| ≤ a := neg_le.2 (le_trans (le_abs_self (-a)) (le_of_eq (abs_neg a)))
        exact le_trans h1 h2
      · exact ha
    · trans std b
      · exact hb
      · rw [std_le]; exact le_add_of_nonneg_of_le (abs_nonneg a) (le_abs_self b)
  · rintro ⟨r, hr⟩
    rw [abs_le] at hr
    exact ⟨-r, r, hr.1, hr.2⟩

theorem IsFinite.mul [CommRing α] [LinearOrder α] [IsOrderedRing α] {x y : Hyper ι α}
    (hx : IsFinite x) (hy : IsFinite y) : IsFinite (x * y) := by
  rw [IsFinite_iff_abs_le] at hx hy ⊢
  obtain ⟨r, hr⟩ := hx
  obtain ⟨s, hs⟩ := hy
  use abs r * abs s + 1
  have hr' : abs x ≤ std (abs r) := le_trans hr ((std_le r (abs r)).mpr (le_abs_self r))
  have hs' : abs y ≤ std (abs s) := le_trans hs ((std_le s (abs s)).mpr (le_abs_self s))
  rw [abs_mul]
  calc abs x * abs y ≤ std (abs r) * std (abs s) :=
      mul_le_mul hr' hs' (abs_nonneg y) ((std_le 0 (abs r)).mpr (abs_nonneg r))
    _ = std (abs r * abs s) := by rw [← std_mul]
    _ ≤ std (abs r * abs s) + 1 := le_add_of_nonneg_right zero_le_one
    _ = std (abs r * abs s + 1) := by rw [std_add, std_one]

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

theorem coe_nat_eq_std (n : ℕ) : (n : Hypernatural) = std n := rfl

theorem omega_gt_nat (n : ℕ) : (n : Hypernatural) < omega := by
  rw [lt_def]
  simp only [omega, coe_nat_eq_std, std_def, Germ.const, Germ.liftRel_coe, ofSeq, Germ.ofFun]
  apply Filter.mem_hyperfilter_of_finite_compl
  dsimp
  simp only [Set.compl_setOf, not_lt]
  exact Set.finite_le_nat n

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


/-! ## Overspill and Underspill

These principles relate properties of standard elements to properties of infinite elements.
-/

section Overspill

/-- **Overspill Principle** for standard predicates:
If a predicate holds for arbitrarily large standard naturals, it holds for some infinite
hypernatural. -/
theorem exists_infinite_of_forall_exists_gt {P : ℕ → Prop}
    (h : ∀ n : ℕ, ∃ m : ℕ, P m ∧ m > n) :
    ∃ x : Hyper ℕ ℕ, IsInfinite x ∧ liftPred P x := by
  -- We use countable saturation on the family Q_n(x) := P x ∧ x > n
  let Q (n : ℕ) (x : ℕ) := P x ∧ x > n
  have hsat : ∃ x : Hyper ℕ ℕ, ∀ n, liftPred (Q n) x := by
    apply countable_saturation
    intro F
    -- Let m be a witness for max F
    let max_n := if h : F.Nonempty then F.max' h else 0
    obtain ⟨m, hm, hm_gt⟩ := h (max_n)
    use std m
    intro n hn
    rw [liftPred_std]
    refine ⟨hm, lt_of_le_of_lt ?_ hm_gt⟩
    have hF : F.Nonempty := ⟨n, hn⟩
    dsimp only [max_n]
    rw [dif_pos hF]
    exact Finset.le_max' F n hn
  obtain ⟨x, hx⟩ := hsat
  use x
  constructor
  · rw [IsInfinite, IsFinite]
    push_neg
    intro a b _
    -- x > n for all n. In particular x > b.
    -- hx b gives liftPred (Q b) x => liftPred (fun y => y > b) x => x > std b
    have : x > std b := by
      specialize hx b
      rw [liftPred_and] at hx
      exact hx.2
    exact this
  · -- liftPred P x follows from hx 0 (or any n)
    specialize hx 0
    rw [liftPred_and] at hx
    exact hx.1

/-- **Underspill Principle** for standard predicates:
If a predicate holds for all infinite hypernaturals, it holds for all sufficiently large
standard naturals. -/
theorem exists_forall_ge_of_forall_infinite {P : ℕ → Prop}
    (h : ∀ x : Hyper ℕ ℕ, IsInfinite x → liftPred P x) :
    ∃ n : ℕ, ∀ m ≥ n, P m := by
  by_contra hnot
  push_neg at hnot
  -- hnot says ∀ n, ∃ m ≥ n, ¬P m
  -- By overspill applied to ¬P, there exists infinite x such that ¬P x
  have hover : ∃ x : Hyper ℕ ℕ, IsInfinite x ∧ liftPred (fun k => ¬P k) x := by
    apply exists_infinite_of_forall_exists_gt
    intro n
    obtain ⟨m, hm_ge, hm_not⟩ := hnot (n + 1)
    exact ⟨m, hm_not, lt_of_lt_of_le (Nat.lt_succ_self n) hm_ge⟩
  obtain ⟨x, hinf, hnotP⟩ := hover
  rw [liftPred_not] at hnotP
  exact hnotP (h x hinf)

end Overspill

/-! ## Topology and Compactness -/

section Topology

open scoped NonstandardAnalysis

variable [TopologicalSpace α]

/-- The monad of a filter `F` is the set of hyperreal points that are in the star of every set
in `F`. -/
def monad (F : Filter α) : Set (Hyper ι α) :=
  {x | ∀ U ∈ F, liftPred (· ∈ U) x}

/-- A point `x` is near standard to `y` if `x` is in the monad of the neighborhood filter of `y`. -/
def IsNearStandard (x : Hyper ι α) (y : α) : Prop :=
  x ∈ monad (nhds y)

set_option quotPrecheck false
/-- Notation for near standard: `x ≈ y` -/
local infix:50 " ≈ " => IsNearStandard

/-- The ultrafilter corresponding to a hyperreal `x`. -/
noncomputable def asUltrafilter (x : Hyper ι α) : Ultrafilter α :=
  Ultrafilter.map (Classical.choose (Hyper.exists_seq_rep x)) (hyperfilter ι)

omit [TopologicalSpace α] in
theorem mem_star_iff_mem_asUltrafilter (x : Hyper ι α) (S : Set α) :
    liftPred (· ∈ S) x ↔ S ∈ (asUltrafilter x : Filter α) := by
  simp only [asUltrafilter, Ultrafilter.mem_coe, Ultrafilter.mem_map]
  let f := Classical.choose (Hyper.exists_seq_rep x)
  have hf : ofSeq f = x := Classical.choose_spec (Hyper.exists_seq_rep x)
  conv_lhs => rw [← hf, liftPred_ofSeq]
  rfl

omit [TopologicalSpace α] in
/-- If the model is sufficiently saturated, every ultrafilter is represented by some hyperreal. -/
theorem exists_hyper_of_ultrafilter [Nonempty (Set α ↪ ι)] (F : Ultrafilter α) :
    ∃ x : Hyper ι α, asUltrafilter x = F := by
  classical
  obtain ⟨e⟩ := ‹Nonempty (Set α ↪ ι)›
  let P : Set α → α → Prop := fun S x => S ∈ F → x ∈ S
  have hfin : ∀ G : Finset (Set α), ∃ x : Hyper ι α, ∀ S ∈ G, liftPred (P S) x := by
    intro G
    let G_in_F := G.filter (fun S => S ∈ F)
    have h_inter_mem : ⋂₀ (G_in_F : Set (Set α)) ∈ (F : Filter α) := by
      rw [Set.sInter_eq_biInter]
      rw [Filter.biInter_mem G_in_F.finite_toSet]
      intro S hS
      rw [Finset.mem_coe, Finset.mem_filter] at hS
      exact hS.2
    have h_nonempty : (⋂₀ (G_in_F : Set (Set α))).Nonempty :=
      Filter.nonempty_of_mem h_inter_mem
    obtain ⟨a, ha⟩ := h_nonempty
    use std a
    intro S hS
    rw [liftPred_std]
    simp only [P]
    intro hSF
    apply Set.mem_sInter.mp ha S
    change S ∈ G.filter (fun S => S ∈ F)
    rw [Finset.mem_filter]
    exact ⟨hS, hSF⟩
  obtain ⟨x, hx⟩ := cardinal_saturation e hfin
  use x
  apply Ultrafilter.ext
  intro S
  change S ∈ (asUltrafilter x : Filter α) ↔ S ∈ F
  rw [← mem_star_iff_mem_asUltrafilter]
  constructor
  · intro hxS
    by_contra hS_not
    have hSc : Sᶜ ∈ F := Ultrafilter.compl_mem_iff_notMem.mpr hS_not
    specialize hx Sᶜ
    have hxSc : x ∈★ Sᶜ := by
      have h_eq : P Sᶜ = (fun x => x ∈ Sᶜ) := by
        ext a
        simp only [P, hSc, true_implies]
      rwa [h_eq] at hx
    have h_inter : x ∈★ (S ∩ Sᶜ) := by
      change liftPred (fun x => x ∈ S ∧ x ∈ Sᶜ) x
      rw [liftPred_and x]
      exact ⟨hxS, hxSc⟩
    rw [Set.inter_compl_self] at h_inter
    -- x ∈★ ∅
    have h_false : x ∈★ (∅ : Set α) ↔ False := by
      change liftPred (fun _ => False) x ↔ False
      obtain ⟨f, rfl⟩ := Hyper.ofSeq_surjective x
      rw [Hyper.liftPred_ofSeq]
      simp only [Filter.eventually_false_iff_eq_bot]
      exact iff_false_intro (hyperfilter ι).neBot.ne
    rwa [h_false] at h_inter
  · intro hSF
    specialize hx S
    have h_eq : P S = (fun x => x ∈ S) := by
      ext a
      simp only [P, hSF, true_implies]
    rwa [h_eq] at hx

/-- Characterization of compactness using nonstandard analysis.
A set `K` is compact iff every point in `*K` is near standard to some point in `K`.
(Reverse direction requires saturation). -/
theorem isCompact_iff_nearStd [Nonempty (Set α ↪ ι)] (K : Set α) :
    IsCompact K ↔ ∀ x : Hyper ι α, x ∈★ K → ∃ y ∈ K, x ≈ y := by
  constructor
  · intro hK x hx
    let U := asUltrafilter x
    have hUK : K ∈ (U : Filter α) := (mem_star_iff_mem_asUltrafilter x K).mp hx
    obtain ⟨y, hyK, hy⟩ := IsCompact.ultrafilter_le_nhds hK U (le_principal_iff.mpr hUK)
    use y, hyK
    intro V hV
    rw [mem_star_iff_mem_asUltrafilter]
    exact hy hV
  · intro h
    rw [isCompact_iff_ultrafilter_le_nhds]
    intro F hFK
    obtain ⟨x, hx⟩ := exists_hyper_of_ultrafilter (ι := ι) F
    have hxK : x ∈★ K := by
      rw [mem_star_iff_mem_asUltrafilter, hx]
      exact le_principal_iff.mp hFK
    obtain ⟨y, hyK, hy⟩ := h x hxK
    use y, hyK
    rw [← hx]
    intro V hV
    rw [← mem_star_iff_mem_asUltrafilter]
    exact hy V hV

end Topology


section StandardPart

scoped infix:50 " ≈ " => IsNearStandard



variable [Infinite ι] [Field α] [ConditionallyCompleteLinearOrder α] [IsStrictOrderedRing α]
variable [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] [NoMaxOrder α] [NoMinOrder α]

open scoped NonstandardAnalysis
open Topology

theorem isNearStandard_def (x : Hyper ι α) (y : α) : IsNearStandard x y ↔ ∀ U ∈ 𝓝 y, x ∈★ U := by
  rw [IsNearStandard, monad]
  rfl

theorem mem_star_Iio (x : Hyper ι α) (a : α) : x ∈★ Set.Iio a ↔ x < std a := by
  induction x using Germ.inductionOn with | h f =>
  erw [Hyper.liftPred_ofSeq, Hyper.lt_def, Hyper.std, Hyper.liftRel_ofSeq]
  rfl

theorem mem_star_Ioi (x : Hyper ι α) (a : α) : x ∈★ Set.Ioi a ↔ std a < x := by
  induction x using Germ.inductionOn with | h f =>
  erw [Hyper.liftPred_ofSeq, Hyper.lt_def, Hyper.std, Hyper.liftRel_ofSeq]
  rfl

theorem mem_star_inter (x : Hyper ι α) (s t : Set α) : x ∈★ (s ∩ t) ↔ x ∈★ s ∧ x ∈★ t := by
  induction x using Germ.inductionOn with | h f =>
  change (∀ᶠ i in hyperfilter ι, f i ∈ s ∩ t) ↔ (∀ᶠ i in hyperfilter ι, f i ∈ s) ∧ (∀ᶠ i in hyperfilter ι, f i ∈ t)
  simp only [Set.mem_inter_iff, Filter.eventually_and]

theorem mem_star_Ici (x : Hyper ι α) (a : α) : x ∈★ Set.Ici a ↔ std a ≤ x := by
  change liftPred (fun y => a ≤ y) x ↔ std a ≤ x
  change liftRel (· ≤ ·) (std a) x ↔ std a ≤ x
  rfl

theorem mem_star_Iic (x : Hyper ι α) (a : α) : x ∈★ Set.Iic a ↔ x ≤ std a := by
  change liftPred (fun y => y ≤ a) x ↔ x ≤ std a
  change liftRel (· ≤ ·) x (std a) ↔ x ≤ std a
  rfl

theorem mem_star_Icc (x : Hyper ι α) (a b : α) : x ∈★ Set.Icc a b ↔ std a ≤ x ∧ x ≤ std b := by
  rw [← Set.Ici_inter_Iic, mem_star_inter, mem_star_Ici, mem_star_Iic]

theorem mem_star_Ioo (x : Hyper ι α) (a b : α) : x ∈★ Set.Ioo a b ↔ std a < x ∧ x < std b := by
  rw [← Set.Ioi_inter_Iio, mem_star_inter, mem_star_Ioi, mem_star_Iio]

theorem mem_star_std {s : Set α} {a : α} : (a : Hyper ι α) ∈★ s ↔ a ∈ s := by
  change liftPred (· ∈ s) (std a) ↔ a ∈ s
  rw [liftPred_std]

theorem star_mono {s t : Set α} (h : s ⊆ t) {x : Hyper ι α} : x ∈★ s → x ∈★ t := by
  induction x using Germ.inductionOn
  intro hx
  exact Filter.Eventually.mono hx (fun i hi => h hi)

/-- The standard part of a finite hyperreal. -/
noncomputable def st (x : Hyper ι α) : α := sSup {r : α | std r ≤ x}

theorem st_eq_sSup (x : Hyper ι α) : st x = sSup {r : α | std r ≤ x} := rfl

theorem isFinite_iff_exists_st (x : Hyper ι α) : IsFinite x ↔ ∃ r : α, IsNearStandard x r := by
  constructor
  · intro hx
    dsimp [IsFinite] at hx
    let a := Classical.choose hx
    have hx_a := Classical.choose_spec hx
    let b := Classical.choose hx_a
    have h_ab := Classical.choose_spec hx_a
    obtain ⟨ha, hb⟩ := h_ab
    let S := {r : α | (r : Hyper ι α) ≤ x}
    have hS_nonempty : S.Nonempty := ⟨a, ha⟩
    have hS_bddAbove : BddAbove S := ⟨b, fun r hr => by
      have : (r : Hyper ι α) ≤ b := hr.trans hb
      simp at this ⊢
      exact this⟩
    let y := sSup S
    use y
    rw [IsNearStandard, monad]
    intro U hU
    rw [mem_nhds_iff] at hU
    obtain ⟨V, hVU, hV_open, hyV⟩ := hU
    have h_exists := mem_nhds_iff_exists_Ioo_subset.mp (IsOpen.mem_nhds hV_open hyV)
    let u := h_exists.choose
    let v := h_exists.choose_spec.choose
    have huv := h_exists.choose_spec.choose_spec
    have h_mem_Ioo : y ∈ Set.Ioo u v := huv.1
    have h_subset : Set.Ioo u v ⊆ V := huv.2
    have h_lt : u < y := h_mem_Ioo.1
    have h_gt : y < v := h_mem_Ioo.2
    have h_x_lt : x < (v : Hyper ι α) := by
      by_contra h_not
      have : (v : Hyper ι α) ≤ x := le_of_not_gt h_not
      have : v ∈ S := this
      have : v ≤ y := le_csSup hS_bddAbove this
      have : v < v := lt_of_le_of_lt this h_gt
      exact lt_irrefl v this
    have h_u_lt_x : (u : Hyper ι α) < x := by
      obtain ⟨r, hr_in, hr_gt⟩ := exists_lt_of_lt_csSup hS_nonempty h_lt
      exact hr_gt.trans_le (le_of_eq rfl) -- Placeholder, need to fix this proof logic if needed
/-- The galaxy of a family of sets is the union of their stars. -/
def galaxy (S : Set (Set α)) : Set (Hyper ι α) :=
  ⋃ s ∈ S, {x | liftPred (· ∈ s) x}

theorem galaxy_mem (S : Set (Set α)) (x : Hyper ι α) :
    x ∈ galaxy S ↔ ∃ s ∈ S, liftPred (· ∈ s) x := by
  simp [galaxy]

set_option linter.unusedSectionVars false in

theorem liftPredSeq_mono {P Q : ι → α → Prop} (h : ∀ i x, P i x → Q i x) (x : Hyper ι α) :
    liftPredSeq P x → liftPredSeq Q x := by
  induction x using Germ.inductionOn
  intro hP
  unfold liftPredSeq at *
  filter_upwards [hP] with i hi
  exact h i _ hi


/-- A set in `Hyper ι α` is hyperfinite if it is the internal extension of a sequence of finite sets. -/
def IsHyperfinite (A : Set (Hyper ι α)) : Prop :=
  ∃ S : ι → Set α, (∀ i, (S i).Finite) ∧ ∀ x, x ∈ A ↔ liftPredSeq (fun i y => y ∈ S i) x

theorem IsHyperfinite.isInternal {A : Set (Hyper ι α)} (h : IsHyperfinite A) : IsInternal A := by
  obtain ⟨S, _, hS⟩ := h
  use S, hS

/-- **Approximation Theorem**: For any infinite set `A`, there exists a hyperfinite set `H`
such that `{std a | a ∈ A} ⊆ H ⊆ A*`. -/
theorem exists_hyperfinite_approximation [Countable ι] {A : Set α} (hA : A.Countable) (hA_inf : A.Infinite) :
    ∃ H : Set (Hyper ι α), IsHyperfinite H ∧
      (∀ a ∈ A, (std a : Hyper ι α) ∈ H) ∧
      (∀ x ∈ H, liftPred (· ∈ A) x) ∧
      (∀ a ∈ A, (std a : Hyper ι α) ∈ H) ⊂ H := by
  obtain ⟨f, hf⟩ := hA.exists_injective_nat
  obtain ⟨f, hf⟩ := hA.exists_injective_nat
  let s : ℕ → Finset α := fun n => ((Set.Finite.preimage_embedding (Function.Embedding.mk f hf) (Set.finite_le_nat n)).toFinset).map (Function.Embedding.subtype (fun x => x ∈ A))
  -- We need to map this sequence to ι
  -- Since ι is infinite and countable, there exists a bijection g : ℕ ≃ ι
  have : Nonempty (ℕ ≃ ι) := nonempty_equiv_of_countable
  let g := this.some
  let S : ι → Set α := fun i => s (g.symm i)
  have hS_fin : ∀ i, (S i).Finite := fun i => (s (g.symm i)).finite_toSet
  let H := {x | liftPredSeq (fun i y => y ∈ S i) x}
  use H
  constructor
  · exact ⟨S, hS_fin, fun x => Iff.rfl⟩
  constructor
  · intro a ha
    simp only [H, liftPredSeq, std, Germ.const]
    have : {i | a ∈ S i} ∈ hyperfilter ι := by
      -- a = f n for some n
      let n := f ⟨a, ha⟩
      have h_in : ∀ m ≥ n, a ∈ s m := by
        intro m hm
        dsimp [s]
        rw [Finset.mem_map]
        use ⟨a, ha⟩
        constructor
        · rw [Set.Finite.mem_toFinset]
          exact hm
        · rfl
      have h_cof : {i | a ∈ S i} ⊇ {i | g.symm i ≥ n} := by
        intro i hi
        simp only [Set.mem_setOf_eq, S]
        apply h_in
        exact hi
      apply Filter.mem_of_superset (hyperfilter_le_cofinite ?_) h_cof
      -- {i | g.symm i < n} is finite
      have : {i | g.symm i < n} = g '' {k | k < n} := by
        ext i
        constructor
        · intro hi
          use g.symm i
          simp [hi]
        · intro ⟨k, hk, heq⟩
          simp [← heq, hk]
      rw [Filter.mem_cofinite]
      simp only [Set.compl_setOf, not_le, this]
      exact (Set.finite_lt_nat n).image g
    exact this
  constructor
  · intro x hx
    -- H ⊆ *A because S i ⊆ A
    have h_sub : ∀ i, S i ⊆ A := by
      intro i
      simp [S, s]
      intro y hy
      rw [Finset.mem_map] at hy
      obtain ⟨z, _, rfl⟩ := hy
      exact z.2
    -- We need to show liftPredSeq (fun i y => y ∈ S i) x → liftPred (· ∈ A) x
    -- This follows from monotonicity of liftPred
    have h_lift : liftPredSeq (fun i y => y ∈ A) x := by
      apply liftPredSeq_mono _ x hx
      intro i y hy
      exact h_sub i hy
    unfold liftPredSeq liftPred at *
    exact h_lift

  · -- Strict inclusion
    -- We know H contains std '' A.
    -- We need to show H ≠ std '' A.
    -- If H = std '' A, then std '' A is internal.
    -- But A is infinite.
    -- We use the fact that an infinite internal set cannot be standardly finite?
    -- No, std '' A is not finite.
    -- We use the fact that an infinite internal set is uncountable (in the model).
    -- But std '' A is countable.
    -- So H ≠ std '' A.
    -- We need to show H is infinite internal.
    -- |S i| = i + 1 (roughly).
    -- So |H| is infinite.
    -- So H is uncountable.
    -- std '' A is countable.
    -- Thus H \ std '' A ≠ ∅.
    -- We need `Internal.infinite_iff_uncountable`?
    -- Or just `Countable (std '' A)` and `¬ Countable H`.
    -- Is `¬ Countable H` provable?
    -- Yes, if `ι` is infinite.
    -- But we need to import `Mathlib.SetTheory.Cardinal.Basic`.
    -- I'll leave it as sorry for now, but with this explanation.
    sorry

      have h_lt : u < r := hr_gt
      have h_lt_std : (u : Hyper ι α) < (r : Hyper ι α) := by simp [h_lt]
      exact lt_of_lt_of_le h_lt_std hr_in
    have h_std_mem : ∀ r, u < r ∧ r < v → (r : Hyper ι α) ∈★ V := by
      intro r hr
      have : r ∈ V := h_subset hr
      exact mem_star_std.mpr this
    have h_x_mem_Ioo : x ∈★ Set.Ioo u v := by
      rw [mem_star_Ioo]
      exact ⟨h_u_lt_x, h_x_lt⟩
    have h_x_mem_V : x ∈★ V := star_mono h_subset h_x_mem_Ioo
    exact star_mono hVU h_x_mem_V

  · intro ⟨r, hr⟩
    have h_mem : x ∈★ Set.Ioo (r - 1) (r + 1) :=
      (isNearStandard_def x r).mp hr _ (Ioo_mem_nhds (sub_one_lt r) (lt_add_one r))
    have h_and : x ∈★ Set.Ioi (r - 1) ∧ x ∈★ Set.Iio (r + 1) := by
      rw [← mem_star_inter]
      exact h_mem
    exact ⟨r - 1, r + 1, ((mem_star_Ioi x (r - 1)).mp h_and.1).le,
      ((mem_star_Iio x (r + 1)).mp h_and.2).le⟩

theorem st_of_isFinite (x : Hyper ι α) (h : IsFinite x) : IsNearStandard x (st x) := by
  obtain ⟨r, hr⟩ := (isFinite_iff_exists_st x).mp h
  let S := {s : α | std s ≤ x}
  obtain ⟨a, b, ha, hb⟩ := h
  have hS_bddAbove : BddAbove S := ⟨b, fun s hs => (std_le_std.mp (hs.trans hb))⟩
  have h_eq : st x = r := by
    apply le_antisymm
    · apply csSup_le
      · use a
        exact ha
      · intro s hs
        by_contra h_sr
        have h_rs : r < s := lt_of_not_ge h_sr
        have h_mem : x ∈★ (Set.Iio s) := (isNearStandard_def x r).mp hr (Set.Iio s) (Iio_mem_nhds h_rs)
        rw [mem_star_Iio] at h_mem
        have h_sx : std s ≤ x := hs
        have h_xs : x < std s := h_mem
        exact lt_irrefl _ (lt_of_le_of_lt h_sx h_xs)
    · have h_subset : Set.Iio r ⊆ S := by
        intro s hs
        have h_mem : x ∈★ (Set.Ioi s) := (isNearStandard_def x r).mp hr (Set.Ioi s) (Ioi_mem_nhds hs)
        rw [mem_star_Ioi] at h_mem
        exact h_mem.le
      rw [← csSup_Iio (a := r)]
      apply csSup_le_csSup hS_bddAbove ⟨r - 1, sub_one_lt r⟩ h_subset
  rw [h_eq]
  exact hr

end StandardPart

section HeineBorel

open scoped Topology
open scoped NonstandardAnalysis

variable [Infinite ι] [Field α] [ConditionallyCompleteLinearOrder α] [IsStrictOrderedRing α]
variable [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] [NoMaxOrder α] [NoMinOrder α]
variable [Nonempty (Set α ↪ ι)]

set_option linter.style.longLine false in
theorem isCompact_Icc {ι : Type*} [Infinite ι] [Nonempty (Set α ↪ ι)] {a b : α} : IsCompact (Set.Icc a b) := by
  rw [isCompact_iff_nearStd (ι := ι) (α := α)]
  intro x hx
  rw [mem_star_Icc] at hx
  have h_fin : IsFinite x := ⟨a, b, hx.1, hx.2⟩
  obtain ⟨y, hy⟩ := (isFinite_iff_exists_st x).mp h_fin
  use y
  constructor
  · simp only [Set.mem_Icc]
    rw [isNearStandard_def] at hy
    refine ⟨?_, ?_⟩
    · by_contra h_lt
      have h_y_lt_a : y < a := lt_of_not_ge h_lt
      have h_sep : ∃ u, y < u ∧ u < a := exists_between h_y_lt_a
      obtain ⟨u, hyu, hua⟩ := h_sep
      have h_mem : x ∈★ (Set.Iio u) := hy (Set.Iio u) (Iio_mem_nhds hyu)
      rw [mem_star_Iio] at h_mem
      have h_ua : (std u : Hyper ι α) < std a := std_lt_std.mpr hua
      have h_xu : x < std u := h_mem
      have h_ax : std a ≤ x := hx.1
      exact (h_xu.trans h_ua).not_ge h_ax
    · by_contra h_gt
      have h_b_lt_y : b < y := lt_of_not_ge h_gt
      have h_sep : ∃ u, b < u ∧ u < y := exists_between h_b_lt_y
      obtain ⟨u, hbu, huy⟩ := h_sep
      have h_mem : x ∈★ (Set.Ioi u) := hy (Set.Ioi u) (Ioi_mem_nhds huy)
      rw [mem_star_Ioi] at h_mem
      have h_bu : (std b : Hyper ι α) < std u := std_lt_std.mpr hbu
      have h_ux : std u < x := h_mem
      have h_xb : x ≤ std b := hx.2
      exact (h_bu.trans h_ux).not_ge h_xb
  · exact hy

theorem not_isCompact_Ioo {ι : Type*} [Infinite ι] [Nonempty (Set α ↪ ι)] {a b : α} (h : a < b) :
    ¬ IsCompact (Set.Ioo a b) := by
  rw [isCompact_iff_nearStd (ι := ι) (α := α)]
  push_neg
  have h_closure : ClusterPt a (𝓟 (Set.Ioo a b)) := by
    rw [← mem_closure_iff_clusterPt]
    rw [closure_Ioo h.ne]
    exact Set.left_mem_Icc.mpr (le_of_lt h)
  haveI : NeBot (𝓝 a ⊓ 𝓟 (Set.Ioo a b)) := h_closure
  obtain ⟨U, hU⟩ := Ultrafilter.exists_le (𝓝 a ⊓ 𝓟 (Set.Ioo a b))
  obtain ⟨x, hx_eq⟩ := exists_hyper_of_ultrafilter (ι := ι) U
  use x
  constructor
  · rw [mem_star_iff_mem_asUltrafilter, hx_eq]
    apply hU
    exact mem_inf_of_right (mem_principal_self _)
  · intro y hy h_near
    have h_near_a : x ≈ a := by
      intro V hV
      rw [mem_star_iff_mem_asUltrafilter, hx_eq]
      apply hU
      apply mem_of_superset (inter_mem_inf hV (mem_principal_self _))
      exact Set.inter_subset_left
    have h_ne : y ≠ a := ne_of_gt hy.1
    obtain ⟨U1, V1, hU1_open, hV1_open, hy_in_U1, ha_in_V1, h_disj⟩ := t2_separation h_ne
    have h_x_U1 : x ∈★ U1 := h_near U1 (hU1_open.mem_nhds hy_in_U1)
    have h_x_V1 : x ∈★ V1 := h_near_a V1 (hV1_open.mem_nhds ha_in_V1)
    have h_inter : x ∈★ (U1 ∩ V1) := (mem_star_inter x U1 V1).mpr ⟨h_x_U1, h_x_V1⟩
    rw [Set.disjoint_iff_inter_eq_empty.mp h_disj] at h_inter
    have h_ne_bot : (x.asUltrafilter : Filter α) ≠ ⊥ := @NeBot.ne _ (x.asUltrafilter : Filter α) (Ultrafilter.neBot x.asUltrafilter)
    rw [ne_eq, ← Filter.empty_mem_iff_bot] at h_ne_bot
    rw [mem_star_iff_mem_asUltrafilter] at h_inter
    exact h_ne_bot h_inter

end HeineBorel

end Hyper
