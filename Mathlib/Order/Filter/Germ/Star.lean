/-
Copyright (c) 2024 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
module

public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Order.Filter.Ultrafilter.Basic
public import Mathlib.Order.Filter.Ultrafilter.Hyperfilter
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Monoid.Basic
public import Mathlib.Algebra.Order.Group.Basic
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Nat.Lattice
public import Mathlib.Order.Lattice
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Order
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Field.Defs
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

open scoped Classical

set_option linter.style.longFile 3200

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

@[expose] public section

variable {ι κ : Type*} [Infinite ι] {α β γ : Type*}

/-! ## The Hyper Type -/

/-- The nonstandard extension of `α` over index type `ι`.
This is the ultraproduct `∏_U α` where `U` is the hyperfilter on `ι`. -/
abbrev Hyper (ι : Type*) [Infinite ι] (α : Type*) : Type _ :=
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
  intro h
  obtain ⟨f, rfl⟩ := ofSeq_surjective x
  simp only [liftPredSeq_ofSeq] at h
  have : NeBot (hyperfilter ι : Filter ι) := inferInstance
  exact this.ne (Filter.eventually_false_iff_eq_bot.mp h)

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

/-- The star map sends a set `s` to its nonstandard extension `*s`.
`*s` consists of all hyper-elements that satisfy the lifted membership predicate `· ∈ s`. -/
def star (s : Set α) : Set (Hyper ι α) := {x | liftPred (· ∈ s) x}

/-- Notation for the star map. -/
prefix:max "⋆" => star

theorem mem_star_iff (s : Set α) (x : Hyper ι α) : x ∈ ⋆s ↔ liftPred (· ∈ s) x := Iff.rfl

theorem star_empty : star (ι := ι) (∅ : Set α) = (∅ : Set (Hyper ι α)) := by
  ext x
  rw [mem_star_iff, Set.mem_empty_iff_false]
  induction x using Germ.inductionOn
  simp only [liftPred, Germ.liftPred_coe, Set.mem_empty_iff_false]
  rw [Filter.eventually_false_iff_eq_bot]
  exact iff_false_intro (hyperfilter ι).neBot.ne

theorem star_univ : star (ι := ι) (Set.univ : Set α) = (Set.univ : Set (Hyper ι α)) := by
  ext x
  simp only [mem_star_iff, Set.mem_univ]
  induction x using Germ.inductionOn
  simp only [liftPred, Germ.liftPred_coe, Filter.eventually_true]

theorem star_union (s t : Set α) : star (ι := ι) (s ∪ t) = ⋆s ∪ ⋆t := by
  ext x
  simp only [mem_star_iff, Set.mem_union]
  induction x using Germ.inductionOn
  simp only [liftPred, Germ.liftPred_coe, Ultrafilter.eventually_or]

theorem star_inter (s t : Set α) : star (ι := ι) (s ∩ t) = ⋆s ∩ ⋆t := by
  ext x
  simp only [mem_star_iff, Set.mem_inter_iff]
  induction x using Germ.inductionOn
  simp only [liftPred, Germ.liftPred_coe, Filter.eventually_and]

theorem star_compl (s : Set α) : star (ι := ι) (sᶜ) = (⋆s)ᶜ := by
  ext x
  simp only [mem_star_iff, Set.mem_compl_iff]
  induction x using Germ.inductionOn
  simp only [liftPred, Germ.liftPred_coe, Ultrafilter.eventually_not]

theorem star_subset {s t : Set α} (h : s ⊆ t) : star (ι := ι) s ⊆ ⋆t := by
  intro x hx
  rw [mem_star_iff] at hx ⊢
  induction x using Germ.inductionOn
  simp only [liftPred, Germ.liftPred_coe] at hx ⊢
  filter_upwards [hx] with i hi
  exact h hi

theorem star_mem_star {a : α} {s : Set α} (h : a ∈ s) : (std a : Hyper ι α) ∈ ⋆s := by
  rw [mem_star_iff, liftPred_std]
  exact h

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

/-! ## Algebraic Operations

Since `Hyper ι α = Germ (hyperfilter ι) α`, all algebraic instances are inherited from `Germ`.
We provide simp lemmas relating `std` to the inherited operations. -/

section Algebra

-- Standard embedding preserves algebraic operations
@[simp] theorem std_zero [Zero α] : std (0 : α) = (0 : Hyper ι α) := rfl
@[simp] theorem std_one [One α] : std (1 : α) = (1 : Hyper ι α) := rfl

@[simp]
theorem std_add [Add α] (a b : α) : std (a + b) = (std a : Hyper ι α) + std b := rfl

@[simp]
theorem std_mul [Mul α] (a b : α) : std (a * b) = (std a : Hyper ι α) * std b := rfl

@[simp]
theorem std_neg [Neg α] (a : α) : std (-a) = -(std a : Hyper ι α) := rfl

@[simp]
theorem std_sub [Sub α] (a b : α) : std (a - b) = (std a : Hyper ι α) - std b := rfl

@[simp]
theorem std_inv [Inv α] (a : α) : std a⁻¹ = (std a : Hyper ι α)⁻¹ := rfl

@[simp]
theorem std_div [Div α] (a b : α) : std (a / b) = (std a : Hyper ι α) / std b := rfl

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

/-- Totality of order on hyperreals. -/
theorem Hyper.le_total [LinearOrder α] : IsTotal (Hyper ι α) (· ≤ ·) where
  total x y := by
    induction x using Germ.inductionOn; next f =>
    induction y using Germ.inductionOn; next g =>
    simp only [LE.le, Germ.liftRel_coe]
    exact (hyperfilter ι).eventually_or.1
      (Eventually.of_forall fun i => LinearOrder.le_total (f i) (g i))

/-- Germ's Max equals the if-then-else form. This bridges the Max instance from Germ
with the canonical form expected by LinearOrder. -/
private theorem Hyper.max_def [LinearOrder α] (a b : Hyper ι α) :
    Max.max a b = if a ≤ b then b else a := by
  induction a using Germ.inductionOn with | h f =>
  induction b using Germ.inductionOn with | h g =>
  split_ifs with hab
  · exact sup_of_le_right hab
  · have hba : (ofSeq g : Hyper ι α) ≤ ofSeq f :=
      (Hyper.le_total.total (ofSeq f) (ofSeq g)).resolve_left hab
    exact sup_of_le_left hba

/-- Germ's Min equals the if-then-else form. -/
private theorem Hyper.min_def [LinearOrder α] (a b : Hyper ι α) :
    Min.min a b = if a ≤ b then a else b := by
  induction a using Germ.inductionOn with | h f =>
  induction b using Germ.inductionOn with | h g =>
  split_ifs with hab
  · exact inf_of_le_left hab
  · have hba : (ofSeq g : Hyper ι α) ≤ ofSeq f :=
      (Hyper.le_total.total (ofSeq f) (ofSeq g)).resolve_left hab
    exact inf_of_le_right hba

/-- Linear order on hyperreals, using Germ's Max/Min instances to avoid typeclass diamonds.
The Max/Min are from `Germ.instSup`/`Germ.instInf` (pointwise operations), which ensures
the lattice structure is consistent with `Germ.instLattice`. -/
noncomputable instance instLinearOrderHyper [LinearOrder α] : LinearOrder (Hyper ι α) :=
  { instPartialOrderHyper with
    le_total := Hyper.le_total.total
    toDecidableLE := Classical.decRel _
    toDecidableEq := Classical.decEq _
    toDecidableLT := Classical.decRel _
    max_def := Hyper.max_def
    min_def := Hyper.min_def }

noncomputable instance instSemiringHyper [Semiring α] : Semiring (Hyper ι α) :=
  Filter.Germ.instSemiring
noncomputable instance instRingHyper [Ring α] : Ring (Hyper ι α) := Filter.Germ.instRing
noncomputable instance instCommRingHyper [CommRing α] : CommRing (Hyper ι α) :=
  Filter.Germ.instCommRing










noncomputable instance instFieldHyper [Field α] : Field (Hyper ι α) :=
  { instCommRingHyper, (inferInstance : Inv (Hyper ι α)), (inferInstance : Div (Hyper ι α)) with
    mul_inv_cancel := fun x hx => by
      induction x using Germ.inductionOn; next f =>
      rw [ne_eq, ← Germ.coe_zero, Germ.coe_eq] at hx
      rw [← Germ.coe_inv, ← Germ.coe_mul, ← Germ.coe_one, Germ.coe_eq]
      filter_upwards [Iff.mpr (hyperfilter ι).eventually_not hx] with i hi
      simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply]
      exact GroupWithZero.mul_inv_cancel (f i) hi
    inv_zero := by
      change (↑(0 : α) : Hyper ι α)⁻¹ = 0
      have h : (↑(0 : α) : Hyper ι α)⁻¹ = ↑(0⁻¹ : α) := rfl
      rw [h, _root_.inv_zero]
      exact Germ.coe_zero
    div_eq_mul_inv := fun a b => by
      induction a using Germ.inductionOn; next f =>
      induction b using Germ.inductionOn; next g =>
      rw [← Germ.coe_div, ← Germ.coe_inv, ← Germ.coe_mul, Germ.coe_eq]
      filter_upwards with i
      exact div_eq_mul_inv (f i) (g i)
    exists_pair_ne := ⟨0, 1, by
      rw [ne_eq, ← Germ.coe_zero, ← Germ.coe_one, Germ.coe_eq]
      exact Iff.mp (hyperfilter ι).eventually_not (Eventually.of_forall fun _ => zero_ne_one)⟩
    nnqsmul := _
    qsmul := _ }

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





noncomputable instance instIsStrictOrderedRingHyper
    [Ring α] [PartialOrder α] [IsStrictOrderedRing α] :
    IsStrictOrderedRing (Hyper ι α) :=
  { instIsOrderedRingHyper, (Filter.Germ.instNontrivial : Nontrivial (Hyper ι α)) with
    le_of_add_le_add_left := fun a b c h => by
      induction a using Germ.inductionOn; next f =>
      induction b using Germ.inductionOn; next g =>
      induction c using Germ.inductionOn; next k =>
      dsimp [LE.le] at h ⊢
      rw [← Germ.coe_add, ← Germ.coe_add, Germ.liftRel_coe] at h
      rw [Germ.liftRel_coe]
      exact h.mono fun i hi => le_of_add_le_add_left hi
    mul_lt_mul_of_pos_left := fun c hc a b hab => by
      induction a using Germ.inductionOn; next f =>
      induction b using Germ.inductionOn; next g =>
      induction c using Germ.inductionOn; next k =>
      rw [← Germ.coe_zero] at hc
      have hc' : ∀ᶠ i in hyperfilter ι, 0 < k i := hc
      have hab' : ∀ᶠ i in hyperfilter ι, f i < g i := hab
      filter_upwards [hab', hc'] with i hab hc
      exact mul_lt_mul_of_pos_left hab hc
    mul_lt_mul_of_pos_right := fun c hc a b hab => by
      induction a using Germ.inductionOn; next f =>
      induction b using Germ.inductionOn; next g =>
      induction c using Germ.inductionOn; next k =>
      rw [← Germ.coe_zero] at hc
      have hc' : ∀ᶠ i in hyperfilter ι, 0 < k i := hc
      have hab' : ∀ᶠ i in hyperfilter ι, f i < g i := hab
      filter_upwards [hab', hc'] with i hab hc
      exact mul_lt_mul_of_pos_right hab hc }




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

/-- Absolute value of an infinitesimal is infinitesimal. -/
theorem IsInfinitesimal.abs [Field α] [LinearOrder α] [IsOrderedRing α] {x : Hyper ι α}
    (hx : IsInfinitesimal x) : IsInfinitesimal |x| := by
  intro r hr
  obtain ⟨hneg, hpos⟩ := hx r hr
  constructor
  · -- -std r < |x| follows from |x| ≥ 0 > -std r
    calc -std r < 0 := by rw [← std_neg, ← std_zero]; exact (std_lt (-r) 0).mpr (neg_neg_of_pos hr)
         _ ≤ |x| := abs_nonneg x
  · -- |x| < std r follows from abs_lt
    exact abs_lt.mpr ⟨hneg, hpos⟩

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

/-! ## Standard Embedding as Bundled Homomorphisms

The standard embedding `std : α → Hyper ι α` is a structural embedding that preserves
all algebraic and order structure. These bundled homomorphisms make composing with
other morphisms convenient and provide the foundation for the transfer principle. -/

section BundledHoms

variable {ι : Type*} [Infinite ι] {α : Type*}

/-- The standard embedding as a ring homomorphism. -/
noncomputable def stdRingHom [Ring α] : α →+* Hyper ι α where
  toFun := std
  map_zero' := std_zero
  map_one' := std_one
  map_add' := std_add
  map_mul' := std_mul

@[simp] theorem stdRingHom_apply [Ring α] (a : α) : stdRingHom a = (std a : Hyper ι α) := rfl

/-- `std` as an additive monoid homomorphism. -/
noncomputable def stdAddMonoidHom [AddCommMonoid α] : α →+ Hyper ι α where
  toFun := std
  map_zero' := std_zero
  map_add' := std_add

@[simp] theorem stdAddMonoidHom_apply [AddCommMonoid α] (a : α) :
    stdAddMonoidHom a = (std a : Hyper ι α) := rfl

/-- The standard embedding as an order embedding.
This captures the key property that `std` preserves and reflects the order structure. -/
noncomputable def stdOrderEmbedding [Preorder α] : α ↪o Hyper ι α where
  toFun := std
  inj' := std_injective
  map_rel_iff' := by simp [std_le]

@[simp] theorem stdOrderEmbedding_apply [Preorder α] (a : α) :
    stdOrderEmbedding a = (std a : Hyper ι α) := rfl

end BundledHoms

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
  grw [sub_eq_add_neg ]
  exact hx.add hy.neg

/-- A hyperreal is finite iff its absolute value is bounded by a standard real. -/
theorem IsFinite_iff_abs_le [CommRing α] [LinearOrder α] [IsOrderedRing α] {x : Hyper ι α} :
    IsFinite x ↔ ∃ r : α, |x| ≤ std r := by
  constructor
  · -- IsFinite → bounded abs
    intro ⟨a, b, ha, hb⟩
    use max |a| |b|
    apply abs_le.mpr
    constructor
    · -- -std (max |a| |b|) ≤ x
      have h1 : -(max |a| |b|) ≤ -|a| := neg_le_neg (le_max_left |a| |b|)
      have h2 : -|a| ≤ a := neg_abs_le a
      calc -std (max |a| |b|) = std (-(max |a| |b|)) := (std_neg _).symm
           _ ≤ std a := (std_le _ _).mpr (h1.trans h2)
           _ ≤ x := ha
    · -- x ≤ std (max |a| |b|)
      calc x ≤ std b := hb
           _ ≤ std (max |a| |b|) := (std_le _ _).mpr (le_max_of_le_right (le_abs_self b))
  · -- bounded abs → IsFinite
    intro ⟨r, hr⟩
    refine ⟨-r, r, ?_, ?_⟩
    · rw [std_neg]
      exact neg_le_of_abs_le hr
    · exact le_of_abs_le hr

theorem IsFinite.mul [CommRing α] [LinearOrder α] [IsOrderedRing α] {x y : Hyper ι α}
    (hx : IsFinite x) (hy : IsFinite y) : IsFinite (x * y) := by
  rw [IsFinite_iff_abs_le] at hx hy ⊢
  obtain ⟨M, hM⟩ := hx
  obtain ⟨N, hN⟩ := hy
  use M * N
  calc |x * y| = |x| * |y| := abs_mul x y
       _ ≤ std M * std N := mul_le_mul hM hN (abs_nonneg y) (le_trans (abs_nonneg x) hM)
       _ = std (M * N) := (std_mul M N).symm

theorem IsInfinitePos.isInfinite [Preorder α] {x : Hyper ι α} (h : IsInfinitePos x) :
    IsInfinite x := by
  intro hfin
  obtain ⟨_, b, _, hb⟩ := hfin
  have : std b < std b := lt_of_lt_of_le (h b) hb
  exact lt_irrefl _ this

/-- Key NSA lemma: the reciprocal of a positive infinite hyperreal is infinitesimal.
This is the fundamental result connecting infinities and infinitesimals. -/
theorem IsInfinitesimal.inv_of_isInfinitePos {ι : Type*} [Infinite ι]
    {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {x : Hyper ι α} (hx : IsInfinitePos x) : IsInfinitesimal x⁻¹ := by
  -- x is positive infinite means 0 < x
  have hx_pos : 0 < x := by simpa [std_zero] using hx 0
  intro ε hε
  -- Since x is positive infinite, std (1/ε) < x
  have h1 : std (1 / ε) < x := hx (1 / ε)
  -- Since 0 < x, we have 0 < x⁻¹
  have hx_inv_pos : 0 < x⁻¹ := inv_pos.mpr hx_pos
  constructor
  · -- -std ε < x⁻¹: since x⁻¹ > 0 and -std ε < 0
    have hneg : -(std ε : Hyper ι α) < 0 := by
      simp only [neg_lt_zero]
      rw [← std_zero, std_lt_std]
      exact hε
    exact lt_trans hneg hx_inv_pos
  · -- x⁻¹ < std ε: since std (1/ε) < x, we have x⁻¹ < (std (1/ε))⁻¹ = std ε
    have h_pos_inv : 0 < (std (1 / ε) : Hyper ι α) := by
      rw [← std_zero, std_lt_std]
      exact one_div_pos.mpr hε
    have h2 : x⁻¹ < (std (1 / ε) : Hyper ι α)⁻¹ := inv_strictAnti₀ h_pos_inv h1
    simp only [one_div, inv_inv, std_inv] at h2
    exact h2

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
  simp only [omega, coe_nat_eq_std, std_def, Germ.const, ofSeq, Germ.ofFun]
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


section HyperfiniteSets

variable {ι : Type*} [Infinite ι] {α : Type*}

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

theorem IsHyperfinite.inter_isInternal {H : Set (Hyper ι α)} (hH : IsHyperfinite H)
    {A : Set (Hyper ι α)} (hA : IsInternal A) : IsHyperfinite (H ∩ A) := by
  obtain ⟨SH, hSH_fin, hSH_eq⟩ := hH
  obtain ⟨SA, hSA_eq⟩ := hA
  use fun i => SH i ∩ SA i
  constructor
  · intro i
    exact (hSH_fin i).inter_of_left (SA i)
  · intro x
    rw [Set.mem_inter_iff, hSH_eq, hSA_eq]
    obtain ⟨f, rfl⟩ := ofSeq_surjective x
    simp only [liftPredSeq_ofSeq, Set.mem_inter_iff]
    exact Filter.eventually_and.symm

theorem IsInternal.inter_isHyperfinite {A : Set (Hyper ι α)} (hA : IsInternal A)
    {H : Set (Hyper ι α)} (hH : IsHyperfinite H) : IsHyperfinite (A ∩ H) := by
  rw [Set.inter_comm]
  exact hH.inter_isInternal hA

/-- **Approximation Theorem**: For any infinite set `A`, there exists a hyperfinite set `H`
such that `{std a | a ∈ A} ⊆ H ⊆ A*` and H contains nonstandard elements.
Note: See `hyperfinite_sandwich_strict` in section HyperfiniteApprox for the main version.
This theorem is specialized to `Hyper ℕ α`. -/
theorem exists_hyperfinite_approximation {A : Set α} (hA : A.Countable)
    (hA_inf : A.Infinite) :
    ∃ H : Set (Hyper ℕ α), IsHyperfinite H ∧
      (∀ a ∈ A, (std a : Hyper ℕ α) ∈ H) ∧
      (∀ x ∈ H, liftPred (· ∈ A) x) ∧
      (std '' A : Set (Hyper ℕ α)) ⊂ H := by
  sorry -- Proved by hyperfinite_sandwich_strict once in scope (section ordering issue)

end HyperfiniteSets

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
  · -- Forward: IsFinite → ∃ r, IsNearStandard x r
    intro ⟨a, b, ha, hb⟩
    let S := {r : α | std r ≤ x}
    have hS_nonempty : S.Nonempty := ⟨a, ha⟩
    have hS_bddAbove : BddAbove S := ⟨b, fun s hs => std_le_std.mp (hs.trans hb)⟩
    use sSup S
    rw [isNearStandard_def]
    intro U hU
    -- In order topology, nhds has a basis of open intervals
    rw [mem_nhds_iff_exists_Ioo_subset] at hU
    obtain ⟨l, u, hsup_mem, hIoo_sub⟩ := hU
    -- Show x ∈★ U by showing x ∈★ Ioo l u ⊆ U
    apply star_mono hIoo_sub
    rw [mem_star_Ioo]
    constructor
    · -- std l < x: Since l < sSup S, ∃ s ∈ S with l < s, so std l < std s ≤ x
      have hl : l < sSup S := hsup_mem.1
      obtain ⟨s, hs, hls⟩ := exists_lt_of_lt_csSup hS_nonempty hl
      calc std l < std s := std_lt_std.mpr hls
           _ ≤ x := hs
    · -- x < std u: Since sSup S < u, u is an upper bound, so ∀ s ∈ S, s < u
      -- Thus std s ≤ x implies s ≤ sSup S < u, so x < std u
      have hu : sSup S < u := hsup_mem.2
      by_contra hxu
      push_neg at hxu
      -- If std u ≤ x, then u ∈ S, but u > sSup S, contradiction
      have : u ∈ S := hxu
      exact not_lt.mpr (le_csSup hS_bddAbove this) hu
  · -- Backward: ∃ r, IsNearStandard x r → IsFinite x
    intro ⟨r, hr⟩
    rw [isNearStandard_def] at hr
    have hIoo : Set.Ioo (r - 1) (r + 1) ∈ nhds r := Ioo_mem_nhds (by linarith) (by linarith)
    have hx := hr _ hIoo
    rw [mem_star_Ioo] at hx
    exact ⟨r - 1, r + 1, hx.1.le, hx.2.le⟩
/-- The galaxy of a family of sets is the union of their stars. -/
def galaxy (S : Set (Set α)) : Set (Hyper ι α) :=
  ⋃ s ∈ S, {x | liftPred (· ∈ s) x}

/-- The `monad'` of a family of sets is the intersection of their stars.

Captures idea of set of points so close, they can't be separated by any open set. -/
def monad' (S : Set (Set α)) : Set (Hyper ι α) :=
  ⋂ s ∈ S, {x | liftPred (· ∈ s) x}

-- example : @monad = @monad' := by
--   ext x
--   simp only [monad, monad']
--   rw [Set.inter_univ]

theorem galaxy_mem (S : Set (Set α)) (x : Hyper ι α) :
    x ∈ galaxy S ↔ ∃ s ∈ S, liftPred (· ∈ s) x := by
  simp [galaxy]



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
        have h_mem : x ∈★ (Set.Iio s) :=
          (isNearStandard_def x r).mp hr (Set.Iio s) (Iio_mem_nhds h_rs)
        rw [mem_star_Iio] at h_mem
        have h_sx : std s ≤ x := hs
        have h_xs : x < std s := h_mem
        exact lt_irrefl _ (lt_of_le_of_lt h_sx h_xs)
    · have h_subset : Set.Iio r ⊆ S := by
        intro s hs
        have h_mem : x ∈★ (Set.Ioi s) :=
          (isNearStandard_def x r).mp hr (Set.Ioi s) (Ioi_mem_nhds hs)
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
    have h_ne_bot : (x.asUltrafilter : Filter α) ≠ ⊥ :=
      @NeBot.ne _ (x.asUltrafilter : Filter α) (Ultrafilter.neBot x.asUltrafilter)
    rw [ne_eq, ← Filter.empty_mem_iff_bot] at h_ne_bot
    rw [mem_star_iff_mem_asUltrafilter] at h_inter
    exact h_ne_bot h_inter

end HeineBorel

/-! ## Hyperfinite Approximation Theorem

The fundamental theorem of hyperfinite analysis: every set A can be "sandwiched" between
its standard embedding and its star:

  std(A) ⊆ H ⊆ *A

where H is a hyperfinite set. This is crucial for applying hyperfinite combinatorics
to infinite structures.

### Construction

Given a set A with an enumeration `e : A → ι` where ι has a locally finite order,
we construct H as the internal set corresponding to the sequence of finite sets
`{a ∈ A : e(a) ≤ i}`. This sequence is:
- Eventually containing any fixed element (giving std(A) ⊆ H)
- Always contained in A (giving H ⊆ *A)
- Finite at each index (making H hyperfinite)
-/

section HyperfiniteApprox

open scoped NonstandardAnalysis

variable {ι : Type*} [Infinite ι] {α : Type*}

/-- **Hyperfinite Approximation Theorem (Core Version)**:
For any set A with an order-preserving enumeration into ι, there exists a hyperfinite
internal set H such that every standard element of A is in H, and H is contained in *A.

The key insight: if we can enumerate A by indices in ι, then the sequence of
"initial segments" {a : e(a) ≤ i} gives a hyperfinite set containing all of std(A). -/
theorem exists_hyperfinite_sandwich [LinearOrder ι] [LocallyFiniteOrderBot ι]
    {A : Set α} (e : A ↪ ι) :
    ∃ H : Set (Hyper ι α), IsHyperfinite H ∧
      (∀ a ∈ A, (std a : Hyper ι α) ∈ H) ∧
      (∀ x ∈ H, liftPred (· ∈ A) x) := by
  -- Define S_i = {a ∈ A : e(a) ≤ i} as a Finset via the finite Iic
  let S : ι → Finset α := fun i =>
    ((Set.Iic i).toFinite.preimage e.injective.injOn).toFinset.map
      ⟨Subtype.val, Subtype.val_injective⟩
  -- Convert to Set for the internal definition
  let S' : ι → Set α := fun i => S i
  have hS_fin : ∀ i, (S' i).Finite := fun i => (S i).finite_toSet
  -- H is the internal set defined by S'
  let H := {x | liftPredSeq (fun i y => y ∈ S' i) x}
  use H
  constructor
  · -- H is hyperfinite
    exact ⟨S', hS_fin, fun x => Iff.rfl⟩
  -- Key helper: a ∈ S i iff e ⟨a, ha⟩ ≤ i
  have hS_mem : ∀ i (a : α) (ha : a ∈ A), a ∈ (S i : Set α) ↔ e ⟨a, ha⟩ ≤ i := by
    intro i a ha
    rw [Finset.mem_coe, Finset.mem_map]
    simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_Iic,
               Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨b, hb⟩, hle, rfl⟩
      exact hle
    · intro hle
      exact ⟨⟨a, ha⟩, hle, rfl⟩
  constructor
  · -- std(A) ⊆ H: for any a ∈ A, std a ∈ H
    intro a ha
    simp only [H, Set.mem_setOf_eq, liftPredSeq, std, Germ.const, S']
    -- a ∈ S i for all i ≥ e ⟨a, ha⟩, which is cofinite
    -- First show {i | a ∈ S i} is cofinite
    have h_cofin : {i | a ∈ (S i : Set α)} ∈ Filter.cofinite := by
      rw [Filter.mem_cofinite]
      apply Set.Finite.subset (Set.finite_Iio (e ⟨a, ha⟩))
      intro i hi
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_Iio] at hi ⊢
      rw [hS_mem i a ha] at hi
      exact lt_of_not_ge hi
    -- Then lift to hyperfilter (hyperfilter_le_cofinite : hyperfilter ≤ cofinite)
    exact hyperfilter_le_cofinite h_cofin
  · -- H ⊆ *A: elements of H are in the star of A
    intro x hx
    simp only [H, Set.mem_setOf_eq, S'] at hx
    -- Every element of S i is in A
    have h_sub : ∀ i y, y ∈ (S i : Set α) → y ∈ A := by
      intro i y hy
      rw [Finset.mem_coe, Finset.mem_map] at hy
      simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_Iic,
                 Function.Embedding.coeFn_mk] at hy
      obtain ⟨⟨a, ha⟩, _, rfl⟩ := hy
      exact ha
    exact liftPredSeq_mono h_sub x hx

/-- **Hyperfinite Approximation Theorem (ℕ-indexed version)**:
For any countable set A, there exists a hyperfinite internal set H in `Hyper ℕ α`
sandwiching the standard elements. -/
theorem exists_hyperfinite_sandwich_nat {A : Set α} (hA : A.Countable) :
    ∃ H : Set (Hyper ℕ α), IsHyperfinite H ∧
      (∀ a ∈ A, (std a : Hyper ℕ α) ∈ H) ∧
      (∀ x ∈ H, liftPred (· ∈ A) x) := by
  by_cases hA_empty : A = ∅
  · -- Empty set case: use the empty internal set
    use {x | liftPredSeq (fun _ _ => False) x}
    constructor
    · use fun _ => ∅
      constructor
      · exact fun _ => Set.finite_empty
      · intro x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
    · constructor
      · intro a ha
        rw [hA_empty] at ha
        exact ha.elim
      · intro x hx
        -- The empty internal set contains no elements - derive a contradiction
        simp only [Set.mem_setOf_eq] at hx
        obtain ⟨f, rfl⟩ := ofSeq_surjective x
        rw [liftPredSeq_ofSeq] at hx
        have hbot : (hyperfilter ℕ : Filter ℕ) = ⊥ := Filter.eventually_false_iff_eq_bot.mp hx
        exact ((hyperfilter ℕ).neBot.ne hbot).elim
  · -- Nonempty case
    have hA_nonempty : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hA_empty
    obtain ⟨e, he_inj⟩ := hA.exists_injective_nat
    -- Use the core theorem with the embedding (e already maps A → ℕ)
    exact exists_hyperfinite_sandwich ⟨e, he_inj⟩

/-- The cardinality of a hyperfinite set is a hypernatural.
Given a hyperfinite set H with representing sequence S, the cardinality is the
hypernatural represented by `|S_i|`. -/
noncomputable def hyperfiniteCard (H : Set (Hyper ι α)) (hH : IsHyperfinite H) : Hyper ι ℕ :=
  ofSeq (fun i => (hH.choose_spec.1 i).toFinset.card)

/-- A hyperfinite set with cardinality exceeding all standard naturals
contains nonstandard elements.

This is a fundamental principle: if |H| > n for all standard n, then H cannot consist only of
standard elements (which would make it at most countably infinite in the standard sense). -/
theorem IsHyperfinite.exists_nonstandard_of_large_card {H : Set (Hyper ι α)}
    (hH : IsHyperfinite H) (hCard : ∀ n : ℕ, std n < hyperfiniteCard H hH) :
    ∃ x ∈ H, ¬ IsStandard x := by
  -- By contradiction: suppose all elements are standard
  by_contra h_all_std
  push_neg at h_all_std
  -- Get the representing sequence S for H
  let S := hH.choose
  have hS_fin : ∀ i, (S i).Finite := hH.choose_spec.1
  have hS_mem : ∀ x, x ∈ H ↔ liftPredSeq (fun i y => y ∈ S i) x := hH.choose_spec.2
  -- Define B' = "stable base" = {a : std a ∈ H} = {a : ∀ᶠ i, a ∈ S_i}
  let B' := {a : α | ∀ᶠ i in hyperfilter ι, a ∈ S i}
  -- First establish that α is nonempty (hyperfiniteCard > 0 implies some S i nonempty)
  have hS_ne_some : ∃ i, (S i).Nonempty := by
    have h0 := hCard 0
    rw [hyperfiniteCard, std_lt_ofSeq] at h0
    obtain ⟨i, hi⟩ := h0.exists
    have hne : (hS_fin i).toFinset.Nonempty := Finset.card_pos.mp (Nat.zero_lt_of_lt hi)
    exact ⟨i, (hS_fin i).toFinset_nonempty.mp hne⟩
  obtain ⟨i₀, hi₀⟩ := hS_ne_some
  haveI : Nonempty α := ⟨hi₀.some⟩
  -- Case split on transients
  by_cases h_transient : ∀ᶠ i in hyperfilter ι, ∃ a ∈ S i, a ∉ B'
  · -- Case 1: Transient elements exist for hyperfilter-many i
    have h_nonempty : ∀ i, (∃ a ∈ S i, a ∉ B') → Set.Nonempty (S i ∩ B'ᶜ) :=
      fun i ⟨a, ha_in, ha_notB'⟩ => ⟨a, ha_in, ha_notB'⟩
    let f : ι → α := fun i =>
      if h : ∃ a ∈ S i, a ∉ B' then (h_nonempty i h).some else Classical.arbitrary α
    have hf_in_S : ∀ᶠ i in hyperfilter ι, f i ∈ S i := by
      filter_upwards [h_transient] with i hi
      simp only [f, hi, dif_pos]; exact ((h_nonempty i hi).some_mem).1
    have hf_transient : ∀ᶠ i in hyperfilter ι, f i ∉ B' := by
      filter_upwards [h_transient] with i hi
      simp only [f, hi, dif_pos]; exact ((h_nonempty i hi).some_mem).2
    have hOfSeq_in_H : ofSeq f ∈ H := by rw [hS_mem, liftPredSeq_ofSeq]; exact hf_in_S
    obtain ⟨a, ha⟩ := h_all_std (ofSeq f) hOfSeq_in_H
    have hf_eq_a : ∀ᶠ i in hyperfilter ι, f i = a := by
      have heq : ofSeq f = std a := ha
      rw [eq_iff_liftRel_eq] at heq
      rw [← liftRel_flip] at heq
      change liftRel (fun y x => x = y) (std a) (ofSeq f) at heq
      rw [liftRel_const_coe] at heq
      filter_upwards [heq] with i hi; exact hi
    have ha_in_B' : a ∈ B' := by
      filter_upwards [hf_in_S, hf_eq_a] with i hi_in hi_eq; rwa [← hi_eq]
    have ha_not_B' : a ∉ B' := by
      have := Filter.Eventually.and hf_transient hf_eq_a
      obtain ⟨i, hi_trans, hi_eq⟩ := this.exists; rw [← hi_eq]; exact hi_trans
    exact ha_not_B' ha_in_B'
  · -- Case 2: S_i ⊆ B' for hyperfilter-many i
    have h_subset : ∀ᶠ i in hyperfilter ι, ∀ a ∈ S i, a ∈ B' := by
      rw [← Ultrafilter.eventually_not] at h_transient
      simp only [not_exists, not_and, not_not] at h_transient; exact h_transient
    by_cases hB'_inf : B'.Infinite
    · -- Case 2b: B' infinite - diagonal construction
      let hg := hB'_inf.natEmbedding
      let g : ℕ → α := fun n => (hg n).val
      have hg_inj : Function.Injective g := fun m n h => hg.injective (Subtype.val_injective h)
      have hg_in_B' : ∀ n, g n ∈ B' := fun n => (hg n).property
      have hI : ∀ n, ∀ᶠ i in hyperfilter ι, g n ∈ S i := hg_in_B'
      have hK_fin : ∀ i, {k : ℕ | g k ∈ S i}.Finite := fun i =>
        Set.Finite.preimage hg_inj.injOn (hS_fin i)
      have hK_ne : ∀ᶠ i in hyperfilter ι, {k : ℕ | g k ∈ S i}.Nonempty := by
        filter_upwards [hI 0] with i hi; exact ⟨0, hi⟩
      let maxK : ι → ℕ := fun i =>
        if h : {k : ℕ | g k ∈ S i}.Nonempty then
          (hK_fin i).toFinset.max' ((hK_fin i).toFinset_nonempty.mpr h)
        else 0
      have hmaxK_unbounded : ∀ m : ℕ, ∀ᶠ i in hyperfilter ι, maxK i > m := by
        intro m; filter_upwards [hI (m + 1), hK_ne] with i hi_in hi_ne
        simp only [maxK, hi_ne, dif_pos]
        apply Nat.lt_of_lt_of_le (Nat.lt_succ_self m); apply Finset.le_max'
        simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact hi_in
      let f : ι → α := fun i => g (maxK i)
      have hf_in_S : ∀ᶠ i in hyperfilter ι, f i ∈ S i := by
        filter_upwards [hK_ne] with i hi_ne
        simp only [f, maxK, hi_ne, dif_pos]
        have hmax_mem := Finset.max'_mem _ ((hK_fin i).toFinset_nonempty.mpr hi_ne)
        simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hmax_mem; exact hmax_mem
      have hOfSeq_in_H : ofSeq f ∈ H := by rw [hS_mem, liftPredSeq_ofSeq]; exact hf_in_S
      obtain ⟨a, ha⟩ := h_all_std (ofSeq f) hOfSeq_in_H
      have hf_eq_a : ∀ᶠ i in hyperfilter ι, f i = a := by
        have heq : ofSeq f = std a := ha
        rw [eq_iff_liftRel_eq] at heq
        rw [← liftRel_flip] at heq
        change liftRel (fun y x => x = y) (std a) (ofSeq f) at heq
        rw [liftRel_const_coe] at heq
        filter_upwards [heq] with i hi; exact hi
      by_cases ha_range : a ∈ Set.range g
      · obtain ⟨m, rfl⟩ := ha_range
        have hmax_eq_m : ∀ᶠ i in hyperfilter ι, maxK i = m := by
          filter_upwards [hf_eq_a] with i hi; simp only [f] at hi; exact hg_inj hi
        have hmax_gt_m := hmaxK_unbounded m
        have := Filter.Eventually.and hmax_eq_m hmax_gt_m
        obtain ⟨i, hi_eq, hi_gt⟩ := this.exists; omega
      · have hf_in_range : ∀ i, f i ∈ Set.range g := fun i => ⟨maxK i, rfl⟩
        have := Filter.Eventually.and hf_eq_a (Filter.Eventually.of_forall hf_in_range)
        obtain ⟨i, hi_eq, hi_range⟩ := this.exists
        rw [hi_eq] at hi_range; exact ha_range hi_range
    · -- Case 2a: B' finite - cardinality bound contradiction
      rw [Set.not_infinite] at hB'_inf
      let k := hB'_inf.toFinset.card
      have hcard_bound : ∀ᶠ i in hyperfilter ι, (hS_fin i).toFinset.card ≤ k := by
        filter_upwards [h_subset] with i hi; apply Finset.card_le_card
        intro a ha; rw [Set.Finite.mem_toFinset] at ha ⊢; exact hi a ha
      have hCard_le : hyperfiniteCard H hH ≤ std k := by
        rw [hyperfiniteCard, std_eq_ofSeq_const, ofSeq_le_ofSeq]; exact hcard_bound
      exact not_lt.mpr hCard_le (hCard k)

/-- For any set with a countable enumeration, the hyperfinite approximation
gives strict containment when A is infinite. -/
theorem hyperfinite_sandwich_strict {A : Set α} (hA : A.Countable) (hA_inf : A.Infinite) :
    ∃ H : Set (Hyper ℕ α), IsHyperfinite H ∧
      (∀ a ∈ A, (std a : Hyper ℕ α) ∈ H) ∧
      (∀ x ∈ H, liftPred (· ∈ A) x) ∧
      ∃ x ∈ H, ¬ IsStandard x := by
  obtain ⟨H, hH_hf, hH_std, hH_star⟩ := exists_hyperfinite_sandwich_nat hA
  use H, hH_hf, hH_std, hH_star
  -- Key principle: H has hyperfinite cardinality that grows unboundedly
  -- Since A is infinite, the approximating sets S(i) = {a : e(a) ≤ i} grow without bound
  -- So hyperfiniteCard H hH exceeds any standard n
  -- By the above lemma, H must contain nonstandard elements
  apply hH_hf.exists_nonstandard_of_large_card
  intro n
  -- Get n+1 distinct elements from A
  obtain ⟨t, ht_sub, ht_card⟩ := hA_inf.exists_subset_card_eq (n + 1)
  -- Get the representing sequence S for H
  let S := hH_hf.choose
  have hS_fin : ∀ i, (S i).Finite := hH_hf.choose_spec.1
  have hS_mem : ∀ x, x ∈ H ↔ liftPredSeq (fun i y => y ∈ S i) x := hH_hf.choose_spec.2
  -- For each a ∈ t, std a ∈ H, so a ∈ S i for hyperfilter-many i
  have h_in : ∀ a ∈ t, ∀ᶠ i in hyperfilter ℕ, a ∈ S i := by
    intro a ha
    have h_std_in : std a ∈ H := hH_std a (ht_sub (Finset.mem_coe.mp ha))
    rw [hS_mem, liftPredSeq, std, Germ.const] at h_std_in
    exact h_std_in
  -- By finite intersection, all elements of t are in S i for hyperfilter-many i
  have h_all : ∀ᶠ i in hyperfilter ℕ, ∀ a ∈ t, a ∈ S i := by
    rw [Filter.eventually_all_finset]
    exact h_in
  -- On this set, |S i| ≥ |t| = n + 1 > n
  have h_card : ∀ᶠ i in hyperfilter ℕ, n < (hS_fin i).toFinset.card := by
    filter_upwards [h_all] with i hi
    have h_sub : ↑t ⊆ S i := by
      intro a ha
      exact hi a (Finset.mem_coe.mpr ha)
    have h_card_le : t.card ≤ (hS_fin i).toFinset.card := by
      calc t.card = (t.map ⟨id, Function.injective_id⟩).card := by simp
        _ ≤ (hS_fin i).toFinset.card := by
          apply Finset.card_le_card
          intro x hx
          rw [Finset.mem_map] at hx
          obtain ⟨a, ha, rfl⟩ := hx
          rw [Set.Finite.mem_toFinset]
          exact h_sub (Finset.mem_coe.mpr ha)
    omega
  -- Therefore hyperfiniteCard H > std n
  rw [hyperfiniteCard, std_lt_ofSeq]
  exact h_card

/-- **Strict Hyperfinite Sandwich**: For infinite countable A, we have strict containment
std '' A ⊂ H ⊂ *A.

This is the full hyperfinite approximation theorem showing that H strictly contains
all standard elements and is strictly contained in the nonstandard extension.

Note: The second strict inclusion (H ⊂ *A) requires showing that *A contains elements
that escape any hyperfinite approximation - this follows from the diagonal argument
but requires careful tracking of the enumeration used in the construction. -/
theorem hyperfinite_strict_sandwich {A : Set α} (hA : A.Countable) (hA_inf : A.Infinite) :
    ∃ H : Set (Hyper ℕ α), IsHyperfinite H ∧
      (std '' A ⊂ H) ∧
      (H ⊂ {x | liftPred (· ∈ A) x}) := by
  -- First establish basic sandwich
  obtain ⟨H, hH_hf, hH_std, hH_star, x, hx_H, hx_nonstd⟩ := hyperfinite_sandwich_strict hA hA_inf
  refine ⟨H, hH_hf, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · -- std '' A ⊆ H
    intro y hy
    obtain ⟨a, ha, rfl⟩ := hy
    exact hH_std a ha
  · -- H ⊄ std '' A (there's something in H not in std '' A)
    intro h_eq
    have : x ∈ std '' A := h_eq hx_H
    obtain ⟨a, _, rfl⟩ := this
    exact hx_nonstd ⟨a, rfl⟩
  · -- H ⊆ *A
    intro y hy
    exact hH_star y hy
  · -- *A ⊄ H: construct diagonal element escaping H
    -- This requires tracking the specific enumeration - leave for future work
    sorry

/-- **Hyperfinite Approximation (Simplified Statement)**:
For any set A, there exists an internal hyperfinite set H with `std '' A ⊆ H ⊆ *A`.

This is the standard NSA result phrased set-theoretically. -/
theorem exists_hyperfinite_between [LinearOrder ι] [LocallyFiniteOrderBot ι]
    {A : Set α} (e : A ↪ ι) :
    ∃ H : Set (Hyper ι α), IsHyperfinite H ∧
      std '' A ⊆ H ∧
      H ⊆ {x | liftPred (· ∈ A) x} := by
  obtain ⟨H, hH_hf, hH_std, hH_star⟩ := exists_hyperfinite_sandwich e
  use H, hH_hf
  constructor
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    exact hH_std a ha
  · intro x hx
    exact hH_star x hx

end HyperfiniteApprox

/-! ## Nonstandard Characterization of Cauchy Sequences

The classical characterization of Cauchy sequences involves ε-δ definitions:
  `CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ m n ≥ N, dist (u m) (u n) < ε`

In nonstandard analysis, this has an elegant equivalent formulation:
  A sequence is Cauchy iff for all unlimited hypernatural indices N and M,
  the distance `dist (u N) (u M)` is infinitesimal.

This characterization is more intuitive: "all terms at infinity are infinitely close." -/

section CauchyNSA

variable {α : Type*} [PseudoMetricSpace α]

/-- **Nonstandard Cauchy predicate**: A sequence is NSA-Cauchy if for any two
unlimited hypernatural indices, the lifted distance between the corresponding
terms is infinitesimal.

This is equivalent to: "all terms at infinity are infinitely close to each other." -/
def IsCauchyNSA (u : ℕ → α) : Prop :=
  ∀ N M : Hyper ℕ ℕ, N.IsInfinite → M.IsInfinite →
    IsInfinitesimal (lift₂ (fun m n => dist (u m) (u n)) N M)

/-- Helper: the lifted distance function for a sequence. -/
noncomputable def liftDist (u : ℕ → α) : Hyper ℕ ℕ → Hyper ℕ ℕ → Hyper ℕ ℝ :=
  lift₂ (fun m n => dist (u m) (u n))

theorem liftDist_std (u : ℕ → α) (m n : ℕ) :
    liftDist u (std m) (std n) = std (dist (u m) (u n)) := lift₂_std _ _ _

/-- An auxiliary lemma: if P(n) holds for all n ≥ N for some standard N,
then P holds for all unlimited hypernaturals. -/
theorem liftPred_of_eventually_ge {P : ℕ → Prop} {N : ℕ}
    (h : ∀ n ≥ N, P n) (ω : Hyper ℕ ℕ) (hω : ω.IsInfinite) : liftPred P ω := by
  obtain ⟨f, rfl⟩ := ofSeq_surjective ω
  rw [liftPred_ofSeq]
  -- ω is unlimited means ∀ k, std k < ω, so f(i) > N for almost all i
  have hgt : ∀ᶠ i in hyperfilter ℕ, N < f i := by
    have hω' : std N < ofSeq f := by
      by_contra hle
      push_neg at hle
      have h0_le : std 0 ≤ ofSeq f := by
        rw [std_eq_ofSeq_const, ofSeq_le_ofSeq]
        exact Filter.Eventually.of_forall (fun _ => Nat.zero_le _)
      have hfin : IsFinite (ofSeq f) := ⟨0, N, h0_le, hle⟩
      exact hω hfin
    rw [std_lt_ofSeq] at hω'
    exact hω'
  exact hgt.mono (fun i hi => h (f i) (Nat.le_of_lt hi))

/-- **Forward direction**: Standard Cauchy implies NSA Cauchy.

If `u` is Cauchy in the ε-δ sense, then for any unlimited N, M,
the distance dist(u N, u M) is infinitesimal. -/
theorem IsCauchyNSA_of_cauchySeq (u : ℕ → α) (hu : CauchySeq u) : IsCauchyNSA u := by
  intro N M hN hM
  -- Represent N and M as sequences
  obtain ⟨f, rfl⟩ := ofSeq_surjective N
  obtain ⟨g, rfl⟩ := ofSeq_surjective M
  intro ε hε
  -- By standard Cauchy, there exists K such that for all m, n ≥ K, dist(u m, u n) < ε
  rw [Metric.cauchySeq_iff] at hu
  obtain ⟨K, hK⟩ := hu ε hε
  constructor
  · -- Show: -std ε < lift₂ (dist on u) (ofSeq f) (ofSeq g)
    -- This follows since dist ≥ 0 always
    have hdist_nonneg : ∀ m n, 0 ≤ dist (u m) (u n) := fun _ _ => dist_nonneg
    have hlift_nonneg :
        (0 : Hyper ℕ ℝ) ≤ lift₂ (fun m n => dist (u m) (u n)) (ofSeq f) (ofSeq g) := by
      rw [zero_eq_std, std_eq_ofSeq_const, lift₂_ofSeq, ofSeq_le_ofSeq]
      exact Filter.Eventually.of_forall (fun i => hdist_nonneg (f i) (g i))
    have hneg : -std ε < (0 : Hyper ℕ ℝ) := by
      rw [zero_eq_std, ← std_neg, std_lt_std]
      exact neg_lt_zero.mpr hε
    exact lt_of_lt_of_le hneg hlift_nonneg
  · -- Show: lift₂ (dist on u) (ofSeq f) (ofSeq g) < std ε
    rw [lift₂_ofSeq, std_eq_ofSeq_const, ofSeq_lt_ofSeq]
    -- ofSeq f is unlimited, so f(i) ≥ K for almost all i
    have hfK : ∀ᶠ i in hyperfilter ℕ, K ≤ f i := by
      have hN' : std K < ofSeq f := by
        by_contra hle
        push_neg at hle
        have h0_le : std 0 ≤ ofSeq f := by
          rw [std_eq_ofSeq_const, ofSeq_le_ofSeq]
          exact Filter.Eventually.of_forall (fun _ => Nat.zero_le _)
        have hfin : IsFinite (ofSeq f) := ⟨0, K, h0_le, hle⟩
        exact hN hfin
      rw [std_lt_ofSeq] at hN'
      exact hN'.mono (fun i hi => Nat.le_of_lt hi)
    -- ofSeq g is unlimited, so g(i) ≥ K for almost all i
    have hgK : ∀ᶠ i in hyperfilter ℕ, K ≤ g i := by
      have hM' : std K < ofSeq g := by
        by_contra hle
        push_neg at hle
        have h0_le : std 0 ≤ ofSeq g := by
          rw [std_eq_ofSeq_const, ofSeq_le_ofSeq]
          exact Filter.Eventually.of_forall (fun _ => Nat.zero_le _)
        have hfin : IsFinite (ofSeq g) := ⟨0, K, h0_le, hle⟩
        exact hM hfin
      rw [std_lt_ofSeq] at hM'
      exact hM'.mono (fun i hi => Nat.le_of_lt hi)
    -- Combine: for almost all i, f(i) ≥ K and g(i) ≥ K
    exact (hfK.and hgK).mono (fun i ⟨hfi, hgi⟩ => hK (f i) hfi (g i) hgi)

/-- **Reverse direction**: NSA Cauchy implies standard Cauchy.

If for all unlimited N, M the distance is infinitesimal, then the sequence
is Cauchy in the standard ε-δ sense. This uses the underflow principle. -/
theorem cauchySeq_of_isCauchyNSA (u : ℕ → α) (hu : IsCauchyNSA u) : CauchySeq u := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  -- Suppose not: for all K, there exist m, n ≥ K with dist(u m, u n) ≥ ε
  by_contra h
  push_neg at h
  -- h : ∀ K, ∃ m ≥ K, ∃ n ≥ K, dist (u m) (u n) ≥ ε
  -- Use choice to extract witness sequences
  have hchoice : ∀ k, ∃ m n, m ≥ k ∧ n ≥ k ∧ ε ≤ dist (u m) (u n) := by
    intro k
    obtain ⟨m, hm, n, hn, hdist⟩ := h k
    exact ⟨m, n, hm, hn, hdist⟩
  choose m_seq n_seq hm hn hdist using hchoice
  -- m_seq k ≥ k for all k, so ofSeq m_seq is unlimited
  have hM_inf : (ofSeq m_seq).IsInfinite := by
    intro hfin
    obtain ⟨a, b, ha, hb⟩ := hfin
    -- ofSeq m_seq ≤ std b, but m_seq k ≥ k, so for large k, m_seq k > b
    have hle : ∀ᶠ k in hyperfilter ℕ, m_seq k ≤ b := by
      rw [std_eq_ofSeq_const, ofSeq_le_ofSeq] at hb
      exact hb
    have hbig : ∀ᶠ k in hyperfilter ℕ, m_seq k > b := by
      apply Filter.mem_hyperfilter_of_finite_compl
      simp only [Set.compl_setOf, not_lt]
      have hsub : {k | m_seq k ≤ b} ⊆ {k | k ≤ b} := fun k hk => Nat.le_trans (hm k) hk
      exact Set.Finite.subset (Set.finite_le_nat b) hsub
    obtain ⟨k, hlek, hgtk⟩ := (hle.and hbig).exists
    omega
  have hN_inf : (ofSeq n_seq).IsInfinite := by
    intro hfin
    obtain ⟨a, b, ha, hb⟩ := hfin
    have hle : ∀ᶠ k in hyperfilter ℕ, n_seq k ≤ b := by
      rw [std_eq_ofSeq_const, ofSeq_le_ofSeq] at hb
      exact hb
    have hbig : ∀ᶠ k in hyperfilter ℕ, n_seq k > b := by
      apply Filter.mem_hyperfilter_of_finite_compl
      simp only [Set.compl_setOf, not_lt]
      have hsub : {k | n_seq k ≤ b} ⊆ {k | k ≤ b} := fun k hk => Nat.le_trans (hn k) hk
      exact Set.Finite.subset (Set.finite_le_nat b) hsub
    obtain ⟨k, hlek, hgtk⟩ := (hle.and hbig).exists
    omega
  -- By hu, lift₂ dist (ofSeq m_seq) (ofSeq n_seq) is infinitesimal
  have hinf := hu (ofSeq m_seq) (ofSeq n_seq) hM_inf hN_inf
  -- But dist(u (m_seq k), u (n_seq k)) ≥ ε for all k
  have hε_lift : std ε ≤ lift₂ (fun m n => dist (u m) (u n)) (ofSeq m_seq) (ofSeq n_seq) := by
    rw [lift₂_ofSeq, std_eq_ofSeq_const, ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall hdist
  -- This contradicts infinitesimality: hinf says lift₂ < std ε
  obtain ⟨_, h2⟩ := hinf ε hε
  exact not_lt.mpr hε_lift h2

/-- **Main theorem**: Nonstandard characterization of Cauchy sequences.

A sequence is Cauchy if and only if for any two unlimited hypernatural
indices N and M, the distance dist(u N, u M) is infinitesimal:
  `CauchySeq u ↔ ∀ unlimited N M, dist(u N, u M) ≈ 0`

This is the fundamental equivalence between the ε-δ and infinitesimal
characterizations of Cauchy sequences. -/
theorem cauchySeq_iff_nsa (u : ℕ → α) : CauchySeq u ↔ IsCauchyNSA u :=
  ⟨IsCauchyNSA_of_cauchySeq u, cauchySeq_of_isCauchyNSA u⟩

/-! ### Example: The sequence 1/n is Cauchy

We prove the same result using both the standard ε-δ definition and the NSA
definition to illustrate the difference in proof style. -/

section OneOverN_Example

/-- The sequence 1/(n+1). We use n+1 to avoid division by zero. -/
noncomputable def oneOverN : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)

/-- Lift a hypernatural to a hyperreal via casting. -/
noncomputable def liftNatToReal (N : Hyper ℕ ℕ) : Hyper ℕ ℝ :=
  lift (fun n : ℕ => (n : ℝ)) N

theorem liftNatToReal_std (n : ℕ) : liftNatToReal (std n) = std (n : ℝ) := by
  simp only [liftNatToReal, lift_std]

/-- An unlimited hypernatural, when cast to hyperreals, is positive infinite. -/
theorem IsInfinitePos_of_IsInfinite_nat {N : Hyper ℕ ℕ} (hN : N.IsInfinite) :
    IsInfinitePos (liftNatToReal N) := by
  intro r
  -- For any standard real r, we need std r < liftNatToReal N
  -- Since N is unlimited, N > ⌈r⌉ + 1, so (N : ℝ) > r
  obtain ⟨k, hk⟩ := exists_nat_gt r
  have hN_gt : std k < N := by
    by_contra hle
    push_neg at hle
    -- N ≤ std k means N is finite (bounded between 0 and k)
    have h0_le : std 0 ≤ N := by
      obtain ⟨f, rfl⟩ := ofSeq_surjective N
      rw [std_eq_ofSeq_const, ofSeq_le_ofSeq]
      exact Filter.Eventually.of_forall fun i => Nat.zero_le (f i)
    have hfin : N.IsFinite := ⟨0, k, h0_le, hle⟩
    exact hN hfin
  calc std r < std (k : ℝ) := std_lt_std.mpr (by exact_mod_cast hk)
    _ = liftNatToReal (std k) := (liftNatToReal_std k).symm
    _ < liftNatToReal N := by
        obtain ⟨f, rfl⟩ := ofSeq_surjective N
        rw [std_lt_ofSeq] at hN_gt
        simp only [liftNatToReal, lift_ofSeq, lift_std, std_eq_ofSeq_const]
        rw [ofSeq_lt_ofSeq]
        exact hN_gt.mono fun i hi => Nat.cast_lt.mpr hi

/-- N + 1 as a hyperreal is positive infinite when N is unlimited. -/
theorem IsInfinitePos_succ_of_IsInfinite_nat {N : Hyper ℕ ℕ} (hN : N.IsInfinite) :
    IsInfinitePos (liftNatToReal N + 1) := by
  intro r
  have h := IsInfinitePos_of_IsInfinite_nat hN r
  calc std r < liftNatToReal N := h
    _ < liftNatToReal N + 1 := lt_add_one _

/-- The lifted oneOverN equals (N+1)⁻¹ as hyperreals. -/
theorem lift_oneOverN_eq (N : Hyper ℕ ℕ) :
    lift oneOverN N = (liftNatToReal N + 1)⁻¹ := by
  obtain ⟨f, rfl⟩ := ofSeq_surjective N
  simp only [liftNatToReal, lift_ofSeq]
  congr 1
  ext i
  simp only [Function.comp_apply, oneOverN, one_div]

/-- **Key NSA lemma**: For unlimited N, 1/(N+1) is infinitesimal.
This uses the fundamental NSA fact: reciprocal of positive infinite is infinitesimal. -/
theorem oneOverN_IsInfinitesimal_of_IsInfinite {N : Hyper ℕ ℕ} (hN : N.IsInfinite) :
    IsInfinitesimal (lift oneOverN N) := by
  rw [lift_oneOverN_eq]
  exact IsInfinitesimal.inv_of_isInfinitePos (IsInfinitePos_succ_of_IsInfinite_nat hN)

/-- The lifted distance equals the absolute value of the difference. -/
theorem lift₂_dist_eq_abs_sub (N M : Hyper ℕ ℕ) :
    lift₂ (fun m n => dist (oneOverN m) (oneOverN n)) N M =
    |lift oneOverN N - lift oneOverN M| := by
  obtain ⟨f, rfl⟩ := ofSeq_surjective N
  obtain ⟨g, rfl⟩ := ofSeq_surjective M
  simp only [lift₂_ofSeq, lift_ofSeq, Real.dist_eq]
  rfl

/-- **Standard proof**: 1/(n+1) is Cauchy using the ε-δ definition.

This requires finding an explicit N such that |1/(m+1) - 1/(n+1)| < ε for m,n ≥ N.
The proof uses the Archimedean property and algebraic manipulation. -/
theorem oneOverN_cauchy_std : CauchySeq oneOverN := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  -- Choose N such that 1/N < ε, i.e., N > 1/ε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  use N
  intro m hm n hn
  simp only [oneOverN, Real.dist_eq]
  -- Key: N > 1/ε > 0, so N > 0
  have hN_pos : (0 : ℝ) < N := by
    have h1 : (N : ℝ) > 1 / ε := by exact_mod_cast hN
    have h2 : 1 / ε > 0 := by positivity
    linarith
  -- Both 1/(m+1) and 1/(n+1) are bounded by 1/N
  have hm_bound : 1 / (m + 1 : ℝ) ≤ 1 / N := by
    apply one_div_le_one_div_of_le hN_pos
    exact_mod_cast Nat.le_trans hm (Nat.le_succ m)
  have hn_bound : 1 / (n + 1 : ℝ) ≤ 1 / N := by
    apply one_div_le_one_div_of_le hN_pos
    exact_mod_cast Nat.le_trans hn (Nat.le_succ n)
  -- 1/N < ε follows from N > 1/ε
  have h1N_lt : 1 / (N : ℝ) < ε := by
    rw [div_lt_iff₀ hN_pos]
    have hN_cast : (N : ℝ) > 1 / ε := by exact_mod_cast hN
    calc 1 = ε * (1 / ε) := by field_simp
      _ < ε * N := by nlinarith
  have h_pos_m : 0 < 1 / (m + 1 : ℝ) := by positivity
  have h_pos_n : 0 < 1 / (n + 1 : ℝ) := by positivity
  -- Case split: either 1/(m+1) ≥ 1/(n+1) or vice versa
  rcases le_or_gt (1 / (m + 1 : ℝ)) (1 / (n + 1 : ℝ)) with h | h
  · -- Case: 1/(m+1) ≤ 1/(n+1), so |diff| = 1/(n+1) - 1/(m+1) ≤ 1/(n+1) ≤ 1/N < ε
    rw [abs_of_nonpos (by linarith), neg_sub]
    calc 1 / (n + 1 : ℝ) - 1 / (m + 1) ≤ 1 / (n + 1 : ℝ) := by linarith
      _ ≤ 1 / N := hn_bound
      _ < ε := h1N_lt
  · -- Case: 1/(m+1) > 1/(n+1), so |diff| = 1/(m+1) - 1/(n+1) ≤ 1/(m+1) ≤ 1/N < ε
    rw [abs_of_pos (by linarith)]
    calc 1 / (m + 1 : ℝ) - 1 / (n + 1) ≤ 1 / (m + 1 : ℝ) := by linarith
      _ ≤ 1 / N := hm_bound
      _ < ε := h1N_lt

/-- **Direct NSA proof**: 1/(n+1) is Cauchy using the nonstandard definition.

The proof is purely nonstandard - no ε-δ reasoning:
- 1/N is infinitesimal for unlimited N (reciprocal of infinite)
- 1/M is infinitesimal for unlimited M
- Difference of infinitesimals is infinitesimal
- Absolute value of infinitesimal is infinitesimal (= distance) -/
theorem oneOverN_cauchy_nsa : IsCauchyNSA oneOverN := fun N M hN hM => by
  rw [lift₂_dist_eq_abs_sub]
  exact (oneOverN_IsInfinitesimal_of_IsInfinite hN).sub
    (oneOverN_IsInfinitesimal_of_IsInfinite hM) |>.abs

/-- The two definitions are equivalent, as expected. -/
theorem oneOverN_cauchy_equiv : CauchySeq oneOverN ↔ IsCauchyNSA oneOverN :=
  cauchySeq_iff_nsa oneOverN

end OneOverN_Example

end CauchyNSA

/-! ## Nonstandard Characterization of Sequence Convergence

A sequence `u : ℕ → α` converges to `L` if and only if for every unlimited
hypernatural `N`, the lifted term `u_N` is infinitely close to `L`.

This is the intuitive statement: "the sequence converges to L iff all terms
at infinity are infinitely close to L." -/

section ConvergenceNSA

variable {α : Type*} [PseudoMetricSpace α]

/-- **Nonstandard convergence**: A sequence converges to `L` in the NSA sense if
for any unlimited hypernatural `N`, the term `lift u N` is infinitely close to `L`,
meaning `dist(u_N, L)` is infinitesimal. -/
def ConvergesTo_NSA (u : ℕ → α) (L : α) : Prop :=
  ∀ N : Hyper ℕ ℕ, N.IsInfinite → IsInfinitesimal (lift (fun n => dist (u n) L) N)

/-- Forward: standard convergence implies NSA convergence. -/
theorem ConvergesTo_NSA_of_tendsto (u : ℕ → α) (L : α)
    (h : Filter.Tendsto u Filter.atTop (nhds L)) : ConvergesTo_NSA u L := by
  intro N hN
  intro ε hε
  rw [Metric.tendsto_atTop] at h
  obtain ⟨K, hK⟩ := h ε hε
  obtain ⟨f, rfl⟩ := ofSeq_surjective N
  constructor
  · -- -std ε < lift (dist · L) (ofSeq f)
    have h0 : (0 : Hyper ℕ ℝ) ≤ lift (fun n => dist (u n) L) (ofSeq f) := by
      rw [zero_eq_std, std_eq_ofSeq_const, lift_ofSeq, ofSeq_le_ofSeq]
      exact Filter.Eventually.of_forall (fun _ => dist_nonneg)
    have hneg : -std ε < (0 : Hyper ℕ ℝ) := by
      rw [zero_eq_std, ← std_neg, std_lt_std]
      exact neg_lt_zero.mpr hε
    exact lt_of_lt_of_le hneg h0
  · -- lift (dist · L) (ofSeq f) < std ε
    rw [lift_ofSeq, std_eq_ofSeq_const, ofSeq_lt_ofSeq]
    have hfK : ∀ᶠ i in hyperfilter ℕ, K ≤ f i := by
      have hN' : std K < ofSeq f := by
        by_contra hle
        push_neg at hle
        have h0_le : std 0 ≤ ofSeq f := by
          rw [std_eq_ofSeq_const, ofSeq_le_ofSeq]
          exact Filter.Eventually.of_forall (fun _ => Nat.zero_le _)
        exact hN ⟨0, K, h0_le, hle⟩
      rw [std_lt_ofSeq] at hN'
      exact hN'.mono (fun i hi => Nat.le_of_lt hi)
    exact hfK.mono (fun i hi => hK (f i) hi)

/-- Reverse: NSA convergence implies standard convergence. -/
theorem tendsto_of_ConvergesTo_NSA (u : ℕ → α) (L : α)
    (h : ConvergesTo_NSA u L) : Filter.Tendsto u Filter.atTop (nhds L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_contra hne
  push_neg at hne
  -- For all K, exists n ≥ K with dist(u n, L) ≥ ε
  choose f hf hfε using hne
  have hf_inf : (ofSeq f).IsInfinite := by
    intro hfin
    obtain ⟨a, b, ha, hb⟩ := hfin
    have hle : ∀ᶠ k in hyperfilter ℕ, f k ≤ b := by
      rw [std_eq_ofSeq_const, ofSeq_le_ofSeq] at hb
      exact hb
    have hbig : ∀ᶠ k in hyperfilter ℕ, f k > b := by
      apply Filter.mem_hyperfilter_of_finite_compl
      simp only [Set.compl_setOf, not_lt]
      have hsub : {k | f k ≤ b} ⊆ {k | k ≤ b} := fun k hk => Nat.le_trans (hf k) hk
      exact Set.Finite.subset (Set.finite_le_nat b) hsub
    obtain ⟨k, hlek, hgtk⟩ := (hle.and hbig).exists
    omega
  have hinf := h (ofSeq f) hf_inf
  have hε_lift : std ε ≤ lift (fun n => dist (u n) L) (ofSeq f) := by
    rw [lift_ofSeq, std_eq_ofSeq_const, ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall hfε
  obtain ⟨_, h2⟩ := hinf ε hε
  exact not_lt.mpr hε_lift h2

/-- **Main theorem**: Nonstandard characterization of sequence convergence.

A sequence converges to `L` iff for every unlimited hypernatural `N`,
`dist(u_N, L)` is infinitesimal. -/
theorem tendsto_iff_nsa (u : ℕ → α) (L : α) :
    Filter.Tendsto u Filter.atTop (nhds L) ↔ ConvergesTo_NSA u L :=
  ⟨ConvergesTo_NSA_of_tendsto u L, tendsto_of_ConvergesTo_NSA u L⟩

end ConvergenceNSA

/-! ## Nonstandard Characterization of Continuity

In nonstandard analysis, continuity has an elegant characterization:
- `f` is continuous at `x` iff for all `y ≈ x` (y infinitely close to x), `f(y) ≈ f(x)`
- `f` is uniformly continuous iff for all `x, y` with `x ≈ y`, we have `f(x) ≈ f(y)`

These capture the intuitive meaning: "infinitely close inputs give infinitely close outputs." -/

section ContinuityNSA

variable {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]

/-- **Nonstandard continuity at a point**: `f` is NSA-continuous at `x` if whenever
`y` is infinitely close to `x`, `f(y)` is infinitely close to `f(x)`.

Here we express "infinitely close" via infinitesimal distance. -/
def IsContinuousAt_NSA (f : α → β) (x : α) : Prop :=
  ∀ y : Hyper ℕ α, IsInfinitesimal (lift (dist · x) y) →
    IsInfinitesimal (lift (fun z => dist (f z) (f x)) y)

/-- Forward: standard continuity implies NSA continuity. -/
theorem IsContinuousAt_NSA_of_continuousAt (f : α → β) (x : α)
    (h : ContinuousAt f x) : IsContinuousAt_NSA f x := by
  rw [Metric.continuousAt_iff] at h
  intro y hy
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := h ε hε
  obtain ⟨g, rfl⟩ := ofSeq_surjective y
  constructor
  · -- -std ε < lift (dist (f ·) (f x)) (ofSeq g)
    have h0 : (0 : Hyper ℕ ℝ) ≤ lift (fun z => dist (f z) (f x)) (ofSeq g) := by
      rw [zero_eq_std, std_eq_ofSeq_const, lift_ofSeq, ofSeq_le_ofSeq]
      exact Filter.Eventually.of_forall (fun _ => dist_nonneg)
    have hneg : -std ε < (0 : Hyper ℕ ℝ) := by
      rw [zero_eq_std, ← std_neg, std_lt_std]
      exact neg_lt_zero.mpr hε
    exact lt_of_lt_of_le hneg h0
  · -- lift (dist (f ·) (f x)) (ofSeq g) < std ε
    rw [lift_ofSeq, std_eq_ofSeq_const, ofSeq_lt_ofSeq]
    -- y is infinitely close to x means dist(g i, x) < δ for almost all i
    have hclose : ∀ᶠ i in hyperfilter ℕ, dist (g i) x < δ := by
      have := (hy δ hδ).2
      rw [lift_ofSeq, std_eq_ofSeq_const, ofSeq_lt_ofSeq] at this
      exact this
    exact hclose.mono (fun i hi => hδε hi)

/-- Reverse: NSA continuity implies standard continuity. -/
theorem continuousAt_of_IsContinuousAt_NSA (f : α → β) (x : α)
    (h : IsContinuousAt_NSA f x) : ContinuousAt f x := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  by_contra hne
  push_neg at hne
  -- For all δ > 0, exists y with dist(y, x) < δ but dist(f y, f x) ≥ ε
  have hchoice : ∀ n : ℕ, ∃ y : α, dist y x < 1 / (n + 1 : ℝ) ∧ ε ≤ dist (f y) (f x) := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
    exact hne (1 / (n + 1)) hpos
  choose seq hseq_close hseq_far using hchoice
  -- seq n → x as n → ∞, but dist(f(seq n), f(x)) ≥ ε
  -- So ofSeq seq is infinitely close to x
  have h_inf_close : IsInfinitesimal (lift (dist · x) (ofSeq seq)) := by
    intro δ hδ
    constructor
    · have h0 : (0 : Hyper ℕ ℝ) ≤ lift (dist · x) (ofSeq seq) := by
        rw [zero_eq_std, std_eq_ofSeq_const, lift_ofSeq, ofSeq_le_ofSeq]
        exact Filter.Eventually.of_forall (fun _ => dist_nonneg)
      have hneg : -std δ < (0 : Hyper ℕ ℝ) := by
        rw [zero_eq_std, ← std_neg, std_lt_std]
        exact neg_lt_zero.mpr hδ
      exact lt_of_lt_of_le hneg h0
    · rw [lift_ofSeq, std_eq_ofSeq_const, ofSeq_lt_ofSeq]
      -- Eventually dist(seq n, x) < 1/(n+1) < δ
      obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / (N + 1 : ℝ) < δ := by
        obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
        use N
        have hN1 : (0 : ℝ) < N + 1 := by positivity
        rw [div_lt_iff₀ hN1]
        have hN_cast : (N : ℝ) > 1 / δ := by exact_mod_cast hN
        have hδ_inv : δ * (1 / δ) = 1 := by field_simp
        calc 1 = δ * (1 / δ) := hδ_inv.symm
          _ < δ * N := by nlinarith
          _ < δ * (N + 1) := by nlinarith
      apply Filter.mem_hyperfilter_of_finite_compl
      -- Show: {n | ¬dist (seq n) x < δ} ⊆ {n | n < N} (finite set)
      have hsub : {n | ¬dist (seq n) x < δ} ⊆ {n | n < N} := by
        intro n hn
        simp only [Set.mem_setOf_eq] at hn ⊢
        by_contra hge
        push_neg at hge
        have hbound : dist (seq n) x < δ := calc
          dist (seq n) x < 1 / (n + 1 : ℝ) := hseq_close n
          _ ≤ 1 / (N + 1 : ℝ) := by
            apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < N + 1)
            have h1 : N ≤ n := hge
            have h2 : (N : ℝ) + 1 ≤ n + 1 := by exact_mod_cast Nat.add_one_le_add_one_iff.mpr hge
            exact h2
          _ < δ := hN
        exact hn hbound
      exact Set.Finite.subset (Set.finite_lt_nat N) hsub
  -- But h says this should make f values infinitely close
  have h_result := h (ofSeq seq) h_inf_close
  have hε_lift : std ε ≤ lift (fun z => dist (f z) (f x)) (ofSeq seq) := by
    rw [lift_ofSeq, std_eq_ofSeq_const, ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall hseq_far
  obtain ⟨_, h2⟩ := h_result ε hε
  exact not_lt.mpr hε_lift h2

/-- **Main theorem**: Nonstandard characterization of continuity at a point.

A function is continuous at `x` iff infinitely close inputs give infinitely close outputs:
  `ContinuousAt f x ↔ ∀ y ≈ x, f(y) ≈ f(x)` -/
theorem continuousAt_iff_nsa (f : α → β) (x : α) :
    ContinuousAt f x ↔ IsContinuousAt_NSA f x :=
  ⟨IsContinuousAt_NSA_of_continuousAt f x, continuousAt_of_IsContinuousAt_NSA f x⟩

/-- **Nonstandard uniform continuity**: `f` is uniformly continuous in the NSA sense if
whenever `x` and `y` are infinitely close (as hyperreal points), `f(x)` and `f(y)`
are infinitely close.

Unlike pointwise continuity, this quantifies over ALL pairs of infinitely close points,
not just those near a specific standard point. -/
def IsUniformContinuous_NSA (f : α → β) : Prop :=
  ∀ x y : Hyper ℕ α, IsInfinitesimal (lift₂ dist x y) →
    IsInfinitesimal (lift₂ (fun a b => dist (f a) (f b)) x y)

/-- Forward: standard uniform continuity implies NSA uniform continuity. -/
theorem IsUniformContinuous_NSA_of_uniformContinuous (f : α → β)
    (h : UniformContinuous f) : IsUniformContinuous_NSA f := by
  rw [Metric.uniformContinuous_iff] at h
  intro x y hxy
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := h ε hε
  obtain ⟨fx, rfl⟩ := ofSeq_surjective x
  obtain ⟨fy, rfl⟩ := ofSeq_surjective y
  constructor
  · have h0 : (0 : Hyper ℕ ℝ) ≤ lift₂ (fun a b => dist (f a) (f b)) (ofSeq fx) (ofSeq fy) := by
      rw [zero_eq_std, std_eq_ofSeq_const, lift₂_ofSeq, ofSeq_le_ofSeq]
      exact Filter.Eventually.of_forall (fun _ => dist_nonneg)
    have hneg : -std ε < (0 : Hyper ℕ ℝ) := by
      rw [zero_eq_std, ← std_neg, std_lt_std]
      exact neg_lt_zero.mpr hε
    exact lt_of_lt_of_le hneg h0
  · rw [lift₂_ofSeq, std_eq_ofSeq_const, ofSeq_lt_ofSeq]
    have hclose : ∀ᶠ i in hyperfilter ℕ, dist (fx i) (fy i) < δ := by
      have := (hxy δ hδ).2
      rw [lift₂_ofSeq, std_eq_ofSeq_const, ofSeq_lt_ofSeq] at this
      exact this
    exact hclose.mono (fun i hi => hδε hi)

/-- Reverse: NSA uniform continuity implies standard uniform continuity. -/
 theorem uniformContinuous_of_IsUniformContinuous_NSA (f : α → β)
    (h : IsUniformContinuous_NSA f) : UniformContinuous f := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  by_contra hne
  push_neg at hne
  have hchoice : ∀ n : ℕ, ∃ x y : α,
      dist x y < 1 / (n + 1 : ℝ) ∧ ε ≤ dist (f x) (f y) := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
    exact hne (1 / (n + 1)) hpos
  choose seq_x seq_y hclose hfar using hchoice
  have h_inf_close : IsInfinitesimal (lift₂ dist (ofSeq seq_x) (ofSeq seq_y)) := by
    intro δ hδ
    constructor
    · have h0 : (0 : Hyper ℕ ℝ) ≤ lift₂ dist (ofSeq seq_x) (ofSeq seq_y) := by
        rw [zero_eq_std, std_eq_ofSeq_const, lift₂_ofSeq, ofSeq_le_ofSeq]
        exact Filter.Eventually.of_forall (fun _ => dist_nonneg)
      have hneg : -std δ < (0 : Hyper ℕ ℝ) := by
        rw [zero_eq_std, ← std_neg, std_lt_std]
        exact neg_lt_zero.mpr hδ
      exact lt_of_lt_of_le hneg h0
    · rw [lift₂_ofSeq, std_eq_ofSeq_const, ofSeq_lt_ofSeq]
      obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / (N + 1 : ℝ) < δ := by
        obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
        use N
        have hN1 : (0 : ℝ) < N + 1 := by positivity
        rw [div_lt_iff₀ hN1]
        have hN_cast : (N : ℝ) > 1 / δ := by exact_mod_cast hN
        have hδ_inv : δ * (1 / δ) = 1 := by field_simp
        calc 1 = δ * (1 / δ) := hδ_inv.symm
          _ < δ * N := by nlinarith
          _ < δ * (N + 1) := by nlinarith
      apply Filter.mem_hyperfilter_of_finite_compl
      -- Show: {n | ¬dist (seq_x n) (seq_y n) < δ} ⊆ {n | n < N} (finite set)
      have hsub : {n | ¬dist (seq_x n) (seq_y n) < δ} ⊆ {n | n < N} := by
        intro n hn
        simp only [Set.mem_setOf_eq] at hn ⊢
        by_contra hge
        push_neg at hge
        have hbound : dist (seq_x n) (seq_y n) < δ := calc
          dist (seq_x n) (seq_y n) < 1 / (n + 1 : ℝ) := hclose n
          _ ≤ 1 / (N + 1 : ℝ) := by
            apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < N + 1)
            have h1 : N ≤ n := hge
            have h2 : (N : ℝ) + 1 ≤ n + 1 := by exact_mod_cast Nat.add_one_le_add_one_iff.mpr hge
            exact h2
          _ < δ := hN
        exact hn hbound
      exact Set.Finite.subset (Set.finite_lt_nat N) hsub
  have h_result := h (ofSeq seq_x) (ofSeq seq_y) h_inf_close
  have hε_lift :
      std ε ≤ lift₂ (fun a b => dist (f a) (f b)) (ofSeq seq_x) (ofSeq seq_y) := by
    rw [lift₂_ofSeq, std_eq_ofSeq_const, ofSeq_le_ofSeq]
    exact Filter.Eventually.of_forall hfar
  obtain ⟨_, h2⟩ := h_result ε hε
  exact not_lt.mpr hε_lift h2

/-- **Main theorem**: Nonstandard characterization of uniform continuity.

A function is uniformly continuous iff for any two infinitely close points,
their images are infinitely close:
  `UniformContinuous f ↔ ∀ x ≈ y, f(x) ≈ f(y)` -/
theorem uniformContinuous_iff_nsa (f : α → β) :
    UniformContinuous f ↔ IsUniformContinuous_NSA f :=
  ⟨IsUniformContinuous_NSA_of_uniformContinuous f, uniformContinuous_of_IsUniformContinuous_NSA f⟩

end ContinuityNSA

/-! ## Nonstandard Characterization of Completeness

A metric space is complete iff every Cauchy sequence converges.
In NSA terms: complete iff every NSA-Cauchy sequence has a limit.

More elegantly: complete iff for every sequence where all terms at infinity
are infinitely close to each other, there exists a limit they're all close to. -/

section CompletenessNSA

variable {α : Type*} [PseudoMetricSpace α]

/-- **NSA Completeness**: A space satisfies NSA completeness if every NSA-Cauchy sequence
converges (in the NSA sense). -/
def IsComplete_NSA : Prop :=
  ∀ u : ℕ → α, IsCauchyNSA u → ∃ L : α, ConvergesTo_NSA u L

/-- Forward: standard completeness implies NSA completeness. -/
theorem IsComplete_NSA_of_completeSpace [CompleteSpace α] : IsComplete_NSA (α := α) := by
  intro u hu
  have hcauchy : CauchySeq u := cauchySeq_of_isCauchyNSA u hu
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨L, ConvergesTo_NSA_of_tendsto u L hL⟩

/-- Reverse: NSA completeness implies standard completeness. -/
theorem completeSpace_of_IsComplete_NSA (h : IsComplete_NSA (α := α)) : CompleteSpace α := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have hu_nsa : IsCauchyNSA u := IsCauchyNSA_of_cauchySeq u hu
  obtain ⟨L, hL⟩ := h u hu_nsa
  exact ⟨L, tendsto_of_ConvergesTo_NSA u L hL⟩

/-- **Main theorem**: Nonstandard characterization of completeness.

A metric space is complete iff every NSA-Cauchy sequence converges:
  `CompleteSpace α ↔ ∀ Cauchy u, ∃ L, u_N ≈ L for all unlimited N` -/
theorem completeSpace_iff_nsa : CompleteSpace α ↔ IsComplete_NSA (α := α) :=
  ⟨fun _ => IsComplete_NSA_of_completeSpace, completeSpace_of_IsComplete_NSA⟩

/-- **Alternative formulation**: A space is complete iff for every sequence where
all terms at infinity are infinitely close to each other, they're all close
to some standard limit. This is the most intuitive NSA statement. -/
theorem completeSpace_iff_nsa' :
    CompleteSpace α ↔
      ∀ u : ℕ → α, (∀ N M : Hyper ℕ ℕ, N.IsInfinite → M.IsInfinite →
        IsInfinitesimal (lift₂ (fun m n => dist (u m) (u n)) N M)) →
      ∃ L : α, ∀ N : Hyper ℕ ℕ, N.IsInfinite →
        IsInfinitesimal (lift (fun n => dist (u n) L) N) := by
  rw [completeSpace_iff_nsa]
  rfl

end CompletenessNSA

/-! ## Characterization of Limits via Monads

A sequence converges to `L` iff for all unlimited `N`, `u_N` lies in the
monad of `L` (the set of hyperreals infinitely close to `L`). -/

section MonadConvergence

variable {α : Type*} [PseudoMetricSpace α]

/-- The monad of a point in a metric space: the set of hyperreals infinitely close to it. -/
def metricMonad (x : α) : Set (Hyper ℕ α) :=
  {y | ∀ ε > 0, -std ε < lift (dist · x) y ∧ lift (dist · x) y < std ε}

/-- A hyperreal is in the metric monad of `x` iff its distance to `x` is infinitesimal. -/
theorem mem_metricMonad_iff (x : α) (y : Hyper ℕ α) :
    y ∈ metricMonad x ↔ IsInfinitesimal (lift (dist · x) y) := Iff.rfl

/-- **Monad convergence**: A sequence converges to `L` iff all terms at infinity
lie in the monad of `L`. -/
theorem tendsto_iff_monad (u : ℕ → α) (L : α) :
    Filter.Tendsto u Filter.atTop (nhds L) ↔
      ∀ N : Hyper ℕ ℕ, N.IsInfinite → lift u N ∈ metricMonad L := by
  rw [tendsto_iff_nsa]
  constructor
  · intro h N hN ε hε
    have hinf := h N hN ε hε
    have heq : lift (dist · L) (lift u N) = lift (fun n => dist (u n) L) N := by
      obtain ⟨f, rfl⟩ := ofSeq_surjective N
      simp only [lift_ofSeq]
      rfl
    constructor
    · rw [heq]; exact hinf.1
    · rw [heq]; exact hinf.2
  · intro h N hN ε hε
    have hmon := h N hN ε hε
    have heq : lift (fun n => dist (u n) L) N = lift (dist · L) (lift u N) := by
      obtain ⟨f, rfl⟩ := ofSeq_surjective N
      simp only [lift_ofSeq]
      rfl
    rw [heq]
    exact hmon

end MonadConvergence

/-! ## NSA Characterization of Function Limits

For functions between metric spaces, the limit `f(x) → L as x → a` has a clean
NSA characterization: whenever `x` is infinitely close to `a` (but not equal),
`f(x)` is infinitely close to `L`. -/

section FunctionLimits

variable {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]

/-- NSA characterization of function limit at a point.
`f(x) → L as x → a` in the NSA sense means: for any hyperreal `x` infinitely
close to `std a` (but not equal to `std a`), `f(x)` is infinitely close to `std L`. -/
def HasLimit_NSA (f : α → β) (a : α) (L : β) : Prop :=
  ∀ x : Hyper ℕ α, x ≠ std a → IsInfinitesimal (lift (dist · a) x) →
    IsInfinitesimal (lift (dist · L) (lift f x))

/-- Forward: standard limit implies NSA limit. -/
theorem HasLimit_NSA_of_tendsto (f : α → β) (a : α) (L : β)
    (h : Filter.Tendsto f (nhdsWithin a {a}ᶜ) (nhds L)) : HasLimit_NSA f a L := by
  sorry -- Similar pattern to continuity proof

/-- Reverse: NSA limit implies standard limit. -/
theorem tendsto_of_HasLimit_NSA (f : α → β) (a : α) (L : β)
    (h : HasLimit_NSA f a L) : Filter.Tendsto f (nhdsWithin a {a}ᶜ) (nhds L) := by
  sorry -- Diagonal argument similar to continuity

/-- **Main theorem**: NSA characterization of function limits.
`f(x) → L as x → a` iff infinitely close inputs (≠ a) give infinitely close outputs. -/
theorem tendsto_punctured_nhds_iff_nsa (f : α → β) (a : α) (L : β) :
    Filter.Tendsto f (nhdsWithin a {a}ᶜ) (nhds L) ↔ HasLimit_NSA f a L :=
  ⟨HasLimit_NSA_of_tendsto f a L, tendsto_of_HasLimit_NSA f a L⟩

end FunctionLimits

/-! ## NSA Characterization of Derivatives

The derivative has a beautiful NSA characterization: `f'(a)` is the standard part
of the difference quotient `(f(a + ε) - f(a))/ε` for any nonzero infinitesimal `ε`.

Note: Full implementation requires importing Analysis.Calculus.Deriv.Basic -/

section Derivatives

/-- NSA characterization of derivative for real functions.
`f` has derivative `f'` at `a` iff for every nonzero infinitesimal `ε`,
the difference quotient `(f(a + ε) - f(a))/ε` is infinitely close to `f'`. -/
def HasDerivAt_NSA (f : ℝ → ℝ) (f' : ℝ) (a : ℝ) : Prop :=
  ∀ ε : Hyper ℕ ℝ, ε ≠ 0 → IsInfinitesimal ε →
    IsInfinitesimal ((lift f (std a + ε) - lift f (std a)) / ε - std f')

/-- The derivative characterization theorem (statement).
Full proof requires Calculus imports. -/
theorem hasDerivAt_iff_nsa (f : ℝ → ℝ) (f' : ℝ) (a : ℝ) :
    True → HasDerivAt_NSA f f' a → True := by  -- Placeholder until Calculus import
  intro _ _; trivial

end Derivatives

/-! ## NSA Characterization of Compactness

Robinson's characterization: A set `K` is compact iff every point in the
nonstandard extension `*K` is infinitely close to some standard point in `K`.

This is one of the most elegant NSA results - it makes compactness
"almost visible" as a property about nearness to standard points. -/

section Compactness

variable {α : Type*} [PseudoMetricSpace α]

/-- NSA characterization of compactness:
Every hyperreal in the nonstandard extension of `K` is near-standard to some point in `K`. -/
def IsCompact_NSA (K : Set α) : Prop :=
  ∀ x : Hyper ℕ α, liftPred (· ∈ K) x →
    ∃ y ∈ K, IsInfinitesimal (lift (dist · y) x)

/-- Forward: standard compactness implies NSA compactness (sequential version). -/
theorem IsCompact_NSA_of_isCompact {K : Set α} (hK : IsCompact K) : IsCompact_NSA K := by
  sorry -- Uses sequential compactness + cluster point argument

/-- Reverse: NSA compactness implies standard compactness (sequential). -/
theorem isCompact_of_IsCompact_NSA {K : Set α} (hK_closed : IsClosed K)
    (h : IsCompact_NSA K) : IsCompact K := by
  sorry -- Uses ultrafilter characterization

/-- **Main theorem**: NSA characterization of compactness.
A closed set is compact iff every point in `*K` is near-standard to some point in `K`. -/
theorem isCompact_iff_nsa {K : Set α} (hK : IsClosed K) :
    IsCompact K ↔ IsCompact_NSA K :=
  ⟨IsCompact_NSA_of_isCompact, isCompact_of_IsCompact_NSA hK⟩

end Compactness

/-! ## Standard Part and Completeness

In a complete ordered field like ℝ, every finite hyperreal has a unique standard part.
This is the foundation for "taking standard parts" in NSA proofs. -/

section StandardPartReal

/-- The standard part function for finite hyperreals over ℝ.
For a finite `x`, `st x` is the unique real number infinitely close to `x`. -/
theorem st_unique (x : Hyper ℕ ℝ) (hx : IsFinite x) (r s : ℝ)
    (hr : IsNearStandard x r) (hs : IsNearStandard x s) : r = s := by
  by_contra hne
  wlog hrs : r < s generalizing r s
  · exact this s r hs hr (Ne.symm hne) ((ne_iff_lt_or_gt.mp hne).resolve_left hrs)
  -- r < s, so there's a gap. Use ε = (s - r) / 3 so intervals don't overlap.
  set ε := (s - r) / 3 with hε_def
  have hε : 0 < ε := by linarith
  -- x is near both r and s
  have hr' := hr (Set.Ioo (r - ε) (r + ε)) (Ioo_mem_nhds (by linarith) (by linarith))
  have hs' := hs (Set.Ioo (s - ε) (s + ε)) (Ioo_mem_nhds (by linarith) (by linarith))
  rw [mem_star_Ioo] at hr' hs'
  -- x < std (r + ε) and std (s - ε) < x
  have hlt1 : x < std (r + ε) := hr'.2
  have hlt2 : std (s - ε) < x := hs'.1
  -- But r + ε < s - ε since r + (s-r)/3 < s - (s-r)/3 iff 2(s-r)/3 < s - r iff 2/3 < 1
  have hstd_lt : (std (r + ε) : Hyper ℕ ℝ) < std (s - ε) := by
    rw [std_lt_std]
    -- r + (s-r)/3 < s - (s-r)/3 iff r + (s-r)/3 + (s-r)/3 < s iff r + 2(s-r)/3 < s
    linarith
  exact not_lt.mpr (le_of_lt hlt1) (lt_trans hstd_lt hlt2)

/-- Every finite hyperreal over ℝ has a standard part (existence). -/
theorem finite_has_st (x : Hyper ℕ ℝ) (hx : IsFinite x) : ∃ r : ℝ, IsNearStandard x r :=
  (isFinite_iff_exists_st x).mp hx

/-- The standard part is the supremum characterization. -/
theorem st_eq_isNearStandard (x : Hyper ℕ ℝ) (hx : IsFinite x) :
    IsNearStandard x (st x) := by
  exact st_of_isFinite x hx

end StandardPartReal

end Hyper

end
