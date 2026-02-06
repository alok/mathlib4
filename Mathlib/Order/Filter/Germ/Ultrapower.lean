/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
module

public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.FilterProduct

/-!
# Ultrapower (Ultrafilter-Generic)

This file defines the ultrafilter-generic ultrapower as a specialization of `Filter.Germ`.
It provides a small, neutral API that can later be used to decouple NSA from a specific
ultrafilter choice (such as `nonstandardUltrafilter`).

See `Mathlib/Order/Filter/Germ/Ultrapower/Curry.lean` for the one-level equivalence between
iterated ultrapowers and germs over the curried filter.
-/

@[expose] public section

namespace Filter

/-- The ultrafilter-generic ultrapower of `alpha` indexed by `iota`. -/
abbrev Ultrapower {iota : Type*} (U : Ultrafilter iota) (alpha : Type*) : Type _ :=
  Germ (U : Filter iota) alpha

namespace Ultrapower

variable {iota : Type*} {U : Ultrafilter iota}
variable {alpha beta gamma : Type*}

/-- Constant embedding into an ultrapower. -/
noncomputable def ultraConst (a : alpha) : Ultrapower U alpha :=
  Germ.const a

/-- Coercion from the base type to its ultrapower via `ultraConst`. -/
noncomputable instance : Coe alpha (Ultrapower U alpha) where
  coe := ultraConst

/-- Standard (constant) embedding into an ultrapower. -/
noncomputable abbrev std : alpha → Ultrapower U alpha := ultraConst

/-- Construct an ultrapower element from a sequence. -/
def ofSeq (f : iota → alpha) : Ultrapower U alpha := Germ.ofFun f

theorem ofSeq_surjective : Function.Surjective (fun f : iota → alpha => ofSeq (U := U) f) := by
  intro x
  exact Quot.exists_rep x

theorem ofSeq_eq_ofSeq {f g : iota → alpha} :
    ofSeq (U := U) f = ofSeq (U := U) g ↔ ∀ᶠ i in (U : Filter iota), f i = g i := by
  change (f : Germ (U : Filter iota) alpha) = g ↔ f =ᶠ[(U : Filter iota)] g
  exact Germ.coe_eq

theorem ofSeq_le_ofSeq [LE alpha] {f g : iota → alpha} :
    ofSeq (U := U) f ≤ ofSeq (U := U) g ↔ ∀ᶠ i in (U : Filter iota), f i ≤ g i := by
  change (f : Germ (U : Filter iota) alpha) ≤ g ↔ f ≤ᶠ[(U : Filter iota)] g
  exact Germ.coe_le

theorem ofSeq_lt_ofSeq [Preorder alpha] {f g : iota → alpha} :
    ofSeq (U := U) f < ofSeq (U := U) g ↔ ∀ᶠ i in (U : Filter iota), f i < g i := by
  change (f : Germ (U : Filter iota) alpha) < g ↔ ∀ᶠ i in (U : Filter iota), f i < g i
  exact Germ.coe_lt (φ := U)

@[elab_as_elim]
theorem inductionOn {P : Ultrapower U alpha → Prop} (x : Ultrapower U alpha)
    (h : ∀ f : iota → alpha, P (ofSeq f)) : P x :=
  Germ.inductionOn x h

section OfSeqOps

theorem ofSeq_add [Add alpha] (f g : iota → alpha) :
    ofSeq (U := U) f + ofSeq (U := U) g = ofSeq (U := U) (fun i => f i + g i) := rfl

theorem ofSeq_mul [Mul alpha] (f g : iota → alpha) :
    ofSeq (U := U) f * ofSeq (U := U) g = ofSeq (U := U) (fun i => f i * g i) := rfl

theorem ofSeq_pow [Pow alpha ℕ] (f : iota → alpha) (n : ℕ) :
    ofSeq (U := U) f ^ n = ofSeq (U := U) (fun i => f i ^ n) := rfl

theorem ofSeq_neg [Neg alpha] (f : iota → alpha) :
    -ofSeq (U := U) f = ofSeq (U := U) (fun i => -f i) := rfl

theorem ofSeq_sub [Sub alpha] (f g : iota → alpha) :
    ofSeq (U := U) f - ofSeq (U := U) g = ofSeq (U := U) (fun i => f i - g i) := rfl

theorem ofSeq_inv [Inv alpha] (f : iota → alpha) :
    (ofSeq (U := U) f)⁻¹ = ofSeq (U := U) (fun i => (f i)⁻¹) := rfl

theorem ofSeq_div [Div alpha] (f g : iota → alpha) :
    ofSeq (U := U) f / ofSeq (U := U) g = ofSeq (U := U) (fun i => f i / g i) := rfl

@[simp] theorem ofSeq_zero [Zero alpha] : ofSeq (U := U) (fun _ => (0 : alpha)) = 0 := rfl

@[simp] theorem ofSeq_one [One alpha] : ofSeq (U := U) (fun _ => (1 : alpha)) = 1 := rfl

end OfSeqOps

/-- Map a function to the ultrapower. -/
def map (f : alpha -> beta) : Ultrapower U alpha -> Ultrapower U beta :=
  Germ.map f

/-- Map a binary function to the ultrapower. -/
noncomputable def map2 (f : alpha -> beta -> gamma) :
    Ultrapower U alpha -> Ultrapower U beta -> Ultrapower U gamma :=
  Germ.map₂ f

/-- Lift a predicate to the ultrapower. -/
def liftPred (P : alpha -> Prop) : Ultrapower U alpha -> Prop :=
  Germ.LiftPred P

/-- Lift a relation to the ultrapower. -/
def liftRel (R : alpha -> beta -> Prop) :
    Ultrapower U alpha -> Ultrapower U beta -> Prop :=
  Germ.LiftRel R

/-- Alias for `map`. -/
abbrev lift (f : alpha → beta) : Ultrapower U alpha → Ultrapower U beta := map f

/-- Alias for `map2`. -/
noncomputable abbrev lift₂ (f : alpha → beta → gamma) :
    Ultrapower U alpha → Ultrapower U beta → Ultrapower U gamma := map2 f

/-- Legacy alias for `liftPred`. -/
abbrev mapPred (P : alpha → Prop) : Ultrapower U alpha → Prop := liftPred P

/-- Legacy alias for `liftRel`. -/
abbrev mapRel (R : alpha → beta → Prop) :
    Ultrapower U alpha → Ultrapower U beta → Prop := liftRel R

/-- Alias for transfer-oriented APIs. -/
abbrev transferPred (P : alpha → Prop) : Ultrapower U alpha → Prop := liftPred P

/-- Alias for transfer-oriented APIs. -/
abbrev transferRel (R : alpha → beta → Prop) :
    Ultrapower U alpha → Ultrapower U beta → Prop := liftRel R

/-- The ultrafilter on the base type represented by a point of the ultrapower. -/
noncomputable def ultrafilterOf (x : Ultrapower U alpha) : Ultrafilter alpha :=
  Ultrafilter.map (Classical.choose (Quot.exists_rep x)) U

@[simp]
theorem liftPred_ofSeq {P : alpha → Prop} (f : iota → alpha) :
    liftPred (U := U) P (ofSeq (U := U) f) ↔ ∀ᶠ i in (U : Filter iota), P (f i) :=
  by
    simp [liftPred, ofSeq, Germ.liftPred_coe]

theorem liftPred_of_eventually {P : alpha → Prop} {f : iota → alpha}
    (h : ∀ᶠ i in (U : Filter iota), P (f i)) :
    liftPred (U := U) P (ofSeq (U := U) f) := by
  exact (liftPred_ofSeq (U := U) (P := P) f).2 h

theorem eventually_of_liftPred {P : alpha → Prop} {f : iota → alpha}
    (h : liftPred (U := U) P (ofSeq (U := U) f)) :
    ∀ᶠ i in (U : Filter iota), P (f i) := by
  exact (liftPred_ofSeq (U := U) (P := P) f).1 h

theorem liftPred_iff_eventually_of_eq {P : alpha → Prop} {x : Ultrapower U alpha} {f : iota → alpha}
    (hx : x = ofSeq (U := U) f) :
    liftPred (U := U) P x ↔ ∀ᶠ i in (U : Filter iota), P (f i) := by
  subst hx
  exact liftPred_ofSeq (U := U) (P := P) f

@[simp]
theorem liftRel_ofSeq {R : alpha → beta → Prop} (f : iota → alpha) (g : iota → beta) :
    liftRel (U := U) R (ofSeq (U := U) f) (ofSeq (U := U) g) ↔
      ∀ᶠ i in (U : Filter iota), R (f i) (g i) :=
  by
    simp [liftRel, ofSeq, Germ.liftRel_coe]

theorem liftRel_of_eventually {R : alpha → beta → Prop} {f : iota → alpha} {g : iota → beta}
    (h : ∀ᶠ i in (U : Filter iota), R (f i) (g i)) :
    liftRel (U := U) R (ofSeq (U := U) f) (ofSeq (U := U) g) := by
  exact (liftRel_ofSeq (U := U) (R := R) f g).2 h

theorem eventually_of_liftRel {R : alpha → beta → Prop} {f : iota → alpha} {g : iota → beta}
    (h : liftRel (U := U) R (ofSeq (U := U) f) (ofSeq (U := U) g)) :
    ∀ᶠ i in (U : Filter iota), R (f i) (g i) := by
  exact (liftRel_ofSeq (U := U) (R := R) f g).1 h

theorem liftRel_iff_eventually_of_eq {R : alpha → beta → Prop}
    {x : Ultrapower U alpha} {y : Ultrapower U beta}
    {f : iota → alpha} {g : iota → beta}
    (hx : x = ofSeq (U := U) f) (hy : y = ofSeq (U := U) g) :
    liftRel (U := U) R x y ↔ ∀ᶠ i in (U : Filter iota), R (f i) (g i) := by
  subst hx
  subst hy
  exact liftRel_ofSeq (U := U) (R := R) f g

@[simp]
theorem liftPred_std [NeBot (U : Filter iota)] {P : alpha → Prop} {a : alpha} :
    liftPred (U := U) P (std a : Ultrapower U alpha) ↔ P a := by
  simp [std, ultraConst, liftPred, Germ.liftPred_const_iff]

@[simp]
theorem liftRel_std [NeBot (U : Filter iota)] {R : alpha → beta → Prop} {a : alpha} {b : beta} :
    liftRel (U := U) R (std a : Ultrapower U alpha) (std b) ↔ R a b := by
  simp [std, ultraConst, liftRel, Germ.liftRel_const_iff]

@[simp]
theorem lift_std (f : alpha → beta) (a : alpha) :
    lift (U := U) f (std a : Ultrapower U alpha) = (std (f a) : Ultrapower U beta) := by
  simp [std, ultraConst, lift, map, Germ.map_const]

theorem forall_ofSeq_iff (P : Ultrapower U alpha → Prop) :
    (∀ x : Ultrapower U alpha, P x) ↔ ∀ f : iota → alpha, P (ofSeq (U := U) f) := by
  constructor
  · intro h f
    exact h (ofSeq f)
  · intro h x
    rcases ofSeq_surjective x with ⟨f, hf⟩
    simpa [hf] using h f

theorem exists_ofSeq_iff (P : Ultrapower U alpha → Prop) :
    (∃ x : Ultrapower U alpha, P x) ↔ ∃ f : iota → alpha, P (ofSeq (U := U) f) := by
  constructor
  · rintro ⟨x, hx⟩
    rcases ofSeq_surjective x with ⟨f, hf⟩
    refine ⟨f, ?_⟩
    simpa [hf.symm] using hx
  · rintro ⟨f, hf⟩
    exact ⟨ofSeq f, hf⟩

theorem forall_std_iff [NeBot (U : Filter iota)] (P : alpha → Prop) :
    (∀ a : alpha, P a) ↔ (∀ x : Ultrapower U alpha, liftPred (U := U) P x) := by
  constructor
  · intro h x
    rcases ofSeq_surjective x with ⟨f, hf⟩
    have h' : ∀ᶠ i in (U : Filter iota), P (f i) :=
      Filter.Eventually.of_forall fun i => h (f i)
    have hx : x = ofSeq (U := U) f := hf.symm
    simpa [hx, liftPred_ofSeq] using h'
  · intro h a
    simpa using (h (std a))

section LogicalConnectives

variable {P Q : alpha → Prop}

theorem liftPred_and (x : Ultrapower U alpha) :
    liftPred (U := U) (fun a => P a ∧ Q a) x ↔
      liftPred (U := U) P x ∧ liftPred (U := U) Q x := by
  rcases ofSeq_surjective x with ⟨f, hf⟩
  have hx : x = ofSeq (U := U) f := hf.symm
  simp [hx, liftPred_ofSeq]

theorem liftPred_or (x : Ultrapower U alpha) :
    liftPred (U := U) (fun a => P a ∨ Q a) x ↔
      liftPred (U := U) P x ∨ liftPred (U := U) Q x := by
  rcases ofSeq_surjective x with ⟨f, hf⟩
  have hx : x = ofSeq (U := U) f := hf.symm
  simp [hx, liftPred_ofSeq, Ultrafilter.eventually_or]

theorem liftPred_not (x : Ultrapower U alpha) :
    liftPred (U := U) (fun a => ¬ P a) x ↔ ¬ liftPred (U := U) P x := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [liftPred_ofSeq, liftPred_ofSeq]
  exact (Ultrafilter.eventually_not (f := U) (p := fun i => P (f i)))

theorem liftPred_imp (x : Ultrapower U alpha) :
    liftPred (U := U) (fun a => P a → Q a) x ↔
      (liftPred (U := U) P x → liftPred (U := U) Q x) := by
  rw [show (fun a => P a → Q a) = (fun a => ¬ P a ∨ Q a) by ext; tauto]
  rw [liftPred_or, liftPred_not]
  tauto

theorem liftPred_exists_iff {Q : alpha → beta → Prop} {x : Ultrapower U alpha} :
    liftPred (U := U) (fun a => ∃ b, Q a b) x ↔
      ∃ y : Ultrapower U beta, liftRel (U := U) Q x y := by
  classical
  rcases ofSeq_surjective x with ⟨f, hf⟩
  have hx : x = ofSeq (U := U) f := hf.symm
  simp only [hx, liftPred_ofSeq]
  constructor
  · intro h
    have : Nonempty beta := by
      obtain ⟨n, hn⟩ := Filter.nonempty_of_mem h
      obtain ⟨b, _⟩ := hn
      exact ⟨b⟩
    let g (n : iota) : beta :=
      if h : ∃ b, Q (f n) b then
        Classical.choose h
      else
        Classical.choice ‹_›
    refine ⟨ofSeq g, ?_⟩
    rw [liftRel_ofSeq]
    filter_upwards [h] with n hn
    have h_ex : ∃ b, Q (f n) b := hn
    simp only [g, h_ex, dif_pos]
    exact Classical.choose_spec h_ex
  · rintro ⟨y, hy⟩
    rcases ofSeq_surjective y with ⟨g, hg⟩
    have hy' : ∀ᶠ n in (U : Filter iota), Q (f n) (g n) := by
      simpa [hg.symm, liftRel_ofSeq] using hy
    filter_upwards [hy'] with n hn
    exact ⟨g n, hn⟩

end LogicalConnectives

/-- An element of an ultrapower is standard if it is the image of some `a : alpha`. -/
def IsStandard (x : Ultrapower U alpha) : Prop := ∃ a, x = std a

theorem IsStandard.of_std (a : alpha) : IsStandard (std a : Ultrapower U alpha) := ⟨a, rfl⟩

/-- Existential transfer (standard witnesses only). -/
theorem exists_std_iff [NeBot (U : Filter iota)] (P : alpha → Prop) :
    (∃ a : alpha, P a) ↔ (∃ x : Ultrapower U alpha, IsStandard x ∧ liftPred P x) := by
  constructor
  · intro ⟨a, ha⟩
    exact ⟨std a, IsStandard.of_std a, by simp [ha]⟩
  · rintro ⟨x, hstd, hP⟩
    obtain ⟨a, rfl⟩ := hstd
    exact ⟨a, by simpa using hP⟩

end Ultrapower

end Filter
