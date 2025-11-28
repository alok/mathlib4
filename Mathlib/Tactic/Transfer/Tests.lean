/-
Copyright (c) 2024 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Mathlib.Tactic.Transfer
import Mathlib.Data.Rat.Hyperrational
import Mathlib.Order.Filter.Germ.Product

/-!
# Transfer Tactic Test Suite

This file contains a comprehensive test suite for the transfer tactic and
transfer principle lemmas for hypernaturals and hyperrationals.

## Test Categories

1. Basic Transfer Lemmas - Core `liftPred` and `liftRel` functionality
2. Logical Connective Transfer - And, Or, Not, Imp
3. Quantifier Transfer - Forall, Exists
4. Order Transfer - Order relations transfer correctly
5. Predicate Transfer - Standard predicates like Prime, Even, Odd
6. TransferableNat Typeclass - Typeclass-based transfer
-/

open Hypernatural Hyperrational Filter
open Mathlib.Tactic.Transfer

namespace TransferTests

/-! ## 1. Basic Transfer Lemmas -/

section BasicTransfer

/-- Test: liftPred on standard element is equivalent to predicate on that element. -/
theorem test_liftPred_coe_nat {P : ℕ → Prop} {n : ℕ} :
    Hypernatural.liftPred P (n : ℕ*) ↔ P n :=
  Hypernatural.liftPred_coe

/-- Test: liftRel on standard elements is the relation on those elements. -/
theorem test_liftRel_coe_nat {R : ℕ → ℕ → Prop} {a b : ℕ} :
    Hypernatural.liftRel R (a : ℕ*) (b : ℕ*) ↔ R a b :=
  Hypernatural.liftRel_coe

/-- Test: liftPred on standard element for hyperrationals. -/
theorem test_liftPred_ofRat {P : ℚ → Prop} {q : ℚ} :
    Hyperrational.liftPred P (Hyperrational.ofRat q) ↔ P q :=
  Hyperrational.liftPred_ofRat

end BasicTransfer

/-! ## 2. Logical Connective Transfer -/

section LogicalTransfer

/-- Test: Conjunction transfers through liftPred. -/
theorem test_liftPred_and {P Q : ℕ → Prop} {x : ℕ*} :
    Hypernatural.liftPred (fun n => P n ∧ Q n) x ↔
    Hypernatural.liftPred P x ∧ Hypernatural.liftPred Q x :=
  Hypernatural.liftPred_and

/-- Test: Disjunction transfers through liftPred (uses ultrafilter property). -/
theorem test_liftPred_or {P Q : ℕ → Prop} {x : ℕ*} :
    Hypernatural.liftPred (fun n => P n ∨ Q n) x ↔
    Hypernatural.liftPred P x ∨ Hypernatural.liftPred Q x :=
  Hypernatural.liftPred_or

/-- Test: Negation transfers through liftPred (uses ultrafilter property). -/
theorem test_liftPred_not {P : ℕ → Prop} {x : ℕ*} :
    Hypernatural.liftPred (fun n => ¬P n) x ↔ ¬Hypernatural.liftPred P x :=
  Hypernatural.liftPred_not

/-- Test: Implication transfers through liftPred. -/
theorem test_liftPred_imp {P Q : ℕ → Prop} {x : ℕ*} :
    Hypernatural.liftPred (fun n => P n → Q n) x ↔
    (Hypernatural.liftPred P x → Hypernatural.liftPred Q x) :=
  Hypernatural.liftPred_imp

/-- Test: Conjunction for hyperrationals. -/
theorem test_liftPred_and_rat {P Q : ℚ → Prop} {x : ℚ*} :
    Hyperrational.liftPred (fun q => P q ∧ Q q) x ↔
    Hyperrational.liftPred P x ∧ Hyperrational.liftPred Q x :=
  Hyperrational.liftPred_and

/-- Test: Disjunction for hyperrationals. -/
theorem test_liftPred_or_rat {P Q : ℚ → Prop} {x : ℚ*} :
    Hyperrational.liftPred (fun q => P q ∨ Q q) x ↔
    Hyperrational.liftPred P x ∨ Hyperrational.liftPred Q x :=
  Hyperrational.liftPred_or

/-- Test: Negation for hyperrationals. -/
theorem test_liftPred_not_rat {P : ℚ → Prop} {x : ℚ*} :
    Hyperrational.liftPred (fun q => ¬P q) x ↔ ¬Hyperrational.liftPred P x :=
  Hyperrational.liftPred_not

end LogicalTransfer

/-! ## 3. Quantifier Transfer -/

section QuantifierTransfer

/-- Test: Universal quantifier transfer (both directions). -/
theorem test_forall_transfer {P : ℕ → Prop} :
    (∀ n : ℕ, P n) ↔ (∀ x : ℕ*, Hypernatural.liftPred P x) :=
  Hypernatural.forall_iff_forall_liftPred

/-- Test: Existential transfer (forward direction). -/
theorem test_exists_transfer {P : ℕ → Prop} :
    (∃ n : ℕ, P n) → (∃ x : ℕ*, Hypernatural.liftPred P x) :=
  Hypernatural.exists_implies_exists_liftPred

/-- Test: Universal transfer for hyperrationals. -/
theorem test_forall_transfer_rat {P : ℚ → Prop} :
    (∀ q : ℚ, P q) ↔ (∀ x : ℚ*, Hyperrational.liftPred P x) :=
  Hyperrational.forall_iff_forall_liftPred

/-- Test: Existential transfer for hyperrationals. -/
theorem test_exists_transfer_rat {P : ℚ → Prop} :
    (∃ q : ℚ, P q) → (∃ x : ℚ*, Hyperrational.liftPred P x) :=
  Hyperrational.exists_implies_exists_liftPred

end QuantifierTransfer

/-! ## 4. Arithmetic Transfer -/

section ArithmeticTransfer

/-- Test: Addition is compatible with ofSeq. -/
theorem test_add_ofSeq {f g : ℕ → ℕ} :
    ofSeq f + ofSeq g = ofSeq (f + g) := rfl

/-- Test: Multiplication is compatible with ofSeq. -/
theorem test_mul_ofSeq {f g : ℕ → ℕ} :
    ofSeq f * ofSeq g = ofSeq (f * g) := rfl

/-- Test: Addition for hyperrationals. -/
theorem test_add_ofSeq_rat {f g : ℕ → ℚ} :
    Hyperrational.ofSeq f + Hyperrational.ofSeq g = Hyperrational.ofSeq (f + g) := rfl

/-- Test: Multiplication for hyperrationals. -/
theorem test_mul_ofSeq_rat {f g : ℕ → ℚ} :
    Hyperrational.ofSeq f * Hyperrational.ofSeq g = Hyperrational.ofSeq (f * g) := rfl

end ArithmeticTransfer

/-! ## 5. Order Transfer -/

section OrderTransfer

/-- Test: Less-than transfers via ofSeq. -/
theorem test_lt_ofSeq {f g : ℕ → ℕ} :
    ofSeq f < ofSeq g ↔ ∀ᶠ n in hyperfilter ℕ, f n < g n :=
  ofSeq_lt_ofSeq

/-- Test: Less-or-equal transfers via ofSeq. -/
theorem test_le_ofSeq {f g : ℕ → ℕ} :
    ofSeq f ≤ ofSeq g ↔ ∀ᶠ n in hyperfilter ℕ, f n ≤ g n :=
  ofSeq_le_ofSeq

/-- Test: Equality transfers via ofSeq. -/
theorem test_eq_ofSeq {f g : ℕ → ℕ} :
    ofSeq f = ofSeq g ↔ ∀ᶠ n in hyperfilter ℕ, f n = g n :=
  ofSeq_eq_ofSeq

/-- Test: Order relations for hyperrationals. -/
theorem test_lt_ofSeq_rat {f g : ℕ → ℚ} :
    Hyperrational.ofSeq f < Hyperrational.ofSeq g ↔
    ∀ᶠ n in hyperfilter ℕ, f n < g n :=
  Hyperrational.ofSeq_lt_ofSeq

theorem test_le_ofSeq_rat {f g : ℕ → ℚ} :
    Hyperrational.ofSeq f ≤ Hyperrational.ofSeq g ↔
    ∀ᶠ n in hyperfilter ℕ, f n ≤ g n :=
  Hyperrational.ofSeq_le_ofSeq

end OrderTransfer

/-! ## 6. Predicate Transfer -/

section PredicateTransfer

/-- Test: HyperPrime is defined as liftPred of Nat.Prime. -/
theorem test_HyperPrime_def : HyperPrime = Hypernatural.liftPred Nat.Prime := rfl

/-- Test: Standard primes are HyperPrime when embedded. -/
theorem test_std_prime_is_HyperPrime {p : ℕ} (hp : Nat.Prime p) : HyperPrime (p : ℕ*) := by
  rw [HyperPrime, Hypernatural.liftPred_coe]
  exact hp

/-- Test: Even predicate transfers. -/
theorem test_even_transfer {n : ℕ} (h : Even n) :
    Hypernatural.liftPred Even (n : ℕ*) := by
  rw [Hypernatural.liftPred_coe]
  exact h

/-- Test: Odd predicate transfers. -/
theorem test_odd_transfer {n : ℕ} (h : Odd n) :
    Hypernatural.liftPred Odd (n : ℕ*) := by
  rw [Hypernatural.liftPred_coe]
  exact h

/-- Test: Divisibility relation transfers. -/
theorem test_dvd_transfer {d n : ℕ} (h : d ∣ n) :
    Hypernatural.liftRel (· ∣ ·) (d : ℕ*) (n : ℕ*) := by
  rw [Hypernatural.liftRel_coe]
  exact h

end PredicateTransfer

/-! ## 7. Combined Transfer Examples -/

section CombinedExamples

/-- Test: The infinitely many primes theorem transfers. -/
theorem test_infinitely_many_primes_transfer
    (h : ∀ n : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > n) :
    ∀ x : ℕ*, ∃ p : ℕ*, HyperPrime p ∧ p > x :=
  infinitely_many_primes_transfer h

/-- Test: Transitivity of order transfers. -/
theorem test_lt_trans_transfer {x y z : ℕ*} (hxy : x < y) (hyz : y < z) : x < z :=
  lt_trans hxy hyz

/-- Test: Combined predicate: even and positive transfers. -/
theorem test_combined_pred {n : ℕ} (he : Even n) (hp : 0 < n) :
    Hypernatural.liftPred (fun m => Even m ∧ 0 < m) (n : ℕ*) := by
  rw [Hypernatural.liftPred_and, Hypernatural.liftPred_coe, Hypernatural.liftPred_coe]
  exact ⟨he, hp⟩

end CombinedExamples

/-! ## 8. Germ-Product Bridge Tests -/

section BridgeTests

/-- Test: The Germ-Product equivalence exists. -/
def test_germ_product_equiv {l : Filter ℕ} :
    Filter.Germ l ℕ ≃ Filter.Product l (fun _ => ℕ) :=
  Filter.Germ.prodEquiv

/-- Test: prodEquiv preserves the quotient structure. -/
theorem test_prodEquiv_ofFun {l : Filter ℕ} (f : ℕ → ℕ) :
    Filter.Germ.prodEquiv (Filter.Germ.ofFun f : Filter.Germ l ℕ) =
    (f : Filter.Product l (fun _ => ℕ)) :=
  Filter.Germ.prodEquiv_ofFun f

end BridgeTests

/-! ## 9. Infinitesimal Tests (Hyperrational) -/

section InfinitesimalTests

/-- Test: Sum of infinitesimals is infinitesimal. -/
theorem test_infinitesimal_add {x y : ℚ*}
    (hx : Hyperrational.Infinitesimal x) (hy : Hyperrational.Infinitesimal y) :
    Hyperrational.Infinitesimal (x + y) :=
  Hyperrational.Infinitesimal.add hx hy

/-- Test: Negation preserves infinitesimal. -/
theorem test_infinitesimal_neg {x : ℚ*} (hx : Hyperrational.Infinitesimal x) :
    Hyperrational.Infinitesimal (-x) :=
  Hyperrational.Infinitesimal.neg hx

end InfinitesimalTests

/-! ## 10. IST Axiom Tests -/

section ISTTests

open Hyper

/-- Test: IsStandard holds for standard elements. -/
theorem test_IsStandard_std (n : ℕ) : IsStandard (Hyper.std n : Hyper ℕ ℕ) :=
  IsStandard.of_std n

/-- Test: Transfer (T) - Universal quantifier. -/
theorem test_transfer_forall {P : ℕ → Prop} :
    (∀ n : ℕ, P n) ↔ (∀ x : Hyper ℕ ℕ, Hyper.liftPred P x) :=
  Hyper.forall_std_iff P

/-- Test: Transfer (T) - Existential quantifier with standard restriction. -/
theorem test_transfer_exists {P : ℕ → Prop} :
    (∃ n : ℕ, P n) ↔ (∃ x : Hyper ℕ ℕ, IsStandard x ∧ Hyper.liftPred P x) :=
  Hyper.exists_std_iff P

/-- Test: Idealization (I) - Overflow principle. -/
theorem test_overflow {P : ℕ → Prop} (hP : ∀ n : ℕ, P n) :
    ∀ x : Hyper ℕ ℕ, Hyper.liftPred P x :=
  Hyper.overflow hP

/-- Test: Idealization (I) - Existence of infinite elements. -/
theorem test_exists_infinite : ∃ w : Hyper ℕ ℕ, ∀ n : ℕ, Hyper.std n < w :=
  Hyper.exists_infinite_nat

/-- Test: omega is greater than all standard naturals. -/
theorem test_omega_gt_std (n : ℕ) : Hyper.std n < Hyper.omega :=
  Hyper.omega_gt_std n

/-- Test: Idealization (I) - Underflow principle. -/
theorem test_underflow {P : ℕ → Prop} (hP : Hyper.liftPred P Hyper.omega) :
    ∀ n : ℕ, ∃ m : ℕ, m ≥ n ∧ P m :=
  Hyper.underflow Hyper.omega_gt_std hP

/-- Test: Standardization (S) - standard part of predicate. -/
theorem test_standardization (P : Hyper ℕ ℕ → Prop) :
    ∃ Q : ℕ → Prop, ∀ n : ℕ, Q n ↔ P (Hyper.std n) :=
  Hyper.standardization P

/-- Test: standardPart is inverse of liftPred on standard elements. -/
theorem test_standardPart_liftPred (P : ℕ → Prop) :
    Hyper.standardPart (Hyper.liftPred P : Hyper ℕ ℕ → Prop) = P :=
  Hyper.standardPart_liftPred P

/-- Test: IsInfinite for omega. -/
theorem test_omega_isInfinite : Hyper.IsInfinite Hyper.omega :=
  Hyper.omega_isInfinite

/-- Test: Generic omega for any infinite linearly ordered type. -/
theorem test_omega'_gt_std (n : ℕ) : Hyper.std n < (Hyper.omega' : Hyper ℕ ℕ) :=
  Hyper.omega'_gt_std n

end ISTTests

/-! ## Test Summary

All tests pass if this file compiles without errors.

Total tests: 45+
Categories covered:
- Basic liftPred/liftRel
- Logical connectives (∧, ∨, ¬, →)
- Quantifiers (∀, ∃)
- Arithmetic operations (+, *)
- Order relations (<, ≤, =)
- Standard predicates (Prime, Even, Odd, ∣)
- Combined examples
- Germ-Product bridge
- Infinitesimal properties
- IST axioms (Transfer, Idealization, Standardization)
-/

end TransferTests
