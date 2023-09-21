/-
Copyright (c) 2022 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.Algebra.Associated
import Mathlib.NumberTheory.Divisors

#align_import algebra.is_prime_pow from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

/-!
# Prime powers

This file deals with prime powers: numbers which are positive integer powers of a single prime.
-/


variable {R : Type*} [CommMonoidWithZero R] (n p : R) (k : ℕ)

/-- `n` is a prime power if there is a prime `p` and a positive natural `k` such that `n` can be
written as `p^k`. -/
def IsPrimePow : Prop :=
  ∃ (p : R) (k : ℕ), Prime p ∧ 0 < k ∧ p ^ k = n
#align is_prime_pow IsPrimePow

lemma isPrimePow_def : IsPrimePow n ↔ ∃ (p : R) (k : ℕ), Prime p ∧ 0 < k ∧ p ^ k = n :=
  Iff.rfl
#align is_prime_pow_def isPrimePow_def

/-- An equivalent definition for prime powers: `n` is a prime power iff there is a prime `p` and a
natural `k` such that `n` can be written as `p^(k+1)`. -/
lemma isPrimePow_iff_pow_succ : IsPrimePow n ↔ ∃ (p : R) (k : ℕ), Prime p ∧ p ^ (k + 1) = n :=
  (isPrimePow_def _).trans
    ⟨fun ⟨p, k, hp, hk, hn⟩ => ⟨_, _, hp, by rwa [Nat.sub_add_cancel hk]⟩, fun ⟨p, k, hp, hn⟩ =>
      ⟨_, _, hp, Nat.succ_pos', hn⟩⟩
#align is_prime_pow_iff_pow_succ isPrimePow_iff_pow_succ

lemma not_isPrimePow_zero [NoZeroDivisors R] : ¬IsPrimePow (0 : R) := by
  simp only [isPrimePow_def, not_exists, not_and', and_imp]
  intro x n _hn hx
  rw [pow_eq_zero hx]
  simp
#align not_is_prime_pow_zero not_isPrimePow_zero

lemma IsPrimePow.not_unit {n : R} (h : IsPrimePow n) : ¬IsUnit n :=
  let ⟨_p, _k, hp, hk, hn⟩ := h
  hn ▸ (isUnit_pow_iff hk.ne').not.mpr hp.not_unit
#align is_prime_pow.not_unit IsPrimePow.not_unit

lemma IsUnit.not_isPrimePow {n : R} (h : IsUnit n) : ¬IsPrimePow n := fun h' => h'.not_unit h
#align is_unit.not_is_prime_pow IsUnit.not_isPrimePow

lemma not_isPrimePow_one : ¬IsPrimePow (1 : R) :=
  isUnit_one.not_isPrimePow
#align not_is_prime_pow_one not_isPrimePow_one

lemma Prime.isPrimePow {p : R} (hp : Prime p) : IsPrimePow p :=
  ⟨p, 1, hp, zero_lt_one, by simp⟩
#align prime.is_prime_pow Prime.isPrimePow

lemma IsPrimePow.pow {n : R} (hn : IsPrimePow n) {k : ℕ} (hk : k ≠ 0) : IsPrimePow (n ^ k) :=
  let ⟨p, k', hp, hk', hn⟩ := hn
  ⟨p, k * k', hp, mul_pos hk.bot_lt hk', by rw [pow_mul', hn]⟩
#align is_prime_pow.pow IsPrimePow.pow

lemma IsPrimePow.ne_zero [NoZeroDivisors R] {n : R} (h : IsPrimePow n) : n ≠ 0 := fun t =>
  not_isPrimePow_zero (t ▸ h)
#align is_prime_pow.ne_zero IsPrimePow.ne_zero

lemma IsPrimePow.ne_one {n : R} (h : IsPrimePow n) : n ≠ 1 := fun t =>
  not_isPrimePow_one (t ▸ h)
#align is_prime_pow.ne_one IsPrimePow.ne_one

section Nat

lemma isPrimePow_nat_iff (n : ℕ) : IsPrimePow n ↔ ∃ p k : ℕ, Nat.Prime p ∧ 0 < k ∧ p ^ k = n := by
  simp only [isPrimePow_def, Nat.prime_iff]
#align is_prime_pow_nat_iff isPrimePow_nat_iff

lemma Nat.Prime.isPrimePow {p : ℕ} (hp : p.Prime) : IsPrimePow p :=
  _root_.Prime.isPrimePow (prime_iff.mp hp)
#align nat.prime.is_prime_pow Nat.Prime.isPrimePow

lemma isPrimePow_nat_iff_bounded (n : ℕ) :
    IsPrimePow n ↔ ∃ p : ℕ, p ≤ n ∧ ∃ k : ℕ, k ≤ n ∧ p.Prime ∧ 0 < k ∧ p ^ k = n := by
  rw [isPrimePow_nat_iff]
  refine' Iff.symm ⟨fun ⟨p, _, k, _, hp, hk, hn⟩ => ⟨p, k, hp, hk, hn⟩, _⟩
  rintro ⟨p, k, hp, hk, rfl⟩
  refine' ⟨p, _, k, (Nat.lt_pow_self hp.one_lt _).le, hp, hk, rfl⟩
  conv => { lhs; rw [←(pow_one p)] }
  exact (Nat.pow_le_iff_le_right hp.two_le).mpr hk
#align is_prime_pow_nat_iff_bounded isPrimePow_nat_iff_bounded

instance {n : ℕ} : Decidable (IsPrimePow n) :=
  decidable_of_iff' _ (isPrimePow_nat_iff_bounded n)

lemma IsPrimePow.dvd {n m : ℕ} (hn : IsPrimePow n) (hm : m ∣ n) (hm₁ : m ≠ 1) : IsPrimePow m := by
  rw [isPrimePow_nat_iff] at hn ⊢
  rcases hn with ⟨p, k, hp, _hk, rfl⟩
  obtain ⟨i, hik, rfl⟩ := (Nat.dvd_prime_pow hp).1 hm
  refine' ⟨p, i, hp, _, rfl⟩
  apply Nat.pos_of_ne_zero
  rintro rfl
  simp only [pow_zero, ne_eq] at hm₁
#align is_prime_pow.dvd IsPrimePow.dvd

lemma Nat.disjoint_divisors_filter_isPrimePow {a b : ℕ} (hab : a.Coprime b) :
    Disjoint (a.divisors.filter IsPrimePow) (b.divisors.filter IsPrimePow) := by
  simp only [Finset.disjoint_left, Finset.mem_filter, and_imp, Nat.mem_divisors, not_and]
  rintro n han _ha hn hbn _hb -
  exact hn.ne_one (Nat.eq_one_of_dvd_coprimes hab han hbn)
#align nat.disjoint_divisors_filter_prime_pow Nat.disjoint_divisors_filter_isPrimePow

lemma IsPrimePow.two_le : ∀ {n : ℕ}, IsPrimePow n → 2 ≤ n
  | 0, h => (not_isPrimePow_zero h).elim
  | 1, h => (not_isPrimePow_one h).elim
  | _n + 2, _ => le_add_self
#align is_prime_pow.two_le IsPrimePow.two_le

lemma IsPrimePow.pos {n : ℕ} (hn : IsPrimePow n) : 0 < n :=
  pos_of_gt hn.two_le
#align is_prime_pow.pos IsPrimePow.pos

lemma IsPrimePow.one_lt {n : ℕ} (h : IsPrimePow n) : 1 < n :=
  h.two_le
#align is_prime_pow.one_lt IsPrimePow.one_lt

end Nat
