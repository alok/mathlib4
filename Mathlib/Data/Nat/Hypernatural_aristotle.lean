/-
This file was edited by Aristotle.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

The following was proved by Aristotle:

- lemma mul_succ (x y : ℕ*) : x * succ y = x * y + x

- lemma succ_mul (x y : ℕ*) : succ x * y = x * y + y

- lemma hpow_coe (m n : ℕ) : hpow (m : ℕ*) n = (m ^ n : ℕ*)

- lemma hpow_omega_infinite (n : ℕ) (hn : 0 < n) : Infinite (hpow ω n)

- lemma hmin_le_left (x y : ℕ*) : hmin x y ≤ x

- lemma hmin_le_right (x y : ℕ*) : hmin x y ≤ y

- lemma le_hmax_left (x y : ℕ*) : x ≤ hmax x y

- lemma le_hmax_right (x y : ℕ*) : y ≤ hmax x y

- lemma hmin_comm (x y : ℕ*) : hmin x y = hmin y x

- lemma hmax_comm (x y : ℕ*) : hmax x y = hmax y x

- lemma Infinite.tsub_hFinite {x y : ℕ*} (hx : Infinite x) (hy : HFinite y) (hpos : y < x) :
    Infinite (x - y)

- lemma hfact_coe (n : ℕ) : hfact (n : ℕ*) = (Nat.factorial n : ℕ*)

- lemma hfact_pos (x : ℕ*) : 0 < hfact x

- lemma infinite_hfact_omega : Infinite (hfact ω)

- lemma hgcd_comm (x y : ℕ*) : hgcd x y = hgcd y x

- lemma hlcm_comm (x y : ℕ*) : hlcm x y = hlcm y x

- lemma hgcd_dvd_left (x y : ℕ*) : hgcd x y ∣ x

- lemma hgcd_dvd_right (x y : ℕ*) : hgcd x y ∣ y

- lemma dvd_hlcm_left (x y : ℕ*) : x ∣ hlcm x y

- lemma dvd_hlcm_right (x y : ℕ*) : y ∣ hlcm x y

- lemma eq_iff_eventually_eq (x y : ℕ*) : x = y ↔ ∃ f g : ℕ → ℕ, x = ofSeq f ∧ y = ofSeq g ∧
    ∀ᶠ n in nonstandardUltrafilter ℕ, f n = g n
-/

/-
Copyright (c) 2024 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Mathlib.Order.Filter.FilterProduct
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Basic


set_option linter.style.longFile 1800

/-!
# Hypernatural numbers

We build the *hypernatural numbers* `ℕ*` as germs of sequences of naturals on
the (non‑principal) `nonstandardUltrafilter ℕ`, mirroring the construction of `ℝ*` in
`Mathlib/Analysis/Real/Hyperreal.lean`.  The API here is intentionally kept
parallel to the hyperreal API where that makes sense for `ℕ`.
-/

open Classical

open Filter Germ Topology

/-- Hypernatural numbers on the ultrafilter extending the cofinite filter. -/
noncomputable def Hypernatural : Type :=
  Germ (nonstandardUltrafilter ℕ : Filter ℕ) ℕ

namespace Hypernatural

/-- Notation for hypernaturals. -/
@[inherit_doc] notation "ℕ*" => Hypernatural

noncomputable instance : Semiring ℕ* :=
  inferInstanceAs (Semiring (Germ _ _))

noncomputable instance : LinearOrder ℕ* :=
  inferInstanceAs (LinearOrder (Germ _ _))

/-- Natural embedding `ℕ → ℕ*`. -/
@[coe] noncomputable def ofNat : ℕ → ℕ* := const

noncomputable instance instOfNat (n : ℕ) : OfNat ℕ* n := ⟨ofNat n⟩

noncomputable instance : CoeTC ℕ ℕ* := ⟨ofNat⟩

noncomputable instance : Inhabited ℕ* := ⟨ofNat 0⟩

/-- Coercions from `ℕ` to `ℕ*` behave definitionally. -/
@[simp, norm_cast] theorem coe_eq_coe {a b : ℕ} : (a : ℕ*) = b ↔ a = b := Germ.const_inj

theorem coe_ne_coe {a b : ℕ} : (a : ℕ*) ≠ b ↔ a ≠ b := coe_eq_coe.not

@[simp, norm_cast] theorem coe_zero : ((0 : ℕ) : ℕ*) = 0 := rfl

@[simp, norm_cast] theorem coe_one : ((1 : ℕ) : ℕ*) = 1 := rfl

@[simp, norm_cast] theorem coe_add (a b : ℕ) : ((a + b : ℕ) : ℕ*) = a + b := rfl

@[simp, norm_cast] theorem coe_mul (a b : ℕ) : ((a * b : ℕ) : ℕ*) = a * b := rfl

@[simp, norm_cast] theorem coe_le_coe {a b : ℕ} : (a : ℕ*) ≤ b ↔ a ≤ b := Germ.const_le_iff

@[simp, norm_cast] theorem coe_lt_coe {a b : ℕ} : (a : ℕ*) < b ↔ a < b := Germ.const_lt_iff

/-- Build a hypernatural from a sequence. -/
def ofSeq (f : ℕ → ℕ) : ℕ* := (↑f : Germ (nonstandardUltrafilter ℕ : Filter ℕ) ℕ)

theorem ofSeq_const (r : ℕ) : ofSeq (fun _ => r) = (r : ℕ*) := rfl

theorem ofSeq_surjective : Function.Surjective ofSeq := Quot.exists_rep

theorem ofSeq_eq_ofSeq {f g : ℕ → ℕ} : ofSeq f = ofSeq g ↔ ∀ᶠ n in nonstandardUltrafilter ℕ, f n = g n :=
  Germ.coe_eq

theorem ofSeq_le_ofSeq {f g : ℕ → ℕ} : ofSeq f ≤ ofSeq g ↔ ∀ᶠ n in nonstandardUltrafilter ℕ, f n ≤ g n :=
  Germ.coe_le

theorem ofSeq_lt_ofSeq {f g : ℕ → ℕ} : ofSeq f < ofSeq g ↔ ∀ᶠ n in nonstandardUltrafilter ℕ, f n < g n :=
  Germ.coe_lt

/-- A canonical infinite hypernatural. -/
noncomputable def omega : ℕ* := ofSeq Nat.cast

@[inherit_doc] scoped notation "ω" => Hypernatural.omega

theorem omega_pos : 0 < ω :=
  Germ.coe_pos.2 <|
    nonstandardUltrafilter_le_atTop <|
      (eventually_gt_atTop 0).mono fun _n => Nat.cast_pos.2

theorem omega_ne_zero : ω ≠ 0 := omega_pos.ne'

/-- `Infinite x` means that `x` is larger than every standard natural. -/
def Infinite (x : ℕ*) : Prop := ∀ m : ℕ, (m : ℕ*) < x

/-- Positive infinity predicate, aligned with the hyperreal API. -/
def InfinitePos (x : ℕ*) : Prop := ∀ m : ℕ, (m : ℕ*) < x

@[simp] lemma infinitePos_iff_infinite {x : ℕ*} : InfinitePos x ↔ Infinite x := Iff.rfl

theorem InfinitePos.pos {x : ℕ*} (hx : InfinitePos x) : 0 < x := by simpa using hx 0

@[simp] theorem not_infinite_zero : ¬Infinite (0 : ℕ*) := by
  intro h
  exact (lt_irrefl (0 : ℕ*)) (h 0)

@[simp] theorem infinite_omega : Infinite ω := by
  intro m
  have : (m : ℕ*) < ofSeq Nat.cast :=
    (ofSeq_lt_ofSeq).2 <| nonstandardUltrafilter_le_atTop <| (eventually_gt_atTop m).mono fun n hn => by
      simpa using hn
  simpa [omega] using this

theorem Infinite.ne_zero {x : ℕ*} (hx : Infinite x) : x ≠ 0 := by
  intro h
  have : (0 : ℕ*) < (0 : ℕ*) := by simpa [h] using hx 0
  exact lt_irrefl _ this

/-- Standard-part predicate: for hypernaturals this is just equality with a
standard natural number, but keeping the predicate aligns with the hyperreal
API. -/
def IsSt (x : ℕ*) (r : ℕ) : Prop := x = r

lemma isSt_iff_eq {x : ℕ*} {r : ℕ} : IsSt x r ↔ x = r := Iff.rfl

lemma isSt_ofSeq_iff_eventually_eq {f : ℕ → ℕ} {r : ℕ} :
    IsSt (ofSeq f) r ↔ ∀ᶠ n in nonstandardUltrafilter ℕ, f n = r := by
  constructor
  · intro h
    change ofSeq f = (r : ℕ*) at h
    have h' : ofSeq f = ofSeq (fun _ => r) := by simpa [ofSeq_const] using h
    simpa using (ofSeq_eq_ofSeq (f := f) (g := fun _ => r)).1 h'
  · intro hf
    exact (ofSeq_eq_ofSeq).2 hf

lemma IsSt.unique {x : ℕ*} {r s : ℕ} (hr : IsSt x r) (hs : IsSt x s) : r = s := by
  simpa [IsSt] using (hr.symm.trans hs)

/-- Standard-part map: returns the `r : ℕ` witnessing `IsSt x r`, if any,
and `0` otherwise. -/
noncomputable def st (x : ℕ*) : ℕ := if h : ∃ r, IsSt x r then Classical.choose h else 0

lemma IsSt.st_eq {x : ℕ*} {r : ℕ} (hx : IsSt x r) : st x = r := by
  classical
  have h : ∃ r, IsSt x r := ⟨r, hx⟩
  have hchoose : IsSt x (Classical.choose h) := Classical.choose_spec h
  have hEq : Classical.choose h = r := (hx.unique hchoose).symm
  simp [st, h, hEq]

@[simp] lemma st_coe (r : ℕ) : st (r : ℕ*) = r := (IsSt.st_eq (x := (r : ℕ*)) (r := r) rfl)

lemma not_infinite_of_isSt {x : ℕ*} {r : ℕ} (hx : IsSt x r) : ¬Infinite x := by
  intro h
  cases hx
  exact (lt_irrefl (r : ℕ*)) (h r)

lemma infinite_not_isSt {x : ℕ*} (hx : Infinite x) : ¬∃ r, IsSt x r := by
  intro h; rcases h with ⟨r, hr⟩; exact not_infinite_of_isSt (x := x) (r := r) hr hx

/-- Standard-part respects addition when both summands are standard. -/
lemma IsSt.add {x y : ℕ*} {r s : ℕ} (hx : IsSt x r) (hy : IsSt y s) : IsSt (x + y) (r + s) := by
  dsimp [IsSt] at hx hy ⊢
  simp [hx, hy]

/-- Order is reflected to standard parts when both arguments are standard. -/
lemma IsSt.le {x y : ℕ*} {r s : ℕ} (hx : IsSt x r) (hy : IsSt y s) (hxy : x ≤ y) : r ≤ s := by
  dsimp [IsSt] at hx hy
  subst hx; subst hy; simpa using hxy

/-- If two hypernaturals have standard parts and those parts satisfy `r < s`,
then the hypernaturals are ordered. -/
lemma IsSt.lt {x y : ℕ*} {r s : ℕ} (hx : IsSt x r) (hy : IsSt y s) (hrs : r < s) : x < y := by
  dsimp [IsSt] at hx hy
  subst hx; subst hy; simpa using hrs

/-- If a hypernatural is bounded above, it is eventually constant, hence standard. -/
lemma exists_st_of_not_infinite {x : ℕ*} (hx : ¬ Infinite x) : ∃ r : ℕ, IsSt x r := by
  classical
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  obtain ⟨m, hm⟩ := not_forall.mp hx
  have hle : ofSeq f ≤ (m : ℕ*) := not_lt.mp hm
  have hf_le : ∀ᶠ n in nonstandardUltrafilter ℕ, f n ≤ m :=
    (ofSeq_le_ofSeq (f := f) (g := fun _ => m)).1 (by simpa [ofSeq_const] using hle)
  have hUnion_mem :
      (⋃ r ∈ Finset.range (m + 1), {n | f n = r}) ∈ (nonstandardUltrafilter ℕ : Filter ℕ) := by
    have hsubset :
        {n | f n ≤ m} ⊆ ⋃ r ∈ Finset.range (m + 1), {n | f n = r} := by
      intro n hn
      have hrange : f n ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hn)
      exact Set.mem_iUnion.mpr ⟨f n, Set.mem_iUnion.mpr ⟨hrange, rfl⟩⟩
    exact (nonstandardUltrafilter ℕ : Filter ℕ).mem_of_superset hf_le hsubset
  let u : Ultrafilter ℕ := nonstandardUltrafilter ℕ
  have hUnion_mem' : (⋃ r ∈ Finset.range (m + 1), {n | f n = r}) ∈ (u : Filter ℕ) := hUnion_mem
  have aux : ∀ s : Finset ℕ,
      (⋃ r ∈ s, {n | f n = r}) ∈ (u : Filter ℕ) →
      ∃ r ∈ s, {n | f n = r} ∈ (u : Filter ℕ) := by
    intro s
    refine Finset.induction_on s ?base ?step
    · intro h
      simp at h
    · intro a s ha hs hmem
      have hmem' : {n | f n = a} ∪ ⋃ r ∈ s, {n | f n = r} ∈ (u : Filter ℕ) := by
        simpa [Finset.mem_insert, ha] using hmem
      have hmem'' : {n | f n = a} ∈ (u : Filter ℕ) ∨ (⋃ r ∈ s, {n | f n = r}) ∈ (u : Filter ℕ) :=
        (u.union_mem_iff (s := {n | f n = a}) (t := ⋃ r ∈ s, {n | f n = r})).1 hmem'
      cases hmem'' with
      | inl h => exact ⟨a, by simp [Finset.mem_insert, ha], h⟩
        | inr h =>
            rcases hs h with ⟨r, hr, hrmem⟩
            exact ⟨r, by simp [Finset.mem_insert, hr], hrmem⟩
  rcases aux _ hUnion_mem' with ⟨r, hr, hrmem⟩
  exact ⟨r, (isSt_ofSeq_iff_eventually_eq (f := f) (r := r)).2 hrmem⟩

lemma exists_st_iff_not_infinite {x : ℕ*} : (∃ r : ℕ, IsSt x r) ↔ ¬ Infinite x := by
  constructor
  · intro h; rcases h with ⟨r, hr⟩; exact not_infinite_of_isSt (x := x) (r := r) hr
  · exact exists_st_of_not_infinite

lemma infinite_iff_not_exists_st {x : ℕ*} : Infinite x ↔ ¬∃ r : ℕ, IsSt x r := by
  classical
  have h := exists_st_iff_not_infinite (x := x)
  constructor
  · intro hx; exact infinite_not_isSt hx
  · intro hnot
    have : ¬¬ Infinite x := by
      intro hfin
      exact hnot (h.mpr hfin)
    exact Classical.not_not.mp this

lemma IsSt.isSt_st {x : ℕ*} {r : ℕ} (hx : IsSt x r) : IsSt x (st x) := by
  simpa [hx.st_eq] using hx

lemma isSt_st_of_exists_st {x : ℕ*} (hx : ∃ r : ℕ, IsSt x r) : IsSt x (st x) := by
  rcases hx with ⟨r, hr⟩
  exact hr.isSt_st

lemma isSt_st_of_not_infinite {x : ℕ*} (hx : ¬ Infinite x) : IsSt x (st x) :=
  isSt_st_of_exists_st (exists_st_of_not_infinite (x := x) hx)

lemma Infinite.st_eq {x : ℕ*} (hx : Infinite x) : st x = 0 := by
  classical
  have hx' : ¬ ∃ r, IsSt x r := infinite_not_isSt hx
  simp [st, hx']

/-- Standard-part is monotone on finite hypernaturals. -/
lemma st_le_of_le {x y : ℕ*} (hx : ¬ Infinite x) (hy : ¬ Infinite y) (hxy : x ≤ y) : st x ≤ st y :=
  (isSt_st_of_not_infinite (x := x) hx).le (isSt_st_of_not_infinite (x := y) hy) hxy

/-- If standard parts are ordered strictly, so are the finite hypernaturals. -/
lemma lt_of_st_lt {x y : ℕ*} (hx : ¬ Infinite x) (hy : ¬ Infinite y) (h : st x < st y) : x < y :=
  (isSt_st_of_not_infinite (x := x) hx).lt (isSt_st_of_not_infinite (x := y) hy) h

/-- Sums of finite hypernaturals are finite. -/
theorem not_infinite_add {x y : ℕ*} (hx : ¬ Infinite x) (hy : ¬ Infinite y) :
    ¬ Infinite (x + y) := by
  intro h
  rcases exists_st_of_not_infinite (x := x) hx with ⟨r, hr⟩
  rcases exists_st_of_not_infinite (x := y) hy with ⟨s, hs⟩
  subst hr; subst hs
  have : (r + s : ℕ*) < (r + s : ℕ*) := h (r + s)
  exact lt_irrefl _ this

/-- A hypernatural is HFinite (finite) if it is not infinite. -/
def HFinite (x : ℕ*) : Prop := ¬ Infinite x

@[simp] lemma hFinite_iff_not_infinite {x : ℕ*} : HFinite x ↔ ¬ Infinite x := Iff.rfl

lemma not_hFinite_iff_infinite {x : ℕ*} : ¬ HFinite x ↔ Infinite x := by simp [HFinite]

/-- Standard hypernaturals are HFinite. -/
@[simp] lemma hFinite_coe (n : ℕ) : HFinite (n : ℕ*) := by
  intro h
  exact (lt_irrefl (n : ℕ*)) (h n)

/-- Zero is HFinite. -/
@[simp] lemma hFinite_zero : HFinite (0 : ℕ*) := hFinite_coe 0

/-- One is HFinite. -/
@[simp] lemma hFinite_one : HFinite (1 : ℕ*) := hFinite_coe 1

/-- Sum of HFinite hypernaturals is HFinite. -/
lemma HFinite.add {x y : ℕ*} (hx : HFinite x) (hy : HFinite y) : HFinite (x + y) :=
  not_infinite_add hx hy

/-- Product of HFinite hypernaturals is HFinite. -/
lemma HFinite.mul {x y : ℕ*} (hx : HFinite x) (hy : HFinite y) : HFinite (x * y) := by
  intro hinf
  rcases exists_st_of_not_infinite hx with ⟨r, hr⟩
  rcases exists_st_of_not_infinite hy with ⟨s, hs⟩
  subst hr; subst hs
  have : (r * s : ℕ*) < (r * s : ℕ*) := hinf (r * s)
  exact lt_irrefl _ this

/-- HFinite respects order: if x ≤ y and y is HFinite, then x is HFinite. -/
lemma HFinite.of_le {x y : ℕ*} (hxy : x ≤ y) (hy : HFinite y) : HFinite x := by
  intro hinf
  apply hy
  intro n
  exact lt_of_lt_of_le (hinf n) hxy

/-- Infinitely close relation: two hypernaturals are infinitely close if they are equal. -/
def InfClose (x y : ℕ*) : Prop := x = y

@[inherit_doc] scoped infixl:50 " ≈ " => InfClose

/-- Infinitely close is reflexive. -/
@[refl, simp] lemma infClose_refl (x : ℕ*) : x ≈ x := rfl

/-- Infinitely close is symmetric. -/
@[symm] lemma infClose_symm {x y : ℕ*} (h : x ≈ y) : y ≈ x := h.symm

/-- Infinitely close is transitive. -/
@[trans] lemma infClose_trans {x y z : ℕ*} (hxy : x ≈ y) (hyz : y ≈ z) : x ≈ z := hxy.trans hyz

/-- For hypernaturals, infinitely close means equal (since there are no infinitesimals in ℕ*). -/
lemma infClose_iff_eq {x y : ℕ*} : x ≈ y ↔ x = y := Iff.rfl

/-- Monad of a hypernatural: the set of all hypernaturals infinitely close to it. -/
def monad (x : ℕ*) : Set ℕ* := {y | x ≈ y}

/-- Galaxy of a hypernatural: for naturals, it's the set of all HFinite hypernaturals. -/
def galaxy (x : ℕ*) : Set ℕ* := {y | HFinite x ∧ HFinite y}

lemma mem_monad_iff {x y : ℕ*} : y ∈ monad x ↔ x ≈ y := Iff.rfl

lemma mem_galaxy_iff {x y : ℕ*} : y ∈ galaxy x ↔ (HFinite x ∧ HFinite y) := Iff.rfl

/-- For hypernaturals, the monad is just the singleton set. -/
lemma monad_eq_singleton {x : ℕ*} : monad x = {x} := by
  ext y
  simp [monad, InfClose]

/-- A hypernatural is in its own monad. -/
@[simp] lemma self_mem_monad (x : ℕ*) : x ∈ monad x := infClose_refl x

/-- A hypernatural is in its own galaxy if it is HFinite. -/
lemma self_mem_galaxy_of_hFinite {x : ℕ*} (hx : HFinite x) : x ∈ galaxy x := by
  simp only [galaxy, Set.mem_setOf_eq]
  exact And.intro hx hx

/-- If both x and y are HFinite, then y is in the galaxy of x. -/
lemma HFinite.mem_galaxy {x y : ℕ*} (hx : HFinite x) (hy : HFinite y) : y ∈ galaxy x := by
  simp only [galaxy, Set.mem_setOf_eq]
  exact And.intro hx hy

/-- Omega is not HFinite. -/
lemma not_hFinite_omega : ¬ HFinite ω := by
  intro h
  exact h infinite_omega

/-- HFinite hypernaturals have a standard part. -/
lemma hFinite_iff_exists_st {x : ℕ*} : HFinite x ↔ ∃ n : ℕ, IsSt x n := by
  simp [HFinite]
  exact exists_st_iff_not_infinite.symm

/-- Monotonicity: if x ≤ y and both are HFinite, then st x ≤ st y. -/
lemma st_monotone {x y : ℕ*} (hx : HFinite x) (hy : HFinite y) (hxy : x ≤ y) : st x ≤ st y :=
  st_le_of_le hx hy hxy

/-- Standard part of sum equals sum of standard parts for HFinite numbers. -/
lemma st_add {x y : ℕ*} (hx : HFinite x) (hy : HFinite y) : st (x + y) = st x + st y := by
  have hx' := isSt_st_of_not_infinite hx
  have hy' := isSt_st_of_not_infinite hy
  exact (hx'.add hy').st_eq

/-- Standard part of zero is zero. -/
@[simp] lemma st_zero : st (0 : ℕ*) = 0 := st_coe 0

/-- Standard part of one is one. -/
@[simp] lemma st_one : st (1 : ℕ*) = 1 := st_coe 1

/-- Standard part is idempotent on standard hypernaturals. -/
@[simp] lemma st_st {n : ℕ} : st (st (n : ℕ*) : ℕ*) = st (n : ℕ*) := by
  simp

/-- HFinite is closed under min. -/
lemma HFinite.min {x y : ℕ*} (hx : HFinite x) (_hy : HFinite y) : HFinite (min x y) :=
  HFinite.of_le (min_le_left x y) hx

/-- For HFinite x and y, if x < y then st x ≤ st y. -/
lemma st_le_of_lt {x y : ℕ*} (hx : HFinite x) (hy : HFinite y) (hxy : x < y) : st x ≤ st y :=
  st_monotone hx hy (le_of_lt hxy)

/-! ### Hypernatural successor (nonstandard extension of Suc) -/

/-- Hypernatural successor: nonstandard extension of `Nat.succ`. -/
noncomputable def hSuc (x : ℕ*) : ℕ* := x + 1

@[simp] lemma hSuc_coe (n : ℕ) : hSuc (n : ℕ*) = ((n + 1) : ℕ*) := rfl

lemma hSuc_eq_add_one (x : ℕ*) : hSuc x = x + 1 := rfl

/-- If x is HFinite, hSuc x is HFinite. -/
lemma HFinite.hSuc {x : ℕ*} (hx : HFinite x) : HFinite (hSuc x) := by
  rw [hSuc_eq_add_one]
  exact hx.add hFinite_one

/-! ### Closure properties for Infinite and HFinite -/

/-- If x is infinite and x ≤ y, then y is infinite (upward closure). -/
lemma Infinite.of_le {x y : ℕ*} (hx : Infinite x) (hle : x ≤ y) : Infinite y := by
  intro n
  exact lt_of_lt_of_le (hx n) hle

/-- Downward closure: If y is HFinite and x ≤ y, then x is HFinite. -/
lemma HFinite.of_le' {x y : ℕ*} (hy : HFinite y) (hle : x ≤ y) : HFinite x :=
  HFinite.of_le hle hy

/-- Maximum of two HFinite hypernaturals is HFinite. -/
lemma HFinite.max {x y : ℕ*} (hx : HFinite x) (hy : HFinite y) : HFinite (max x y) := by
  by_cases h : x ≤ y
  · simpa [max_eq_right h] using hy
  · push_neg at h
    simpa [max_eq_left (le_of_lt h)] using hx

/-! ### Transfer principles -/

/-- Coercion commutes with min. -/
@[simp] lemma coe_min (a b : ℕ) : ((min a b : ℕ) : ℕ*) = min (a : ℕ*) (b : ℕ*) := by
  by_cases h : a ≤ b
  · simp [Nat.min_eq_left h, min_eq_left (coe_le_coe.mpr h)]
  · push_neg at h
    simp [Nat.min_eq_right (le_of_lt h), min_eq_right (coe_le_coe.mpr (le_of_lt h))]

/-- Coercion commutes with max. -/
@[simp] lemma coe_max (a b : ℕ) : ((max a b : ℕ) : ℕ*) = max (a : ℕ*) (b : ℕ*) := by
  by_cases h : a ≤ b
  · simp [Nat.max_eq_right h, max_eq_right (coe_le_coe.mpr h)]
  · push_neg at h
    simp [Nat.max_eq_left (le_of_lt h), max_eq_left (coe_le_coe.mpr (le_of_lt h))]

/-- Every HFinite hypernatural is bounded by some standard natural. -/
lemma exists_coe_ge_of_hFinite {x : ℕ*} (hx : HFinite x) : ∃ n : ℕ, x ≤ n := by
  rcases exists_st_of_not_infinite hx with ⟨n, hn⟩
  exact ⟨n, le_of_eq hn⟩

/-- A hypernatural is infinite iff it exceeds every standard natural. -/
lemma infinite_iff_forall_coe_lt {x : ℕ*} : Infinite x ↔ ∀ n : ℕ, (n : ℕ*) < x := Iff.rfl

/-- A hypernatural is HFinite iff it's bounded by some standard natural. -/
lemma hFinite_iff_exists_coe_ge {x : ℕ*} : HFinite x ↔ ∃ n : ℕ, x ≤ n := by
  constructor
  · exact exists_coe_ge_of_hFinite
  · intro ⟨n, hn⟩
    exact HFinite.of_le hn (hFinite_coe n)

/-! ### Standard hypernaturals (Isabelle's Nats set) -/

/-- The set of standard hypernaturals: those equal to some standard natural. -/
def Standard : Set ℕ* := Set.range (ofNat)

/-- Standard hypernaturals are exactly those with a standard part. -/
lemma mem_standard_iff {x : ℕ*} : x ∈ Standard ↔ ∃ n : ℕ, x = n := by
  constructor
  · intro ⟨n, hn⟩; exact ⟨n, hn.symm⟩
  · intro ⟨n, hn⟩; exact ⟨n, hn.symm⟩

/-- A standard hypernatural is HFinite. -/
lemma HFinite.of_mem_standard {x : ℕ*} (hx : x ∈ Standard) : HFinite x := by
  rcases mem_standard_iff.mp hx with ⟨n, rfl⟩
  exact hFinite_coe n

/-- An infinite hypernatural is not standard. -/
lemma Infinite.not_mem_standard {x : ℕ*} (hx : Infinite x) : x ∉ Standard := by
  intro hmem
  rcases mem_standard_iff.mp hmem with ⟨n, rfl⟩
  exact (hFinite_coe n) hx

/-- Not standard iff infinite (alternative characterization). -/
lemma not_mem_standard_iff_infinite {x : ℕ*} : x ∉ Standard ↔ Infinite x := by
  constructor
  · intro hnot
    by_contra hfin
    rcases exists_st_of_not_infinite hfin with ⟨n, hn⟩
    exact hnot ⟨n, hn.symm⟩
  · exact Infinite.not_mem_standard

/-- Standard hypernaturals are downward closed: if x is standard and y ≤ x, then y is standard. -/
lemma Standard.downward_closed {x y : ℕ*} (hx : x ∈ Standard) (hle : y ≤ x) : y ∈ Standard := by
  by_contra hy
  rw [not_mem_standard_iff_infinite] at hy
  rcases mem_standard_iff.mp hx with ⟨n, rfl⟩
  have : (n : ℕ*) < y := hy n
  exact (not_lt.mpr hle) this

/-- Zero is standard. -/
@[simp] lemma zero_mem_standard : (0 : ℕ*) ∈ Standard := ⟨0, rfl⟩

/-- One is standard. -/
@[simp] lemma one_mem_standard : (1 : ℕ*) ∈ Standard := ⟨1, rfl⟩

/-- A coerced natural is standard. -/
@[simp] lemma coe_mem_standard (n : ℕ) : (n : ℕ*) ∈ Standard := ⟨n, rfl⟩

/-- Omega is not standard. -/
lemma omega_not_mem_standard : ω ∉ Standard := Infinite.not_mem_standard infinite_omega

/-! ### Closure properties for Infinite -/

/-- Adding anything to an infinite hypernatural gives an infinite result. -/
lemma Infinite.add_right {x : ℕ*} (hx : Infinite x) (y : ℕ*) : Infinite (x + y) := by
  intro n
  have h1 : (n : ℕ*) < x := hx n
  have h2 : x ≤ x + y := by
    rcases ofSeq_surjective x with ⟨f, rfl⟩
    rcases ofSeq_surjective y with ⟨g, rfl⟩
    apply (ofSeq_le_ofSeq (f := f) (g := fun i => f i + g i)).2
    filter_upwards with i
    exact Nat.le_add_right (f i) (g i)
  exact lt_of_lt_of_le h1 h2

/-- Adding an infinite hypernatural on the left gives an infinite result. -/
lemma Infinite.add_left {y : ℕ*} (hy : Infinite y) (x : ℕ*) : Infinite (x + y) := by
  rw [add_comm]
  exact hy.add_right x

/-- Adding omega on the right is infinite. -/
@[simp] lemma infinite_add_omega (x : ℕ*) : Infinite (x + ω) := infinite_omega.add_left x

/-- Adding omega on the left is infinite. -/
@[simp] lemma infinite_omega_add (x : ℕ*) : Infinite (ω + x) := infinite_omega.add_right x

/-- Multiplying a positive infinite by a positive hypernatural gives infinite. -/
lemma Infinite.mul_pos {x y : ℕ*} (hx : Infinite x) (hy : 0 < y) : Infinite (x * y) := by
  intro n
  rcases ofSeq_surjective y with ⟨f, rfl⟩
  rcases ofSeq_surjective x with ⟨g, rfl⟩
  have hy' : ∀ᶠ i in nonstandardUltrafilter ℕ, 0 < f i :=
    (ofSeq_lt_ofSeq (f := fun _ => 0) (g := f)).1 (by simpa [ofSeq_const] using hy)
  have hx' : ∀ᶠ i in nonstandardUltrafilter ℕ, n < g i :=
    (ofSeq_lt_ofSeq (f := fun _ => n) (g := g)).1 (by simpa [ofSeq_const] using hx n)
  apply (ofSeq_lt_ofSeq (f := fun _ => n) (g := fun i => g i * f i)).2
  filter_upwards [hx', hy'] with i hni hfi
  have hfi1 : 1 ≤ f i := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hfi)
  calc n = n * 1 := (Nat.mul_one n).symm
       _ ≤ n * f i := Nat.mul_le_mul_left n hfi1
       _ < g i * f i := Nat.mul_lt_mul_of_pos_right hni hfi

/-- ω * ω is infinite. -/
@[simp] lemma infinite_omega_mul_omega : Infinite (ω * ω) := infinite_omega.mul_pos omega_pos

/-! ### More omega lemmas -/

/-- Any standard natural is less than omega. -/
@[simp] lemma coe_lt_omega (n : ℕ) : (n : ℕ*) < ω := infinite_omega n

/-- Any standard natural is at most omega. -/
@[simp] lemma coe_le_omega (n : ℕ) : (n : ℕ*) ≤ ω := le_of_lt (coe_lt_omega n)

/-- Zero is less than omega. -/
@[simp] lemma zero_lt_omega : (0 : ℕ*) < ω := omega_pos

/-- One is less than omega. -/
@[simp] lemma one_lt_omega : (1 : ℕ*) < ω := coe_lt_omega 1

/-- One is at most omega. -/
@[simp] lemma one_le_omega : (1 : ℕ*) ≤ ω := coe_le_omega 1

/-- hSuc of omega is infinite. -/
@[simp] lemma infinite_hSuc_omega : Infinite (hSuc ω) := by
  rw [hSuc_eq_add_one]
  exact infinite_omega.add_right 1

/-- Omega is positive. -/
lemma omega_pos' : ω > 0 := omega_pos

/-- Standard naturals are less than any infinite hypernatural. -/
lemma coe_lt_of_infinite {x : ℕ*} (hx : Infinite x) (n : ℕ) : (n : ℕ*) < x := hx n

/-- Standard naturals are at most any infinite hypernatural. -/
lemma coe_le_of_infinite {x : ℕ*} (hx : Infinite x) (n : ℕ) : (n : ℕ*) ≤ x :=
  le_of_lt (coe_lt_of_infinite hx n)

/-! ### HNatInfinite characterization (Isabelle style) -/

/-- Characterization: x is infinite iff no standard natural equals it. -/
lemma infinite_iff_ne_coe {x : ℕ*} : Infinite x ↔ ∀ n : ℕ, x ≠ n := by
  constructor
  · intro hx n heq
    have : (n : ℕ*) < x := hx n
    rw [heq] at this
    exact lt_irrefl _ this
  · intro hne
    by_contra hfin
    rcases exists_st_of_not_infinite hfin with ⟨n, hn⟩
    exact hne n hn

/-- Characterization: x is HFinite iff it equals some standard natural. -/
lemma hFinite_iff_eq_coe {x : ℕ*} : HFinite x ↔ ∃ n : ℕ, x = n := by
  simp [HFinite, infinite_iff_ne_coe, not_forall]

/-- An infinite hypernatural can be written as y + 1 for some y. -/
lemma Infinite.exists_pred {x : ℕ*} (hx : Infinite x) : ∃ y : ℕ*, x = y + 1 := by
  have h0 : 0 < x := hx 0
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  have hf : ∀ᶠ i in nonstandardUltrafilter ℕ, 0 < f i := (ofSeq_lt_ofSeq (f := fun _ => 0) (g := f)).1
    (by simpa [ofSeq_const] using h0)
  use ofSeq (fun i => f i - 1)
  apply (ofSeq_eq_ofSeq (f := f) (g := fun i => (f i - 1) + 1)).2
  filter_upwards [hf] with i hi
  exact (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hi))).symm

/-- Standard part of multiplication for HFinite numbers. -/
lemma st_mul {x y : ℕ*} (hx : HFinite x) (hy : HFinite y) : st (x * y) = st x * st y := by
  have hx' : x = (st x : ℕ*) := isSt_st_of_not_infinite hx
  have hy' : y = (st y : ℕ*) := isSt_st_of_not_infinite hy
  conv_lhs => rw [hx', hy']
  rw [← coe_mul]
  exact st_coe _

/-! ### Standard set closure properties -/

/-- Sum of standard hypernaturals is standard. -/
lemma Standard.add {x y : ℕ*} (hx : x ∈ Standard) (hy : y ∈ Standard) : x + y ∈ Standard := by
  rcases mem_standard_iff.mp hx with ⟨m, rfl⟩
  rcases mem_standard_iff.mp hy with ⟨n, rfl⟩
  exact ⟨m + n, rfl⟩

/-- Product of standard hypernaturals is standard. -/
lemma Standard.mul {x y : ℕ*} (hx : x ∈ Standard) (hy : y ∈ Standard) : x * y ∈ Standard := by
  rcases mem_standard_iff.mp hx with ⟨m, rfl⟩
  rcases mem_standard_iff.mp hy with ⟨n, rfl⟩
  exact ⟨m * n, rfl⟩

/-- Standard hypernaturals are exactly HFinite ones. -/
lemma mem_standard_iff_hFinite {x : ℕ*} : x ∈ Standard ↔ HFinite x := by
  rw [mem_standard_iff, hFinite_iff_eq_coe]

/-! ### Powers of omega -/

/-- Power of an infinite hypernatural by a positive natural is infinite. -/
lemma Infinite.pow {x : ℕ*} (hx : Infinite x) {n : ℕ} (hn : 0 < n) : Infinite (x ^ n) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn' : n = 0
    · simp only [hn', zero_add, pow_one]
      exact hx
    · rw [pow_succ]
      have hxn : Infinite (x ^ n) := ih (Nat.pos_of_ne_zero hn')
      exact hxn.mul_pos (hx 0)

/-- ω^n is infinite for any positive n. -/
@[simp] lemma infinite_omega_pow {n : ℕ} (hn : 0 < n) : Infinite (ω ^ n) :=
  infinite_omega.pow hn

/-- ω² is infinite. -/
@[simp] lemma infinite_omega_sq : Infinite (ω ^ 2) := infinite_omega_pow (by norm_num)

/-! ### Sequence arithmetic -/

/-- Addition of sequences corresponds to addition of hypernaturals. -/
theorem ofSeq_add (f g : ℕ → ℕ) : ofSeq f + ofSeq g = ofSeq (f + g) := rfl

/-- Multiplication of sequences corresponds to multiplication of hypernaturals. -/
theorem ofSeq_mul (f g : ℕ → ℕ) : ofSeq f * ofSeq g = ofSeq (f * g) := rfl

/-- Power of a sequence. -/
theorem ofSeq_pow (f : ℕ → ℕ) (n : ℕ) : ofSeq f ^ n = ofSeq (f ^ n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ, ih, ofSeq_mul]

/-- Zero sequence gives zero. -/
@[simp] theorem ofSeq_zero : ofSeq 0 = 0 := rfl

/-- One sequence gives one. -/
@[simp] theorem ofSeq_one : ofSeq 1 = 1 := rfl

/-! ### Coercion and power -/

/-- Coercion commutes with power. -/
@[simp, norm_cast] theorem coe_pow (a : ℕ) (n : ℕ) : ((a ^ n : ℕ) : ℕ*) = (a : ℕ*) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ, coe_mul, ih]

/-- HFinite is closed under power. -/
lemma HFinite.pow {x : ℕ*} (hx : HFinite x) (n : ℕ) : HFinite (x ^ n) := by
  induction n with
  | zero => simp only [pow_zero]; exact hFinite_one
  | succ n ih => simp only [pow_succ]; exact ih.mul hx

/-- Standard part of power for HFinite numbers. -/
lemma st_pow {x : ℕ*} (hx : HFinite x) (n : ℕ) : st (x ^ n) = st x ^ n := by
  induction n with
  | zero => simp only [pow_zero, st_one]
  | succ n ih =>
    simp only [pow_succ]
    rw [st_mul (hx.pow n) hx, ih]

/-! ### Omega arithmetic -/

/-- 2 * ω is infinite. -/
@[simp] lemma infinite_two_mul_omega : Infinite (2 * ω) := by
  intro n
  have : (n : ℕ*) < ofSeq (fun i => 2 * i) := by
    apply (ofSeq_lt_ofSeq (f := fun _ => n) (g := fun i => 2 * i)).2
    apply nonstandardUltrafilter_le_atTop
    filter_upwards [Filter.eventually_gt_atTop n] with i hi
    omega
  have h2ω : (2 : ℕ*) * ω = ofSeq (fun i => 2 * i) := by
    simp only [omega]
    rfl
  rw [h2ω]
  exact this

/-- ω + ω = 2 * ω. -/
lemma omega_add_omega : ω + ω = 2 * ω := by
  simp only [omega, ofSeq_add]
  have h2ω : (2 : ℕ*) * ofSeq Nat.cast = ofSeq (fun i => 2 * i) := by
    rfl
  rw [h2ω]
  congr 1
  ext i
  simp only [Pi.add_apply, Nat.cast_id]
  ring

/-- ω + ω is infinite. -/
@[simp] lemma infinite_omega_add_omega : Infinite (ω + ω) := by
  rw [omega_add_omega]
  exact infinite_two_mul_omega

/-- n * ω is infinite for n > 0. -/
lemma infinite_coe_mul_omega {n : ℕ} (hn : 0 < n) : Infinite ((n : ℕ*) * ω) := by
  intro m
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  have hnω : (n : ℕ*) * ω = ofSeq (fun i => n * i) := by
    simp only [omega]
    rfl
  rw [hnω]
  apply (ofSeq_lt_ofSeq (f := fun _ => m) (g := fun i => n * i)).2
  apply nonstandardUltrafilter_le_atTop
  filter_upwards [Filter.eventually_gt_atTop m] with i hi
  calc m < i := hi
       _ = 1 * i := (one_mul i).symm
       _ ≤ n * i := Nat.mul_le_mul_right i hn1

/-- ω * n is infinite for n > 0. -/
lemma infinite_omega_mul_coe {n : ℕ} (hn : 0 < n) : Infinite (ω * (n : ℕ*)) := by
  intro m
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  have hωn : ω * (n : ℕ*) = ofSeq (fun i => i * n) := by
    simp only [omega]
    rfl
  rw [hωn]
  apply (ofSeq_lt_ofSeq (f := fun _ => m) (g := fun i => i * n)).2
  apply nonstandardUltrafilter_le_atTop
  filter_upwards [Filter.eventually_gt_atTop m] with i hi
  calc m < i := hi
       _ = i * 1 := (Nat.mul_one i).symm
       _ ≤ i * n := Nat.mul_le_mul_left i hn1

/-! ### Trichotomy and decidability -/

/-- Every hypernatural is either standard or infinite (no third option). -/
lemma standard_or_infinite (x : ℕ*) : x ∈ Standard ∨ Infinite x := by
  by_cases h : Infinite x
  · exact Or.inr h
  · exact Or.inl (mem_standard_iff_hFinite.mpr h)

/-- A hypernatural is standard iff it is not infinite. -/
lemma mem_standard_iff_not_infinite {x : ℕ*} : x ∈ Standard ↔ ¬ Infinite x :=
  mem_standard_iff_hFinite

/-- Two standard hypernaturals are equal iff their standard parts are equal. -/
lemma eq_of_st_eq {x y : ℕ*} (hx : HFinite x) (hy : HFinite y) (h : st x = st y) : x = y := by
  have hx' : x = (st x : ℕ*) := isSt_st_of_not_infinite hx
  have hy' : y = (st y : ℕ*) := isSt_st_of_not_infinite hy
  rw [hx', hy', h]

/-! ### Strict positivity -/

/-- A hypernatural is positive iff it's eventually positive. -/
lemma pos_iff_ofSeq_pos {f : ℕ → ℕ} : 0 < ofSeq f ↔ ∀ᶠ n in nonstandardUltrafilter ℕ, 0 < f n :=
  ofSeq_lt_ofSeq (f := fun _ => 0) (g := f)

/-- Every infinite hypernatural is positive. -/
lemma Infinite.pos {x : ℕ*} (hx : Infinite x) : 0 < x := hx 0

/-! ### Comparisons between standard and infinite -/

/-- Standard is strictly less than infinite. -/
lemma standard_lt_infinite {x y : ℕ*} (hx : x ∈ Standard) (hy : Infinite y) : x < y := by
  rcases mem_standard_iff.mp hx with ⟨n, rfl⟩
  exact hy n

/-- Standard is at most infinite. -/
lemma standard_le_infinite {x y : ℕ*} (hx : x ∈ Standard) (hy : Infinite y) : x ≤ y :=
  le_of_lt (standard_lt_infinite hx hy)

/-- If x < y and y is standard, then x is standard. -/
lemma standard_of_lt {x y : ℕ*} (hxy : x < y) (hy : y ∈ Standard) : x ∈ Standard := by
  rcases mem_standard_iff.mp hy with ⟨n, rfl⟩
  by_contra hx
  rw [not_mem_standard_iff_infinite] at hx
  have : (n : ℕ*) ≤ x := coe_le_of_infinite hx n
  exact (lt_irrefl x) (lt_of_lt_of_le hxy this)

/-! ### Factorial -/

/-- Hypernatural factorial: extension of factorial to hypernaturals. -/
noncomputable def factorial (x : ℕ*) : ℕ* :=
  Quot.liftOn x (fun f => ofSeq (fun n => Nat.factorial (f n)))
    (fun f g hfg => by
      apply ofSeq_eq_ofSeq.mpr
      filter_upwards [hfg] with n hn
      rw [hn])

/-- Factorial of a standard natural. -/
@[simp] lemma factorial_coe (n : ℕ) : factorial (n : ℕ*) = (Nat.factorial n : ℕ*) := rfl

/-- Factorial of zero is one. -/
@[simp] lemma factorial_zero : factorial (0 : ℕ*) = 1 := by rfl

/-- Factorial of one is one. -/
@[simp] lemma factorial_one : factorial (1 : ℕ*) = 1 := by rfl

/-- Factorial is always positive. -/
lemma factorial_pos (x : ℕ*) : 0 < factorial x := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  apply (ofSeq_lt_ofSeq (f := fun _ => 0) (g := fun n => Nat.factorial (f n))).2
  filter_upwards with n
  exact Nat.factorial_pos (f n)

/-- Factorial of omega is infinite. -/
@[simp] lemma infinite_factorial_omega : Infinite (factorial ω) := by
  intro m
  simp only [omega, factorial]
  apply (ofSeq_lt_ofSeq (f := fun _ => m) (g := fun n => Nat.factorial n)).2
  apply nonstandardUltrafilter_le_atTop
  filter_upwards [Filter.eventually_gt_atTop m] with i hi
  calc m < i := hi
       _ ≤ Nat.factorial i := Nat.self_le_factorial i

/-- Factorial of an infinite hypernatural is infinite. -/
lemma Infinite.factorial {x : ℕ*} (hx : Infinite x) : Infinite (factorial x) := by
  intro m
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  change (m : ℕ*) < ofSeq (fun n => Nat.factorial (f n))
  apply (ofSeq_lt_ofSeq (f := fun _ => m) (g := fun n => Nat.factorial (f n))).2
  have hf : ∀ᶠ n in nonstandardUltrafilter ℕ, m < f n :=
    (ofSeq_lt_ofSeq (f := fun _ => m) (g := f)).1 (hx m)
  filter_upwards [hf] with n hn
  calc m < f n := hn
       _ ≤ Nat.factorial (f n) := Nat.self_le_factorial (f n)

/-- Factorial is HFinite on HFinite inputs. -/
lemma HFinite.factorial {x : ℕ*} (hx : HFinite x) : HFinite (factorial x) := by
  rcases exists_st_of_not_infinite hx with ⟨n, hn⟩
  subst hn
  simp only [factorial_coe]
  exact hFinite_coe _

/-- Standard part of factorial. -/
lemma st_factorial {x : ℕ*} (hx : HFinite x) : st (factorial x) = Nat.factorial (st x) := by
  have hx' : x = (st x : ℕ*) := isSt_st_of_not_infinite hx
  conv_lhs => rw [hx']
  simp only [factorial_coe, st_coe]

/-! ### Additional ordering lemmas -/

/-- Strict monotonicity: x < y implies x + z < y + z for any z. -/
lemma add_lt_add_right {x y z : ℕ*} (h : x < y) : x + z < y + z := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rcases ofSeq_surjective y with ⟨g, rfl⟩
  rcases ofSeq_surjective z with ⟨k, rfl⟩
  simp only [ofSeq_add]
  apply (ofSeq_lt_ofSeq (f := fun n => f n + k n) (g := fun n => g n + k n)).2
  have hfg : ∀ᶠ n in nonstandardUltrafilter ℕ, f n < g n := ofSeq_lt_ofSeq.mp h
  filter_upwards [hfg] with n hn
  exact Nat.add_lt_add_right hn (k n)

/-- Strict monotonicity: x < y implies z + x < z + y for any z. -/
lemma add_lt_add_left {x y z : ℕ*} (h : x < y) : z + x < z + y := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rcases ofSeq_surjective y with ⟨g, rfl⟩
  rcases ofSeq_surjective z with ⟨k, rfl⟩
  simp only [ofSeq_add]
  apply (ofSeq_lt_ofSeq (f := fun n => k n + f n) (g := fun n => k n + g n)).2
  have hfg : ∀ᶠ n in nonstandardUltrafilter ℕ, f n < g n := ofSeq_lt_ofSeq.mp h
  filter_upwards [hfg] with n hn
  exact Nat.add_lt_add_left hn (k n)

/-- Multiplication by positive preserves strict order. -/
lemma mul_lt_mul_of_pos_right {x y z : ℕ*} (hxy : x < y) (hz : 0 < z) : x * z < y * z := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rcases ofSeq_surjective y with ⟨g, rfl⟩
  rcases ofSeq_surjective z with ⟨k, rfl⟩
  simp only [ofSeq_mul]
  apply (ofSeq_lt_ofSeq (f := fun n => f n * k n) (g := fun n => g n * k n)).2
  have hfg : ∀ᶠ n in nonstandardUltrafilter ℕ, f n < g n := ofSeq_lt_ofSeq.mp hxy
  have hk : ∀ᶠ n in nonstandardUltrafilter ℕ, 0 < k n := ofSeq_lt_ofSeq.mp hz
  filter_upwards [hfg, hk] with n hn hkn
  exact Nat.mul_lt_mul_of_pos_right hn hkn

/-- Nonnegativity: every hypernatural is nonnegative. -/
@[simp] lemma zero_le (x : ℕ*) : 0 ≤ x := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  apply (ofSeq_le_ofSeq (f := fun _ => 0) (g := f)).2
  filter_upwards with n
  exact Nat.zero_le (f n)

/-- Not less than zero. -/
@[simp] lemma not_lt_zero (x : ℕ*) : ¬ x < 0 := not_lt.mpr (zero_le x)

/-! ### Conversion lemmas -/

/-- A hypernatural equals a standard natural iff they're equal. -/
lemma eq_coe_iff {x : ℕ*} {n : ℕ} : x = n ↔ ∃ m : ℕ, x = m ∧ m = n := by
  constructor
  · intro h; exact ⟨n, h, rfl⟩
  · intro ⟨m, hx, hm⟩; rw [hx, hm]

/-- Omega is not equal to any standard natural. -/
lemma omega_ne_coe (n : ℕ) : ω ≠ n := by
  intro h
  have : Infinite ω := infinite_omega
  rw [h] at this
  exact (hFinite_coe n) this

/-- No standard natural equals omega. -/
lemma coe_ne_omega (n : ℕ) : (n : ℕ*) ≠ ω := (omega_ne_coe n).symm

/-! ### Successor -/

/-- Hypernatural successor: x + 1 -/
noncomputable def succ (x : ℕ*) : ℕ* := x + 1

/-- Successor preserves sequences. -/
lemma succ_ofSeq (f : ℕ → ℕ) : succ (ofSeq f) = ofSeq (fun n => f n + 1) := rfl

/-- Successor of a standard natural. -/
@[simp] lemma succ_coe (n : ℕ) : succ (n : ℕ*) = (n + 1 : ℕ*) := rfl

/-- succ is strictly increasing. -/
lemma lt_succ_self (x : ℕ*) : x < succ x := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  simp only [succ_ofSeq]
  apply (ofSeq_lt_ofSeq (f := f) (g := fun n => f n + 1)).2
  filter_upwards with n
  exact Nat.lt_succ_self (f n)

/-- succ is always positive. -/
lemma succ_pos (x : ℕ*) : 0 < succ x := by
  calc 0 ≤ x := zero_le x
       _ < succ x := lt_succ_self x

/-- Successor of omega is infinite. -/
@[simp] lemma infinite_succ_omega : Infinite (succ ω) := Infinite.add_right infinite_omega 1

/-- Successor of an infinite is infinite. -/
lemma Infinite.succ {x : ℕ*} (hx : Infinite x) : Infinite (succ x) := Infinite.add_right hx 1

/-- Successor of HFinite is HFinite. -/
lemma HFinite.succ {x : ℕ*} (hx : HFinite x) : HFinite (succ x) := by
  rcases exists_st_of_not_infinite hx with ⟨n, rfl⟩
  change HFinite ((n : ℕ*) + 1)
  rw [← Nat.cast_one, ← Nat.cast_add]
  exact hFinite_coe _

/-- Standard part of successor. -/
lemma st_succ {x : ℕ*} (hx : HFinite x) : st (succ x) = st x + 1 := by
  have hx' : x = (st x : ℕ*) := isSt_st_of_not_infinite hx
  conv_lhs => rw [hx']
  change st ((st x : ℕ*) + 1) = st x + 1
  rw [← Nat.cast_one, ← Nat.cast_add, st_coe]

/-- Injectivity of successor. -/
lemma succ_inj {x y : ℕ*} : succ x = succ y ↔ x = y := by
  constructor
  · intro h
    rcases ofSeq_surjective x with ⟨f, rfl⟩
    rcases ofSeq_surjective y with ⟨g, rfl⟩
    simp only [succ_ofSeq] at h
    apply ofSeq_eq_ofSeq.mpr
    have hfg := ofSeq_eq_ofSeq.mp h
    filter_upwards [hfg] with n hn
    omega
  · intro h; rw [h]

/-! ### Minimum and maximum -/

/-- min ≤ left argument. -/
lemma min_le_left (x y : ℕ*) : Min.min x y ≤ x := _root_.min_le_left x y

/-- min ≤ right argument. -/
lemma min_le_right (x y : ℕ*) : Min.min x y ≤ y := _root_.min_le_right x y

/-- left argument ≤ max. -/
lemma le_max_left (x y : ℕ*) : x ≤ Max.max x y := _root_.le_max_left x y

/-- right argument ≤ max. -/
lemma le_max_right (x y : ℕ*) : y ≤ Max.max x y := _root_.le_max_right x y

/-- max of infinite and anything is infinite. -/
lemma Infinite.max_left {x : ℕ*} (hx : Infinite x) (y : ℕ*) : Infinite (Max.max x y) := by
  intro m
  calc (m : ℕ*) < x := hx m
       _ ≤ Max.max x y := le_max_left x y

/-- max with infinite is infinite. -/
lemma Infinite.max_right {y : ℕ*} (hy : Infinite y) (x : ℕ*) : Infinite (Max.max x y) := by
  rw [_root_.max_comm]
  exact hy.max_left x

/-! ### GCD and LCM -/

/-- Hypernatural GCD: lifted pointwise from naturals. -/
noncomputable def gcd (x y : ℕ*) : ℕ* :=
  Quotient.liftOn₂ x y (fun f g => ofSeq (fun n => Nat.gcd (f n) (g n)))
    (fun f₁ f₂ g₁ g₂ hf hg => by
      apply ofSeq_eq_ofSeq.mpr
      filter_upwards [hf, hg] with n hfn hgn
      rw [hfn, hgn])

/-- Hypernatural LCM: lifted pointwise from naturals. -/
noncomputable def lcm (x y : ℕ*) : ℕ* :=
  Quotient.liftOn₂ x y (fun f g => ofSeq (fun n => Nat.lcm (f n) (g n)))
    (fun f₁ f₂ g₁ g₂ hf hg => by
      apply ofSeq_eq_ofSeq.mpr
      filter_upwards [hf, hg] with n hfn hgn
      rw [hfn, hgn])

/-- GCD of standard naturals. -/
@[simp] lemma gcd_coe (m n : ℕ) : gcd (m : ℕ*) (n : ℕ*) = (Nat.gcd m n : ℕ*) := rfl

/-- LCM of standard naturals. -/
@[simp] lemma lcm_coe (m n : ℕ) : lcm (m : ℕ*) (n : ℕ*) = (Nat.lcm m n : ℕ*) := rfl

/-- gcd is commutative. -/
lemma gcd_comm (x y : ℕ*) : gcd x y = gcd y x := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rcases ofSeq_surjective y with ⟨g, rfl⟩
  apply ofSeq_eq_ofSeq.mpr
  filter_upwards with n
  exact Nat.gcd_comm (f n) (g n)

/-- lcm is commutative. -/
lemma lcm_comm (x y : ℕ*) : lcm x y = lcm y x := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rcases ofSeq_surjective y with ⟨g, rfl⟩
  apply ofSeq_eq_ofSeq.mpr
  filter_upwards with n
  exact Nat.lcm_comm (f n) (g n)

/-- GCD divides left argument. -/
lemma gcd_dvd_left (x y : ℕ*) : gcd x y ∣ x := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rcases ofSeq_surjective y with ⟨g, rfl⟩
  use ofSeq (fun n => f n / Nat.gcd (f n) (g n))
  apply ofSeq_eq_ofSeq.mpr
  filter_upwards with n
  rw [Nat.mul_comm]
  exact (Nat.div_mul_cancel (Nat.gcd_dvd_left (f n) (g n))).symm

/-- GCD divides right argument. -/
lemma gcd_dvd_right (x y : ℕ*) : gcd x y ∣ y := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rcases ofSeq_surjective y with ⟨g, rfl⟩
  use ofSeq (fun n => g n / Nat.gcd (f n) (g n))
  apply ofSeq_eq_ofSeq.mpr
  filter_upwards with n
  rw [Nat.mul_comm]
  exact (Nat.div_mul_cancel (Nat.gcd_dvd_right (f n) (g n))).symm

/-- GCD self is self. -/
@[simp] lemma gcd_self (x : ℕ*) : gcd x x = x := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  apply ofSeq_eq_ofSeq.mpr
  filter_upwards with n
  exact Nat.gcd_self (f n)

/-- GCD with zero. -/
@[simp] lemma gcd_zero_right (x : ℕ*) : gcd x 0 = x := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  apply ofSeq_eq_ofSeq.mpr
  filter_upwards with n
  exact Nat.gcd_zero_right (f n)

/-- GCD with zero. -/
@[simp] lemma gcd_zero_left (x : ℕ*) : gcd 0 x = x := by
  rw [gcd_comm, gcd_zero_right]

/-- LCM with zero. -/
@[simp] lemma lcm_zero_right (x : ℕ*) : lcm x 0 = 0 := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  apply ofSeq_eq_ofSeq.mpr
  filter_upwards with n
  exact Nat.lcm_zero_right (f n)

/-- LCM with zero. -/
@[simp] lemma lcm_zero_left (x : ℕ*) : lcm 0 x = 0 := by
  rw [lcm_comm, lcm_zero_right]

/-! ### Decidability and trichotomy -/

/-- Trichotomy for hypernaturals: every hypernatural is either finite or infinite. -/
lemma hFinite_or_infinite (x : ℕ*) : HFinite x ∨ Infinite x := by
  by_cases h : Infinite x
  · right; exact h
  · left; exact h

/-- Comparison with standard: either x < n or n ≤ x. -/
lemma lt_coe_or_le_coe (x : ℕ*) (n : ℕ) : x < n ∨ n ≤ x := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  have hU := Ultrafilter.em (nonstandardUltrafilter ℕ) {m | f m < n}
  cases hU with
  | inl hlt =>
    left
    exact ofSeq_lt_ofSeq.mpr hlt
  | inr hge =>
    right
    apply ofSeq_le_ofSeq.mpr
    have : ∀ᶠ m in nonstandardUltrafilter ℕ, n ≤ f m := by
      convert hge using 1
      ext m
      constructor
      · intro hle hlt; exact (not_le.mpr hlt) hle
      · intro hne; exact le_of_not_gt hne
    exact this

/-- Every hypernatural is either zero or positive. -/
lemma eq_zero_or_pos (x : ℕ*) : x = 0 ∨ 0 < x := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  have hU := Ultrafilter.em (nonstandardUltrafilter ℕ) {m | f m = 0}
  cases hU with
  | inl h =>
    left
    apply ofSeq_eq_ofSeq.mpr
    convert h using 1
  | inr h =>
    right
    apply (ofSeq_lt_ofSeq (f := fun _ => 0) (g := f)).2
    have : ∀ᶠ m in nonstandardUltrafilter ℕ, 0 < f m := by
      convert h using 1
      ext m
      constructor
      · intro hpos heq; rw [heq] at hpos; exact (lt_irrefl 0) hpos
      · intro hne; exact Nat.pos_of_ne_zero hne
    exact this

/-- A hypernatural is positive iff it's not zero. -/
lemma pos_iff_ne_zero {x : ℕ*} : 0 < x ↔ x ≠ 0 := by
  constructor
  · intro h hx
    rw [hx] at h
    exact lt_irrefl 0 h
  · intro h
    cases eq_zero_or_pos x with
    | inl hz => exact absurd hz h
    | inr hp => exact hp

/-! ### Induction principles -/

/-- Induction for HFinite hypernaturals: standard induction works. -/
theorem hFinite_induction {P : ℕ* → Prop}
    (h0 : P 0)
    (hsucc : ∀ n : ℕ, P n → P (n + 1))
    {x : ℕ*} (hx : HFinite x) : P x := by
  rcases exists_st_of_not_infinite hx with ⟨m, rfl⟩
  induction m with
  | zero => exact h0
  | succ k ih => exact hsucc k (ih (hFinite_coe k))

/-- Strong induction for HFinite hypernaturals. -/
theorem hFinite_strong_induction {P : ℕ* → Prop}
    (hind : ∀ n : ℕ, (∀ m : ℕ, m < n → P m) → P n)
    {x : ℕ*} (hx : HFinite x) : P x := by
  rcases exists_st_of_not_infinite hx with ⟨m, rfl⟩
  let P' : ℕ → Prop := fun n => P n
  have hind' : ∀ n : ℕ, (∀ m : ℕ, m < n → P' m) → P' n := hind
  exact Nat.strong_induction_on m hind'

/-- If a property holds for all standard naturals, it holds for all HFinite hypernaturals. -/
theorem forall_standard_of_forall_nat {P : ℕ* → Prop}
    (h : ∀ n : ℕ, P n)
    {x : ℕ*} (hx : HFinite x) : P x := by
  rcases exists_st_of_not_infinite hx with ⟨m, rfl⟩
  exact h m

/-! ### Internal sets and transfer -/

/-- An internal subset of ℕ* is one that can be represented by a sequence of subsets of ℕ. -/
def InternalSet (S : Set ℕ*) : Prop :=
  ∃ A : ℕ → Set ℕ, S = {x | ∃ f, x = ofSeq f ∧ ∀ᶠ n in nonstandardUltrafilter ℕ, f n ∈ A n}

/-- The set of all hypernaturals is internal. -/
lemma internal_univ : InternalSet (Set.univ : Set ℕ*) := by
  use fun _ => Set.univ
  ext x
  simp only [Set.mem_univ, true_iff, Set.mem_setOf_eq]
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  use f
  constructor
  · rfl
  · filter_upwards with n; exact Set.mem_univ (f n)

/-- The empty set is internal. -/
lemma internal_empty : InternalSet (∅ : Set ℕ*) := by
  use fun _ => ∅
  ext x
  simp only [Set.mem_empty_iff_false, false_iff, Set.mem_setOf_eq, not_exists]
  intro f ⟨_, hf⟩
  have : ∀ᶠ n in nonstandardUltrafilter ℕ, f n ∈ (∅ : Set ℕ) := hf
  simp only [Set.mem_empty_iff_false, Filter.eventually_false_iff_eq_bot] at this
  exact Filter.NeBot.ne (nonstandardUltrafilter ℕ).neBot this

/-- Singleton sets of standard naturals are internal. -/
lemma internal_singleton (m : ℕ) : InternalSet ({(m : ℕ*)} : Set ℕ*) := by
  use fun _ => {m}
  ext x
  constructor
  · intro hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    use fun _ => m
    constructor
    · rfl
    · filter_upwards with n; exact Set.mem_singleton m
  · intro ⟨f, hfx, hf⟩
    simp only [Set.mem_singleton_iff]
    rw [hfx]
    apply ofSeq_eq_ofSeq.mpr
    simp only [Set.mem_singleton_iff] at hf
    exact hf

/-! ### Overflow and underspill principles -/

/-- Simplified overflow: omega satisfies any property that holds for all standard naturals,
    provided the property is suitably internal. -/
theorem overflow_omega {P : ℕ → Prop} (hP : ∀ n : ℕ, P n) :
    ∀ᶠ n in nonstandardUltrafilter ℕ, P n := by
  filter_upwards with n
  exact hP n

/-- For sequence-based properties: if P(f(n)) holds for all n, then P holds
    for the hypernatural represented by f. -/
theorem ofSeq_satisfies {P : ℕ → Prop} {f : ℕ → ℕ} (hP : ∀ n : ℕ, P (f n)) :
    ∀ᶠ n in nonstandardUltrafilter ℕ, P (f n) := by
  filter_upwards with n
  exact hP n

/-! ### Truncated subtraction -/

/-- Truncated subtraction for hypernaturals: lifted pointwise from Nat.sub. -/
noncomputable def tsub (x y : ℕ*) : ℕ* :=
  Quotient.liftOn₂ x y (fun f g => ofSeq (fun n => f n - g n))
    (fun f₁ f₂ g₁ g₂ hf hg => by
      apply ofSeq_eq_ofSeq.mpr
      filter_upwards [hf, hg] with n hfn hgn
      rw [hfn, hgn])

/-- Notation for truncated subtraction. -/
noncomputable instance : Sub ℕ* := ⟨tsub⟩

/-- Truncated subtraction of standard naturals. -/
@[simp] lemma tsub_coe (m n : ℕ) : (m : ℕ*) - (n : ℕ*) = ((m - n : ℕ) : ℕ*) := rfl

/-- Truncated subtraction preserves sequences. -/
lemma tsub_ofSeq (f g : ℕ → ℕ) : ofSeq f - ofSeq g = ofSeq (fun n => f n - g n) := rfl

/-- x - 0 = x. -/
@[simp] lemma tsub_zero (x : ℕ*) : x - 0 = x := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  apply ofSeq_eq_ofSeq.mpr
  filter_upwards with n
  exact Nat.sub_zero (f n)

/-- 0 - x = 0. -/
@[simp] lemma zero_tsub (x : ℕ*) : 0 - x = 0 := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  apply ofSeq_eq_ofSeq.mpr
  filter_upwards with n
  exact Nat.zero_sub (f n)

/-- x - x = 0. -/
@[simp] lemma tsub_self (x : ℕ*) : x - x = 0 := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  apply ofSeq_eq_ofSeq.mpr
  filter_upwards with n
  exact Nat.sub_self (f n)

/-- If x ≤ y, then x - y = 0. -/
lemma tsub_eq_zero_of_le {x y : ℕ*} (h : x ≤ y) : x - y = 0 := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rcases ofSeq_surjective y with ⟨g, rfl⟩
  simp only [tsub_ofSeq]
  apply ofSeq_eq_ofSeq.mpr
  have hle : ∀ᶠ n in nonstandardUltrafilter ℕ, f n ≤ g n := ofSeq_le_ofSeq.mp h
  filter_upwards [hle] with n hn
  exact Nat.sub_eq_zero_of_le hn

/-- (x + y) - y = x. -/
lemma add_tsub_cancel_right (x y : ℕ*) : (x + y) - y = x := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rcases ofSeq_surjective y with ⟨g, rfl⟩
  simp only [ofSeq_add, tsub_ofSeq]
  apply ofSeq_eq_ofSeq.mpr
  filter_upwards with n
  exact Nat.add_sub_cancel (f n) (g n)

/-- (x + y) - x = y. -/
lemma add_tsub_cancel_left (x y : ℕ*) : (x + y) - x = y := by
  rw [add_comm]
  exact add_tsub_cancel_right y x

/-- Truncated subtraction is monotone in the first argument. -/
lemma tsub_le_tsub_right {x y : ℕ*} (h : x ≤ y) (z : ℕ*) : x - z ≤ y - z := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rcases ofSeq_surjective y with ⟨g, rfl⟩
  rcases ofSeq_surjective z with ⟨k, rfl⟩
  simp only [tsub_ofSeq]
  apply ofSeq_le_ofSeq.mpr
  have hle : ∀ᶠ n in nonstandardUltrafilter ℕ, f n ≤ g n := ofSeq_le_ofSeq.mp h
  filter_upwards [hle] with n hn
  exact Nat.sub_le_sub_right hn (k n)

/-- Truncated subtraction is antitone in the second argument. -/
lemma tsub_le_tsub_left {y z : ℕ*} (h : y ≤ z) (x : ℕ*) : x - z ≤ x - y := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rcases ofSeq_surjective y with ⟨g, rfl⟩
  rcases ofSeq_surjective z with ⟨k, rfl⟩
  simp only [tsub_ofSeq]
  apply ofSeq_le_ofSeq.mpr
  have hle : ∀ᶠ n in nonstandardUltrafilter ℕ, g n ≤ k n := ofSeq_le_ofSeq.mp h
  filter_upwards [hle] with n hn
  exact Nat.sub_le_sub_left hn (f n)

/-- x - y ≤ x. -/
lemma tsub_le_self (x y : ℕ*) : x - y ≤ x := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rcases ofSeq_surjective y with ⟨g, rfl⟩
  simp only [tsub_ofSeq]
  apply ofSeq_le_ofSeq.mpr
  filter_upwards with n
  exact Nat.sub_le (f n) (g n)

/-- If y ≤ x, then x - y + y = x. -/
lemma tsub_add_cancel_of_le {x y : ℕ*} (h : y ≤ x) : x - y + y = x := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rcases ofSeq_surjective y with ⟨g, rfl⟩
  simp only [tsub_ofSeq, ofSeq_add]
  apply ofSeq_eq_ofSeq.mpr
  have hle : ∀ᶠ n in nonstandardUltrafilter ℕ, g n ≤ f n := ofSeq_le_ofSeq.mp h
  filter_upwards [hle] with n hn
  exact Nat.sub_add_cancel hn

/-- Standard part of tsub for HFinite numbers. -/
lemma st_tsub {x y : ℕ*} (hx : HFinite x) (hy : HFinite y) : st (x - y) = st x - st y := by
  have hx' : x = (st x : ℕ*) := isSt_st_of_not_infinite hx
  have hy' : y = (st y : ℕ*) := isSt_st_of_not_infinite hy
  conv_lhs => rw [hx', hy']
  simp only [tsub_coe, st_coe]

/-- HFinite is closed under tsub. -/
lemma HFinite.tsub {x y : ℕ*} (hx : HFinite x) (_hy : HFinite y) : HFinite (x - y) :=
  HFinite.of_le (tsub_le_self x y) hx

/-! ### Division and modulo -/

/-- Hypernatural division: lifted pointwise from Nat.div. -/
noncomputable def hdiv (x y : ℕ*) : ℕ* :=
  Quotient.liftOn₂ x y (fun f g => ofSeq (fun n => f n / g n))
    (fun f₁ f₂ g₁ g₂ hf hg => by
      apply ofSeq_eq_ofSeq.mpr
      filter_upwards [hf, hg] with n hfn hgn
      rw [hfn, hgn])

/-- Hypernatural modulo: lifted pointwise from Nat.mod. -/
noncomputable def hmod (x y : ℕ*) : ℕ* :=
  Quotient.liftOn₂ x y (fun f g => ofSeq (fun n => f n % g n))
    (fun f₁ f₂ g₁ g₂ hf hg => by
      apply ofSeq_eq_ofSeq.mpr
      filter_upwards [hf, hg] with n hfn hgn
      rw [hfn, hgn])

noncomputable instance : Div ℕ* := ⟨hdiv⟩

noncomputable instance : Mod ℕ* := ⟨hmod⟩

/-- Division of standard naturals. -/
@[simp] lemma hdiv_coe (m n : ℕ) : (m : ℕ*) / (n : ℕ*) = ((m / n : ℕ) : ℕ*) := rfl

/-- Modulo of standard naturals. -/
@[simp] lemma hmod_coe (m n : ℕ) : (m : ℕ*) % (n : ℕ*) = ((m % n : ℕ) : ℕ*) := rfl

/-- Division preserves sequences. -/
lemma hdiv_ofSeq (f g : ℕ → ℕ) : ofSeq f / ofSeq g = ofSeq (fun n => f n / g n) := rfl

/-- Modulo preserves sequences. -/
lemma hmod_ofSeq (f g : ℕ → ℕ) : ofSeq f % ofSeq g = ofSeq (fun n => f n % g n) := rfl

/-- Division by 1 is identity. -/
@[simp] lemma hdiv_one (x : ℕ*) : x / 1 = x := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  apply ofSeq_eq_ofSeq.mpr
  filter_upwards with n
  exact Nat.div_one (f n)

/-- Division by itself gives 1 for nonzero. -/
lemma hdiv_self {x : ℕ*} (hx : x ≠ 0) : x / x = 1 := by
  have hpos : 0 < x := pos_iff_ne_zero.mpr hx
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  apply ofSeq_eq_ofSeq.mpr
  have hne : ∀ᶠ n in nonstandardUltrafilter ℕ, 0 < f n := ofSeq_lt_ofSeq.mp hpos
  filter_upwards [hne] with n hn
  exact Nat.div_self hn

/-- 0 / x = 0. -/
@[simp] lemma zero_hdiv (x : ℕ*) : 0 / x = 0 := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  apply ofSeq_eq_ofSeq.mpr
  filter_upwards with n
  exact Nat.zero_div (f n)

/-- x / 0 = 0. -/
@[simp] lemma hdiv_zero (x : ℕ*) : x / 0 = 0 := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  apply ofSeq_eq_ofSeq.mpr
  filter_upwards with n
  exact Nat.div_zero (f n)

/-- x % 1 = 0. -/
@[simp] lemma hmod_one (x : ℕ*) : x % 1 = 0 := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  apply ofSeq_eq_ofSeq.mpr
  filter_upwards with n
  exact Nat.mod_one (f n)

/-- x % x = 0 for nonzero x. -/
lemma hmod_self {x : ℕ*} (hx : x ≠ 0) : x % x = 0 := by
  have hpos : 0 < x := pos_iff_ne_zero.mpr hx
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  apply ofSeq_eq_ofSeq.mpr
  have hne : ∀ᶠ n in nonstandardUltrafilter ℕ, 0 < f n := ofSeq_lt_ofSeq.mp hpos
  filter_upwards [hne] with n _
  exact Nat.mod_self (f n)

/-- 0 % x = 0. -/
@[simp] lemma zero_hmod (x : ℕ*) : 0 % x = 0 := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  apply ofSeq_eq_ofSeq.mpr
  filter_upwards with n
  exact Nat.zero_mod (f n)

/-- Division-modulo identity: x = (x / y) * y + x % y. -/
lemma hdiv_add_hmod (x y : ℕ*) : (x / y) * y + x % y = x := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rcases ofSeq_surjective y with ⟨g, rfl⟩
  simp only [hdiv_ofSeq, hmod_ofSeq, ofSeq_mul, ofSeq_add]
  apply ofSeq_eq_ofSeq.mpr
  filter_upwards with n
  simp only [Pi.mul_apply, Pi.add_apply]
  rw [mul_comm]
  exact Nat.div_add_mod (f n) (g n)

/-- x % y < y for positive y. -/
lemma hmod_lt {x y : ℕ*} (hy : 0 < y) : x % y < y := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rcases ofSeq_surjective y with ⟨g, rfl⟩
  simp only [hmod_ofSeq]
  apply ofSeq_lt_ofSeq.mpr
  have hpos : ∀ᶠ n in nonstandardUltrafilter ℕ, 0 < g n := ofSeq_lt_ofSeq.mp hy
  filter_upwards [hpos] with n hn
  exact Nat.mod_lt (f n) hn

/-- x / y ≤ x. -/
lemma hdiv_le_self (x y : ℕ*) : x / y ≤ x := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rcases ofSeq_surjective y with ⟨g, rfl⟩
  simp only [hdiv_ofSeq]
  apply ofSeq_le_ofSeq.mpr
  filter_upwards with n
  exact Nat.div_le_self (f n) (g n)

/-- Standard part of division for HFinite numbers with nonzero divisor. -/
lemma st_hdiv {x y : ℕ*} (hx : HFinite x) (hy : HFinite y) : st (x / y) = st x / st y := by
  have hx' : x = (st x : ℕ*) := isSt_st_of_not_infinite hx
  have hy' : y = (st y : ℕ*) := isSt_st_of_not_infinite hy
  conv_lhs => rw [hx', hy']
  simp only [hdiv_coe, st_coe]

/-- Standard part of modulo for HFinite numbers. -/
lemma st_hmod {x y : ℕ*} (hx : HFinite x) (hy : HFinite y) : st (x % y) = st x % st y := by
  have hx' : x = (st x : ℕ*) := isSt_st_of_not_infinite hx
  have hy' : y = (st y : ℕ*) := isSt_st_of_not_infinite hy
  conv_lhs => rw [hx', hy']
  simp only [hmod_coe, st_coe]

/-- HFinite is closed under division. -/
lemma HFinite.hdiv {x y : ℕ*} (hx : HFinite x) (_hy : HFinite y) : HFinite (x / y) :=
  HFinite.of_le (hdiv_le_self x y) hx

/-- HFinite is closed under modulo with positive divisor. -/
lemma HFinite.hmod {x y : ℕ*} (hx : HFinite x) (hy : HFinite y) : HFinite (x % y) := by
  by_cases h : y = 0
  · subst h
    rcases ofSeq_surjective x with ⟨f, rfl⟩
    have h0 : (0 : ℕ*) = ofSeq (fun _ => 0) := rfl
    rw [h0, hmod_ofSeq]
    -- In Lean 4, n % 0 = n, so ofSeq (fun n => f n % 0) = ofSeq f
    have : ofSeq (fun n => f n % 0) = ofSeq f := by
      apply ofSeq_eq_ofSeq.mpr
      filter_upwards with n
      exact Nat.mod_zero (f n)
    rw [this]
    exact hx
  · have hpos : 0 < y := pos_iff_ne_zero.mpr h
    have hlt : x % y < y := hmod_lt hpos
    exact HFinite.of_le' hy (le_of_lt hlt)

/-! ### Additional comparison lemmas -/

/-- If x < y + 1 then x ≤ y. -/
lemma le_of_lt_succ {x y : ℕ*} (h : x < succ y) : x ≤ y := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rcases ofSeq_surjective y with ⟨g, rfl⟩
  apply ofSeq_le_ofSeq.mpr
  have hlt : ∀ᶠ n in nonstandardUltrafilter ℕ, f n < g n + 1 := ofSeq_lt_ofSeq.mp h
  filter_upwards [hlt] with n hn
  exact Nat.le_of_lt_succ hn

/-- If x ≤ y then x < y + 1. -/
lemma lt_succ_of_le {x y : ℕ*} (h : x ≤ y) : x < succ y := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rcases ofSeq_surjective y with ⟨g, rfl⟩
  apply ofSeq_lt_ofSeq.mpr
  have hle : ∀ᶠ n in nonstandardUltrafilter ℕ, f n ≤ g n := ofSeq_le_ofSeq.mp h
  filter_upwards [hle] with n hn
  exact Nat.lt_succ_of_le hn

/-- x ≤ y iff x < y + 1. -/
lemma le_iff_lt_succ {x y : ℕ*} : x ≤ y ↔ x < succ y :=
  ⟨lt_succ_of_le, le_of_lt_succ⟩

/-- If 0 < x then there exists y with x = y + 1. -/
lemma exists_eq_succ_of_pos {x : ℕ*} (hx : 0 < x) : ∃ y : ℕ*, x = succ y := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  have hpos : ∀ᶠ n in nonstandardUltrafilter ℕ, 0 < f n := ofSeq_lt_ofSeq.mp hx
  use ofSeq (fun n => f n - 1)
  rw [succ_ofSeq]
  apply ofSeq_eq_ofSeq.mpr
  filter_upwards [hpos] with n hn
  exact (Nat.sub_add_cancel (Nat.one_le_of_lt hn)).symm

/-- Predecessor function. -/
noncomputable def pred (x : ℕ*) : ℕ* := x - 1

/-- Predecessor preserves sequences. -/
lemma pred_ofSeq (f : ℕ → ℕ) : pred (ofSeq f) = ofSeq (fun n => f n - 1) := rfl

/-- Predecessor of standard natural. -/
@[simp] lemma pred_coe (n : ℕ) : pred (n : ℕ*) = (n - 1 : ℕ*) := rfl

/-- pred (succ x) = x. -/
@[simp] lemma pred_succ (x : ℕ*) : pred (succ x) = x := by
  simp only [pred, succ, add_tsub_cancel_right]

/-- succ (pred x) = x for positive x. -/
lemma succ_pred {x : ℕ*} (hx : 0 < x) : succ (pred x) = x := by
  unfold pred succ
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  have h1 : (1 : ℕ*) = ofSeq (fun _ => 1) := rfl
  rw [h1, tsub_ofSeq, ofSeq_add]
  apply ofSeq_eq_ofSeq.mpr
  have hpos : ∀ᶠ n in nonstandardUltrafilter ℕ, 0 < f n := ofSeq_lt_ofSeq.mp hx
  filter_upwards [hpos] with n hn
  simp only [Pi.add_apply]
  exact Nat.sub_add_cancel (Nat.one_le_of_lt hn)

/-- pred 0 = 0. -/
@[simp] lemma pred_zero : pred (0 : ℕ*) = 0 := by
  simp only [pred]
  exact zero_tsub 1

/-- If x is infinite, pred x is infinite. -/
lemma Infinite.pred {x : ℕ*} (hx : Infinite x) : Infinite (pred x) := by
  intro n
  have hn1 : ((n + 1) : ℕ*) < x := hx (n + 1)
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [pred_ofSeq]
  apply ofSeq_lt_ofSeq.mpr
  have hlt : ∀ᶠ i in nonstandardUltrafilter ℕ, n + 1 < f i := ofSeq_lt_ofSeq.mp hn1
  filter_upwards [hlt] with i hi
  exact Nat.lt_sub_of_add_lt hi

/-- pred of HFinite is HFinite. -/
lemma HFinite.pred' {x : ℕ*} (hx : HFinite x) : HFinite (Hypernatural.pred x) := by
  unfold Hypernatural.pred
  exact hx.tsub hFinite_one

/-- Standard part of pred. -/
lemma st_pred {x : ℕ*} (hx : HFinite x) : st (pred x) = st x - 1 := by
  simp only [pred, st_tsub hx hFinite_one, st_one]

/-! ### Divisibility -/

/-- Divisibility for hypernaturals: x ∣ y iff there exists z with y = x * z. -/
lemma hdvd_def (x y : ℕ*) : x ∣ y ↔ ∃ z : ℕ*, y = x * z := Iff.rfl

/-- Standard divisibility lifts to hypernaturals. -/
lemma coe_dvd_coe_of_dvd {m n : ℕ} (h : m ∣ n) : (m : ℕ*) ∣ (n : ℕ*) := by
  rcases h with ⟨k, hk⟩
  use (k : ℕ*)
  simp [hk]

/-- Every hypernatural divides itself. -/
@[simp] lemma dvd_refl (x : ℕ*) : x ∣ x := ⟨1, (mul_one x).symm⟩

/-- 1 divides every hypernatural. -/
@[simp] lemma one_dvd (x : ℕ*) : 1 ∣ x := ⟨x, (one_mul x).symm⟩

/-- Every hypernatural divides 0. -/
@[simp] lemma dvd_zero (x : ℕ*) : x ∣ 0 := ⟨0, (mul_zero x).symm⟩

/-- 0 divides only 0. -/
lemma zero_dvd {x : ℕ*} : 0 ∣ x ↔ x = 0 := by
  constructor
  · intro ⟨z, hz⟩
    simp only [zero_mul] at hz
    exact hz
  · intro h
    subst h
    exact dvd_refl 0

/-! ### More Arithmetic Properties -/

/-- Multiplication by successor. -/
lemma mul_succ (x y : ℕ*) : x * succ y = x * y + x := by
  rw [ Hypernatural.succ, mul_add, mul_one ]

/-- Successor times x. -/
lemma succ_mul (x y : ℕ*) : succ x * y = x * y + y := by
  -- By the distributive property of multiplication over addition, we have (x + 1) * y = x * y + 1 * y.
  have h_dist : (x + 1) * y = x * y + 1 * y := by
    exact add_mul _ _ _;
  aesop

/-- Power of hypernatural. -/
noncomputable def hpow (x : ℕ*) (n : ℕ) : ℕ* :=
  match n with
  | 0 => 1
  | n + 1 => hpow x n * x

@[simp] lemma hpow_zero (x : ℕ*) : hpow x 0 = 1 := rfl

@[simp] lemma hpow_succ (x : ℕ*) (n : ℕ) : hpow x (n + 1) = hpow x n * x := rfl

/-- Power preserves standard naturals. -/
lemma hpow_coe (m n : ℕ) : hpow (m : ℕ*) n = (m ^ n : ℕ*) := by
  induction n <;> simp_all +decide [ pow_succ ]

/-- omega^n is infinite for n ≥ 1. -/
lemma hpow_omega_infinite (n : ℕ) (hn : 0 < n) : Infinite (hpow ω n) := by
  induction' hn with n hn ih;
  · simp +decide [ Hypernatural.Infinite ];
  · exact ih.mul_pos ( by norm_num )

/-! ### Min and Max -/

/-- Minimum of two hypernaturals. -/
noncomputable def hmin (x y : ℕ*) : ℕ* :=
  Quotient.liftOn₂ x y (fun f g => ofSeq (fun n => min (f n) (g n)))
    (fun f₁ f₂ g₁ g₂ hf hg => by
      apply ofSeq_eq_ofSeq.mpr
      filter_upwards [hf, hg] with n hfn hgn
      simp [hfn, hgn])

/-- Maximum of two hypernaturals. -/
noncomputable def hmax (x y : ℕ*) : ℕ* :=
  Quotient.liftOn₂ x y (fun f g => ofSeq (fun n => max (f n) (g n)))
    (fun f₁ f₂ g₁ g₂ hf hg => by
      apply ofSeq_eq_ofSeq.mpr
      filter_upwards [hf, hg] with n hfn hgn
      simp [hfn, hgn])

@[simp] lemma hmin_ofSeq (f g : ℕ → ℕ) : hmin (ofSeq f) (ofSeq g) = ofSeq (fun n => min (f n) (g n)) := rfl

@[simp] lemma hmax_ofSeq (f g : ℕ → ℕ) : hmax (ofSeq f) (ofSeq g) = ofSeq (fun n => max (f n) (g n)) := rfl

lemma hmin_le_left (x y : ℕ*) : hmin x y ≤ x := by
  -- By definition of min, we know that min x y ≤ x.
  apply min_le_left

lemma hmin_le_right (x y : ℕ*) : hmin x y ≤ y := by
  -- By definition of min, we know that min x y ≤ y.
  apply min_le_right

lemma le_hmax_left (x y : ℕ*) : x ≤ hmax x y := by
  -- By definition of hmax, we know that x ≤ hmax x y and y ≤ hmax x y. This follows directly from the definition of hmax.
  apply le_max_left

lemma le_hmax_right (x y : ℕ*) : y ≤ hmax x y := by
  -- By definition of max, we know that max x y ≤ y if and only if x ≤ y. Therefore, we can use the fact that for any two numbers, one is less than or equal to the maximum of the two.
  apply le_max_right

lemma hmin_comm (x y : ℕ*) : hmin x y = hmin y x := by
  -- The minimum function is commutative, so min(x, y) = min(y, x).
  apply min_comm

lemma hmax_comm (x y : ℕ*) : hmax x y = hmax y x := by
  -- The maximum function is commutative, so we can apply the commutativity of the maximum function on ℕ.
  apply max_comm

/-! ### More Infinite and HFinite Properties -/

/-- Infinite minus HFinite is still infinite (if result is positive). -/
lemma Infinite.tsub_hFinite {x y : ℕ*} (hx : Infinite x) (hy : HFinite y) (hpos : y < x) :
    Infinite (x - y) := by
  contrapose! hx;
  rw [ show x = ( x - y ) + y from _ ];
  · exact?;
  · rw [ tsub_add_cancel_of_le hpos.le ]

/-! ### Factorial (optional, requires more setup) -/

/-- Factorial of a hypernatural, defined pointwise. -/
noncomputable def hfact (x : ℕ*) : ℕ* :=
  Quotient.liftOn x (fun f => ofSeq (fun n => Nat.factorial (f n)))
    (fun f₁ f₂ hf => by
      apply ofSeq_eq_ofSeq.mpr
      filter_upwards [hf] with n hn
      simp [hn])

@[simp] lemma hfact_ofSeq (f : ℕ → ℕ) : hfact (ofSeq f) = ofSeq (fun n => Nat.factorial (f n)) := rfl

lemma hfact_coe (n : ℕ) : hfact (n : ℕ*) = (Nat.factorial n : ℕ*) := by
  -- By definition of quotient lift, we know that applying it to the constant sequence n gives the constant sequence n.factorial.
  apply Quotient.sound;
  -- The constant function n! is equal to itself everywhere.
  apply Filter.EventuallyEq.rfl

lemma hfact_pos (x : ℕ*) : 0 < hfact x := by
  -- Since the factorial of any natural number is positive, we can conclude that the hypernatural factorial is also positive.
  have h_pos : ∀ n : ℕ, 0 < Nat.factorial n := by
    exact fun n => Nat.factorial_pos n;
  -- Since the factorial of any natural number is positive, we can conclude that the hypernatural factorial is also positive by applying the definition of hfact.
  have h_pos : ∀ f : ℕ → ℕ, (∀ n, 0 < Nat.factorial (f n)) → 0 < ofSeq (fun n => Nat.factorial (f n)) := by
    -- Since the sequence is positive at every index, the germ is positive.
    intros f hf
    have h_pos_seq : ∀ᶠ n in nonstandardUltrafilter ℕ, 0 < Nat.factorial (f n) := by
      exact?;
    exact?;
  -- Apply the hypothesis `h_pos` to the sequence representing `x`.
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, x = ofSeq f := by
    exact ⟨ _, Eq.symm <| Quotient.out_eq _ ⟩;
  aesop

lemma infinite_hfact_omega : Infinite (hfact ω) := by
  -- Apply the lemma that states if x is infinite, then x! is infinite.
  apply Infinite.factorial; exact infinite_omega

/-! ### GCD and LCM -/

/-- GCD of two hypernaturals. -/
noncomputable def hgcd (x y : ℕ*) : ℕ* :=
  Quotient.liftOn₂ x y (fun f g => ofSeq (fun n => Nat.gcd (f n) (g n)))
    (fun f₁ f₂ g₁ g₂ hf hg => by
      apply ofSeq_eq_ofSeq.mpr
      filter_upwards [hf, hg] with n hfn hgn
      simp [hfn, hgn])

/-- LCM of two hypernaturals. -/
noncomputable def hlcm (x y : ℕ*) : ℕ* :=
  Quotient.liftOn₂ x y (fun f g => ofSeq (fun n => Nat.lcm (f n) (g n)))
    (fun f₁ f₂ g₁ g₂ hf hg => by
      apply ofSeq_eq_ofSeq.mpr
      filter_upwards [hf, hg] with n hfn hgn
      simp [hfn, hgn])

@[simp] lemma hgcd_ofSeq (f g : ℕ → ℕ) : hgcd (ofSeq f) (ofSeq g) = ofSeq (fun n => Nat.gcd (f n) (g n)) := rfl

@[simp] lemma hlcm_ofSeq (f g : ℕ → ℕ) : hlcm (ofSeq f) (ofSeq g) = ofSeq (fun n => Nat.lcm (f n) (g n)) := rfl

lemma hgcd_comm (x y : ℕ*) : hgcd x y = hgcd y x := by
  -- By definition of hgcd, we know that hgcd x y = hgcd y x.
  have h_comm : ∀ (f g : ℕ → ℕ), hgcd (ofSeq f) (ofSeq g) = hgcd (ofSeq g) (ofSeq f) := by
    aesop;
    exact congr_arg _ ( funext fun n => Nat.gcd_comm _ _ );
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, x = Hypernatural.ofSeq f := by
    exact ⟨ _, Eq.symm ( Quotient.out_eq' x ) ⟩
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℕ, y = Hypernatural.ofSeq g := by
    -- Since y is a hypernatural, by definition, it's represented by some sequence of naturals. So, I can take that sequence as g.
    obtain ⟨g, hg⟩ : ∃ g : ℕ → ℕ, y = Hypernatural.ofSeq g := by
      have := Hypernatural.ofSeq_surjective y
      tauto;
    -- Since y is equal to the ofSeq of g, we can use g as the witness.
    use g
  rw [hf, hg]
  exact h_comm f g

lemma hlcm_comm (x y : ℕ*) : hlcm x y = hlcm y x := by
  -- Since the lcm function is commutative in the natural numbers, applying it to the sequences in either order should give the same result.
  have h_lcm_comm : ∀ (f g : ℕ → ℕ), ofSeq (fun n => Nat.lcm (f n) (g n)) = ofSeq (fun n => Nat.lcm (g n) (f n)) := by
    -- Since the LCM function is commutative in the natural numbers, we can apply it to the sequences.
    intros f g
    simp [Nat.lcm_comm];
  -- By definition of `hlcm` for hypernaturals, we can write `x` and `y` as `ofSeq f` and `ofSeq g` for some sequences `f` and `g`.
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, x = ofSeq f := by
    exact ⟨ _, Eq.symm <| Quotient.out_eq x ⟩
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℕ, y = ofSeq g := by
    -- Since any element in the hypernaturals can be represented as a sequence, we can use the fact that y is an element of the hypernaturals to obtain such a sequence g.
    have h_surjective : Function.Surjective Hypernatural.ofSeq := by
      exact?;
    exact h_surjective y |> Exists.imp fun g hg => hg.symm;
  unfold Hypernatural.hlcm; aesop;

lemma hgcd_dvd_left (x y : ℕ*) : hgcd x y ∣ x := by
  -- By definition of hgcd, we have that hgcd x y divides x.
  apply Hypernatural.gcd_dvd_left

lemma hgcd_dvd_right (x y : ℕ*) : hgcd x y ∣ y := by
  -- By definition of hgcd, we know that for any sequences f and g representing x and y, hgcd( ofSeq f, ofSeq g ) divides ofSeq g.
  have h_hgcd_div_g : ∀ f g : ℕ → ℕ, hgcd (ofSeq f) (ofSeq g) ∣ ofSeq g := by
    -- By definition of H, we know that Nat.gcd (f n) (g n) divides g n for all n.
    have h_div : ∀ f g : ℕ → ℕ, ∀ n, Nat.gcd (f n) (g n) ∣ g n := by
      -- By definition of gcd, we know that gcd(a, b) divides both a and b.
      intros f g n
      apply Nat.gcd_dvd_right;
    intros f g
    have h_div_seq : ∀ n, Nat.gcd (f n) (g n) ∣ g n := h_div f g
    simp [Hypernatural.hgcd, h_div_seq];
    -- Since the gcd of f(n) and g(n) divides g(n) for all n, the sequence of gcds divides the sequence of g.
    have h_seq_div : ∀ n, Nat.gcd (f n) (g n) ∣ g n := by
      assumption;
    use Hypernatural.ofSeq (fun n => g n / Nat.gcd (f n) (g n));
    exact Quotient.sound <| Filter.Eventually.of_forall fun n => by simp +decide [ Nat.mul_div_cancel' ( h_seq_div n ) ] ;
  obtain ⟨ f, rfl ⟩ := Hypernatural.ofSeq_surjective x; obtain ⟨ g, rfl ⟩ := Hypernatural.ofSeq_surjective y; exact h_hgcd_div_g f g;

lemma dvd_hlcm_left (x y : ℕ*) : x ∣ hlcm x y := by
  -- Apply the definition of `hlcm` to get the equality.
  obtain ⟨f, hf⟩ := Hypernatural.ofSeq_surjective x
  obtain ⟨g, hg⟩ := Hypernatural.ofSeq_surjective y;
  -- Since $f(n)$ divides $Nat.lcm(f(n), g(n))$ for all $n$, we have $ofSeq f$ divides $ofSeq (fun n => Nat.lcm (f n) (g n))$.
  have h_div : ∀ n, f n ∣ Nat.lcm (f n) (g n) := by
    exact fun n => Nat.dvd_lcm_left _ _;
  -- Since $f(n)$ divides $Nat.lcm(f(n), g(n))$ for all $n$, we can write $Nat.lcm(f(n), g(n)) = f(n) * h(n)$ for some function $h$.
  obtain ⟨h, hh⟩ : ∃ h : ℕ → ℕ, ∀ n, Nat.lcm (f n) (g n) = f n * h n := by
    exact ⟨ fun n => Nat.lcm ( f n ) ( g n ) / f n, fun n => by rw [ Nat.mul_div_cancel' ( h_div n ) ] ⟩;
  aesop;
  use Hypernatural.ofSeq h;
  exact?

lemma dvd_hlcm_right (x y : ℕ*) : y ∣ hlcm x y := by
  -- Since y divides the maximum of the prime powers in x and y, and the lcm is the product of these maximums, y must divide the lcm.
  have h_div_max : ∀ (a b : ℕ), b ∣ Nat.lcm a b := by
    -- By definition of lcm, b divides the least common multiple of a and b.
    intros a b
    apply Nat.dvd_lcm_right;
  have h_div_lcm : ∀ (f g : ℕ → ℕ), (∀ n, g n ∣ Nat.lcm (f n) (g n)) → ofSeq g ∣ hlcm (ofSeq f) (ofSeq g) := by
    -- If for every n, g n divides lcm(f n, g n), then there exists a sequence c_n such that lcm(f n, g n) = g n * c_n.
    intro f g h_div
    obtain ⟨c, hc⟩ : ∃ c : ℕ → ℕ, ∀ n, Nat.lcm (f n) (g n) = g n * c n := by
      exact ⟨ fun n => Nat.lcm ( f n ) ( g n ) / g n, fun n => by rw [ Nat.mul_div_cancel' ( h_div n ) ] ⟩;
    use Hypernatural.ofSeq c;
    aesop;
  -- Since y is a hypernatural, we can represent it as a sequence of natural numbers.
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, x = ofSeq f := by
    exact ⟨ _, Eq.symm <| Quotient.out_eq x ⟩
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℕ, y = ofSeq g := by
    exact ⟨ _, Eq.symm <| Quotient.out_eq' y ⟩;
  aesop

/-! ### Cofinality Properties -/

/-- For any hypernatural, there exists a representing sequence. -/
lemma exists_seq (x : ℕ*) : ∃ f : ℕ → ℕ, x = ofSeq f := by
  rcases ofSeq_surjective x with ⟨f, hf⟩
  exact ⟨f, hf.symm⟩

/-- Two hypernaturals are equal iff their representing sequences agree almost everywhere. -/
lemma eq_iff_eventually_eq (x y : ℕ*) : x = y ↔ ∃ f g : ℕ → ℕ, x = ofSeq f ∧ y = ofSeq g ∧
    ∀ᶠ n in nonstandardUltrafilter ℕ, f n = g n := by
  aesop;
  · -- By definition of Hypernatural, every hypernatural is the germ of some sequence.
    obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, x = Hypernatural.ofSeq f := by
      exact?;
    exact ⟨ f, hf, f, hf, Filter.Eventually.of_forall fun n => rfl ⟩;
  · exact?

end Hypernatural