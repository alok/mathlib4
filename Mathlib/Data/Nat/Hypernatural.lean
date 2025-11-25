
/-
Copyright (c) 2024 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Mathlib.Order.Filter.FilterProduct
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Basic

/-!
# Hypernatural numbers

We build the *hypernatural numbers* `ℕ*` as germs of sequences of naturals on
the (non‑principal) `hyperfilter ℕ`, mirroring the construction of `ℝ*` in
`Mathlib/Analysis/Real/Hyperreal.lean`.  The API here is intentionally kept
parallel to the hyperreal API where that makes sense for `ℕ`.
-/

open Classical
open Filter Germ Topology

/-- Hypernatural numbers on the ultrafilter extending the cofinite filter. -/
noncomputable def Hypernatural : Type :=
  Germ (hyperfilter ℕ : Filter ℕ) ℕ

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
def ofSeq (f : ℕ → ℕ) : ℕ* := (↑f : Germ (hyperfilter ℕ : Filter ℕ) ℕ)

theorem ofSeq_const (r : ℕ) : ofSeq (fun _ => r) = (r : ℕ*) := rfl

theorem ofSeq_surjective : Function.Surjective ofSeq := Quot.exists_rep

theorem ofSeq_eq_ofSeq {f g : ℕ → ℕ} : ofSeq f = ofSeq g ↔ ∀ᶠ n in hyperfilter ℕ, f n = g n :=
  Germ.coe_eq

theorem ofSeq_le_ofSeq {f g : ℕ → ℕ} : ofSeq f ≤ ofSeq g ↔ ∀ᶠ n in hyperfilter ℕ, f n ≤ g n :=
  Germ.coe_le

theorem ofSeq_lt_ofSeq {f g : ℕ → ℕ} : ofSeq f < ofSeq g ↔ ∀ᶠ n in hyperfilter ℕ, f n < g n :=
  Germ.coe_lt

/-- A canonical infinite hypernatural. -/
noncomputable def omega : ℕ* := ofSeq Nat.cast

@[inherit_doc] scoped notation "ω" => Hypernatural.omega

theorem omega_pos : 0 < ω :=
  Germ.coe_pos.2 <|
    Nat.hyperfilter_le_atTop <|
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
    (ofSeq_lt_ofSeq).2 <| Nat.hyperfilter_le_atTop <| (eventually_gt_atTop m).mono fun n hn => by
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
    IsSt (ofSeq f) r ↔ ∀ᶠ n in hyperfilter ℕ, f n = r := by
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
  have hf_le : ∀ᶠ n in hyperfilter ℕ, f n ≤ m :=
    (ofSeq_le_ofSeq (f := f) (g := fun _ => m)).1 (by simpa [ofSeq_const] using hle)
  have hUnion_mem :
      (⋃ r ∈ Finset.range (m + 1), {n | f n = r}) ∈ (hyperfilter ℕ : Filter ℕ) := by
    have hsubset :
        {n | f n ≤ m} ⊆ ⋃ r ∈ Finset.range (m + 1), {n | f n = r} := by
      intro n hn
      have hrange : f n ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hn)
      exact Set.mem_iUnion.mpr ⟨f n, Set.mem_iUnion.mpr ⟨hrange, rfl⟩⟩
    exact (hyperfilter ℕ : Filter ℕ).mem_of_superset hf_le hsubset
  let u : Ultrafilter ℕ := hyperfilter ℕ
  have hUnion_mem' : (⋃ r ∈ Finset.range (m + 1), {n | f n = r}) ∈ (u : Filter ℕ) := hUnion_mem
  have aux : ∀ s : Finset ℕ,
      (⋃ r ∈ s, {n | f n = r}) ∈ (u : Filter ℕ) →
      ∃ r ∈ s, {n | f n = r} ∈ (u : Filter ℕ) := by
    intro s
    refine Finset.induction_on s ?base ?step
    · intro h
      have : (∅ : Set ℕ) ∉ (u : Filter ℕ) := u.empty_notMem
      exact (this (by simpa using h)).elim
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
  have hy' : ∀ᶠ i in hyperfilter ℕ, 0 < f i :=
    (ofSeq_lt_ofSeq (f := fun _ => 0) (g := f)).1 (by simpa [ofSeq_const] using hy)
  have hx' : ∀ᶠ i in hyperfilter ℕ, n < g i :=
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
  have hf : ∀ᶠ i in hyperfilter ℕ, 0 < f i := (ofSeq_lt_ofSeq (f := fun _ => 0) (g := f)).1
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

end Hypernatural
