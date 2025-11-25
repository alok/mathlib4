/-
Copyright (c) 2024 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Mathlib.Order.Filter.FilterProduct
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Hypernatural

/-!
# Hyperrational numbers

We build the *hyperrational numbers* `ℚ*` as germs of sequences of rationals on
the ultrafilter extending the cofinite filter, mirroring the constructions of
`ℝ*` and `ℕ*`.
-/

open Filter Germ Topology

/-- Hyperrational numbers on the ultrafilter extending the cofinite filter. -/
noncomputable def Hyperrational : Type :=
  Germ (hyperfilter ℕ : Filter ℕ) ℚ

namespace Hyperrational

/-- Notation for hyperrationals. -/
@[inherit_doc] notation "ℚ*" => Hyperrational

noncomputable instance : Field ℚ* :=
  inferInstanceAs (Field (Germ _ _))

noncomputable instance : LinearOrder ℚ* :=
  inferInstanceAs (LinearOrder (Germ _ _))

instance : IsStrictOrderedRing ℚ* :=
  inferInstanceAs (IsStrictOrderedRing (Germ _ _))

/-- Construct a hyperrational number from a sequence of rationals. -/
noncomputable def ofSeq (f : ℕ → ℚ) : ℚ* := (↑f : Germ (hyperfilter ℕ : Filter ℕ) ℚ)

theorem ofSeq_surjective : Function.Surjective ofSeq := Quot.exists_rep

theorem ofSeq_eq_ofSeq {f g : ℕ → ℚ} : ofSeq f = ofSeq g ↔ ∀ᶠ n in hyperfilter ℕ, f n = g n :=
  Germ.coe_eq

theorem ofSeq_lt_ofSeq {f g : ℕ → ℚ} : ofSeq f < ofSeq g ↔ ∀ᶠ n in hyperfilter ℕ, f n < g n :=
  Germ.coe_lt

theorem ofSeq_le_ofSeq {f g : ℕ → ℚ} : ofSeq f ≤ ofSeq g ↔ ∀ᶠ n in hyperfilter ℕ, f n ≤ g n :=
  Germ.coe_le

/-- Standard embedding of rationals as constant sequences. -/
noncomputable def ofRat (q : ℚ) : ℚ* := ofSeq (fun _ => q)

noncomputable instance : Coe ℚ ℚ* := ⟨ofRat⟩

@[simp]
theorem ofRat_eq_ofRat {a b : ℚ} : ofRat a = ofRat b ↔ a = b := by
  simp only [ofRat, ofSeq_eq_ofSeq, Filter.eventually_const]

@[simp]
theorem ofRat_le_ofRat {a b : ℚ} : ofRat a ≤ ofRat b ↔ a ≤ b := by
  simp only [ofRat, ofSeq_le_ofSeq, Filter.eventually_const]

@[simp]
theorem ofRat_lt_ofRat {a b : ℚ} : ofRat a < ofRat b ↔ a < b := by
  simp only [ofRat, ofSeq_lt_ofSeq, Filter.eventually_const]

@[simp]
lemma ofRat_neg (q : ℚ) : ofRat (-q) = -ofRat q := rfl

@[simp]
lemma ofRat_add (a b : ℚ) : ofRat (a + b) = ofRat a + ofRat b := rfl

/-- A sample infinitesimal hyperrational. -/
noncomputable def epsilon : ℚ* := ofSeq fun n => (Nat.succ n : ℚ)⁻¹

/-- A sample infinite hyperrational. -/
noncomputable def omega : ℚ* := ofSeq fun n => n

@[inherit_doc] scoped notation "ε" => Hyperrational.epsilon
@[inherit_doc] scoped notation "ω" => Hyperrational.omega

/-- Positive infinity predicate. -/
def InfinitePos (x : ℚ*) : Prop := ∀ q : ℚ, ofRat q < x

/-- Negative infinity predicate. -/
def InfiniteNeg (x : ℚ*) : Prop := ∀ q : ℚ, x < ofRat q

/-- A hyperrational is infinite if it is either positive or negative infinite. -/
def Infinite (x : ℚ*) : Prop := InfinitePos x ∨ InfiniteNeg x

/-- Infinitesimal hyperrationals: bounded by every positive rational in absolute value. -/
def Infinitesimal (x : ℚ*) : Prop := ∀ q : ℚ, 0 < q → ofRat (-q) < x ∧ x < ofRat q

/-- A hyperrational is HFinite if it is not infinite. -/
def HFinite (x : ℚ*) : Prop := ¬ Infinite x

/-- Infinitely close relation: x ≈ y if x - y is infinitesimal. -/
def InfClose (x y : ℚ*) : Prop := Infinitesimal (x - y)

@[inherit_doc] scoped infixl:50 " ≈ " => InfClose

/-- Monad of a hyperrational. -/
def monad (x : ℚ*) : Set ℚ* := {y | x ≈ y}

/-- Galaxy of a hyperrational. -/
def galaxy (x : ℚ*) : Set ℚ* := {y | HFinite (x - y)}

theorem omega_pos : 0 < ω := by
  rw [show (0 : ℚ*) = ofSeq (fun _ => (0 : ℚ)) from rfl, omega, ofSeq_lt_ofSeq]
  exact Nat.hyperfilter_le_atTop <| (eventually_gt_atTop 0).mono fun n hn => by
    simp only [Nat.cast_pos]
    exact hn

theorem epsilon_pos : 0 < ε := by
  rw [show (0 : ℚ*) = ofSeq (fun _ => (0 : ℚ)) from rfl, epsilon, ofSeq_lt_ofSeq]
  exact Nat.hyperfilter_le_atTop <| eventually_atTop.mpr ⟨1, fun n hn => by
    simp only [Nat.cast_pos, Nat.succ_pos, inv_pos]⟩

theorem epsilon_ne_zero : ε ≠ 0 := epsilon_pos.ne'
theorem omega_ne_zero : ω ≠ 0 := omega_pos.ne'

theorem infinite_omega : Infinite ω := by
  left
  intro q
  rw [ofRat, omega, ofSeq_lt_ofSeq]
  exact Nat.hyperfilter_le_atTop <| eventually_atTop.mpr ⟨⌈q⌉₊ + 1, fun n hn => by
    have : (⌈q⌉₊ : ℚ) < n := by exact_mod_cast Nat.lt_of_succ_le hn
    exact lt_of_le_of_lt (Nat.le_ceil q) this⟩

theorem InfinitePos.pos {x : ℚ*} (hx : InfinitePos x) : 0 < x := by
  have := hx 0
  rw [ofRat] at this
  rw [show (0 : ℚ*) = ofSeq (fun _ => (0 : ℚ)) from rfl]
  exact this

theorem Infinite.ne_zero {x : ℚ*} (hx : Infinite x) : x ≠ 0 := by
  intro h
  rcases hx with hx | hx
  · have := hx 0
    rw [ofRat] at this
    rw [h, show (0 : ℚ*) = ofSeq (fun _ => (0 : ℚ)) from rfl] at this
    exact lt_irrefl _ this
  · have := hx 0
    rw [ofRat] at this
    rw [h, show (0 : ℚ*) = ofSeq (fun _ => (0 : ℚ)) from rfl] at this
    exact lt_irrefl _ this

theorem not_hFinite_omega : ¬ HFinite ω := fun h => h infinite_omega

/-- Infinitely close is reflexive. -/
@[refl] lemma infClose_refl (x : ℚ*) : x ≈ x := by
  intro q hq
  simp only [sub_self]
  rw [show (0 : ℚ*) = ofSeq (fun _ => (0 : ℚ)) from rfl]
  constructor
  · rw [ofRat, ofSeq_lt_ofSeq]
    exact Eventually.of_forall fun _ => neg_lt_zero.mpr hq
  · rw [ofRat, ofSeq_lt_ofSeq]
    exact Eventually.of_forall fun _ => hq

/-- Infinitely close is symmetric. -/
@[symm] lemma infClose_symm {x y : ℚ*} (h : x ≈ y) : y ≈ x := by
  intro q hq
  have h' := h q hq
  have hne : y - x = -(x - y) := by ring
  rw [hne]
  constructor
  · simp only [ofRat_neg]
    exact neg_lt_neg_iff.mpr h'.2
  · calc -(x - y) < -ofRat (-q) := neg_lt_neg_iff.mpr h'.1
      _ = -(-ofRat q) := by simp only [ofRat_neg]
      _ = ofRat q := neg_neg _

/-- Infinitely close is transitive. -/
@[trans] lemma infClose_trans {x y z : ℚ*} (hxy : x ≈ y) (hyz : y ≈ z) : x ≈ z := by
  intro q hq
  have hxy' := hxy (q / 2) (by linarith)
  have hyz' := hyz (q / 2) (by linarith)
  have heq : x - z = (x - y) + (y - z) := by ring
  rw [heq]
  constructor
  · have hsum : ofRat (-q) = ofRat (-(q/2)) + ofRat (-(q/2)) := by
      simp only [← ofRat_add]; ring_nf
    rw [hsum]
    exact add_lt_add hxy'.1 hyz'.1
  · have hsum : ofRat q = ofRat (q/2) + ofRat (q/2) := by
      simp only [← ofRat_add]; ring_nf
    rw [hsum]
    exact add_lt_add hxy'.2 hyz'.2

/-- `InfClose` is an equivalence relation. -/
theorem infClose_equivalence : Equivalence InfClose :=
  ⟨infClose_refl, fun h => infClose_symm h, fun h1 h2 => infClose_trans h1 h2⟩

/-- Setoid instance for infinitely close relation. -/
instance infCloseSetoid : Setoid ℚ* where
  r := InfClose
  iseqv := infClose_equivalence

/-! ## Nonstandard Extension of Functions -/

/-- The nonstandard extension (star map) of a function `f : ℚ → ℚ` to `f* : ℚ* → ℚ*`. -/
noncomputable def star (f : ℚ → ℚ) : ℚ* → ℚ* := Germ.map f

@[simp]
lemma star_ofSeq (f : ℚ → ℚ) (s : ℕ → ℚ) : star f (ofSeq s) = ofSeq (f ∘ s) := rfl

@[simp]
lemma star_ofRat (f : ℚ → ℚ) (q : ℚ) : star f (ofRat q) = ofRat (f q) := rfl

/-! ## Continuity Definitions -/

/-- Standard epsilon-delta continuity of `f : ℚ → ℚ` at point `a`. -/
def ContinuousAt (f : ℚ → ℚ) (a : ℚ) : Prop :=
  ∀ eps : ℚ, 0 < eps → ∃ delta : ℚ, 0 < delta ∧ ∀ x : ℚ, |x - a| < delta → |f x - f a| < eps

/-- Nonstandard (monad) continuity: `f*` maps points infinitely close to `a` to points
infinitely close to `f(a)`. -/
def NSContinuousAt (f : ℚ → ℚ) (a : ℚ) : Prop :=
  ∀ x : ℚ*, InfClose x (ofRat a) → InfClose (star f x) (ofRat (f a))

/-! ## Equivalence of Continuity Definitions -/

/-- Helper: If `x ≈ ofRat a`, then `x - ofRat a` is infinitesimal. -/
lemma infClose_ofRat_iff_infinitesimal {x : ℚ*} {a : ℚ} :
    InfClose x (ofRat a) ↔ Infinitesimal (x - ofRat a) := Iff.rfl

/-- Epsilon-delta continuity implies nonstandard continuity.

The proof transfers the epsilon-delta condition through the ultrafilter:
if x ≈ a, then for any δ > 0 we have |x - a| < δ ultrafilter-almost-everywhere,
so |f(x) - f(a)| < ε ultrafilter-almost-everywhere by epsilon-delta continuity. -/
theorem continuousAt_implies_nsContinuousAt {f : ℚ → ℚ} {a : ℚ}
    (hf : ContinuousAt f a) : NSContinuousAt f a := by
  intro x hx
  unfold InfClose Infinitesimal at hx ⊢
  intro eps heps
  obtain ⟨delta, hdelta_pos, hdelta⟩ := hf eps heps
  have hx_close := hx delta hdelta_pos
  -- x - ofRat a is infinitesimal, so |x - a| < delta ultrafilter-almost-everywhere.
  rcases ofSeq_surjective x with ⟨s, rfl⟩
  -- Convert hyperrational bounds to sequence bounds
  have hlo : ofRat (-delta) < ofSeq s - ofRat a := hx_close.1
  have hhi : ofSeq s - ofRat a < ofRat delta := hx_close.2
  rw [show ofSeq s - ofRat a = ofSeq (fun n => s n - a) from rfl] at hlo hhi
  rw [ofRat, ofSeq_lt_ofSeq] at hlo hhi
  -- Eventually |s_n - a| < delta
  have h_abs_bound : ∀ᶠ n in hyperfilter ℕ, |s n - a| < delta := by
    filter_upwards [hlo, hhi] with n hlo_n hhi_n
    rw [abs_lt]
    exact ⟨hlo_n, hhi_n⟩
  -- By epsilon-delta continuity, eventually |f(s_n) - f(a)| < eps
  have h_f_bound : ∀ᶠ n in hyperfilter ℕ, |f (s n) - f a| < eps := by
    filter_upwards [h_abs_bound] with n hn
    exact hdelta (s n) hn
  -- Convert back to hyperrational inequalities
  constructor
  · rw [show star f (ofSeq s) - ofRat (f a) = ofSeq (fun n => f (s n) - f a) from rfl]
    rw [ofRat, ofSeq_lt_ofSeq]
    filter_upwards [h_f_bound] with n hn
    rw [abs_lt] at hn
    linarith
  · rw [show star f (ofSeq s) - ofRat (f a) = ofSeq (fun n => f (s n) - f a) from rfl]
    rw [ofRat, ofSeq_lt_ofSeq]
    filter_upwards [h_f_bound] with n hn
    rw [abs_lt] at hn
    exact hn.2

/-- Nonstandard continuity implies epsilon-delta continuity.

The proof proceeds by contraposition: if f is not epsilon-delta continuous at a,
we construct a sequence (s_n) with |s_n - a| < 1/(n+1) but |f(s_n) - f(a)| ≥ ε.
The hyperrational x = [s_n] is infinitely close to a, but f*(x) is not infinitely
close to f(a), contradicting nonstandard continuity. -/
theorem nsContinuousAt_implies_continuousAt {f : ℚ → ℚ} {a : ℚ}
    (hf : NSContinuousAt f a) : ContinuousAt f a := by
  by_contra h
  simp only [ContinuousAt, not_forall, not_exists, not_and, not_lt] at h
  obtain ⟨eps, heps_pos, hbad⟩ := h
  -- For each n, pick x_n with |x_n - a| < 1/(n+1) but |f(x_n) - f(a)| ≥ eps
  have hex : ∀ n : ℕ, ∃ x : ℚ, |x - a| < (n + 1 : ℚ)⁻¹ ∧ eps ≤ |f x - f a| := by
    intro n
    have hpos : (0 : ℚ) < (n + 1 : ℚ)⁻¹ := by positivity
    have := hbad ((n + 1 : ℚ)⁻¹) hpos
    simp only [exists_prop] at this ⊢
    obtain ⟨x, hx1, hx2⟩ := this
    exact ⟨x, hx1, hx2⟩
  choose s hs using hex
  let x : ℚ* := ofSeq s
  -- x is infinitely close to a (the sequence s converges to a)
  have hx_close : InfClose x (ofRat a) := by
    unfold InfClose Infinitesimal
    intro q hq
    -- Need to show |x - a| < q, i.e., eventually |s_n - a| < q
    -- Since |s_n - a| < 1/(n+1) and 1/(n+1) → 0, this holds for large n
    -- Find N such that 1/(N+1) < q
    have harch : ∃ N : ℕ, (N + 1 : ℚ)⁻¹ < q := by
      obtain ⟨N, hN⟩ := exists_nat_gt q⁻¹
      use N
      have hN1_pos : (0 : ℚ) < N + 1 := by positivity
      rw [inv_lt_comm₀ hN1_pos hq]
      calc q⁻¹ < N := hN
        _ < N + 1 := by linarith
    obtain ⟨N, hN⟩ := harch
    constructor
    · rw [show (x : ℚ*) - ofRat a = ofSeq (fun n => s n - a) from rfl]
      rw [ofRat, ofSeq_lt_ofSeq]
      apply Nat.hyperfilter_le_atTop
      apply eventually_atTop.mpr
      use N
      intro n hn
      have hs_n := (hs n).1
      rw [abs_lt] at hs_n
      have hN1_pos : (0 : ℚ) < N + 1 := by positivity
      have hn1_pos : (0 : ℚ) < n + 1 := by positivity
      have hinv_mono : (n + 1 : ℚ)⁻¹ ≤ (N + 1 : ℚ)⁻¹ := by
        apply inv_anti₀ hN1_pos
        exact_mod_cast Nat.add_le_add_right hn 1
      linarith
    · rw [show (x : ℚ*) - ofRat a = ofSeq (fun n => s n - a) from rfl]
      rw [ofRat, ofSeq_lt_ofSeq]
      apply Nat.hyperfilter_le_atTop
      apply eventually_atTop.mpr
      use N
      intro n hn
      have hs_n := (hs n).1
      rw [abs_lt] at hs_n
      have hN1_pos : (0 : ℚ) < N + 1 := by positivity
      have hn1_pos : (0 : ℚ) < n + 1 := by positivity
      have hinv_mono : (n + 1 : ℚ)⁻¹ ≤ (N + 1 : ℚ)⁻¹ := by
        apply inv_anti₀ hN1_pos
        exact_mod_cast Nat.add_le_add_right hn 1
      linarith
  -- By nonstandard continuity, f*(x) should be infinitely close to f(a)
  have hfx_close := hf x hx_close
  -- But by construction, |f(s_n) - f(a)| ≥ eps for all n, contradiction
  unfold InfClose Infinitesimal at hfx_close
  have h_half := hfx_close (eps / 2) (by linarith)
  -- The contradiction: f*(x) - f(a) is both in (-eps/2, eps/2) and has |·| ≥ eps
  have hlo : ofRat (-(eps / 2)) < star f x - ofRat (f a) := h_half.1
  have hhi : star f x - ofRat (f a) < ofRat (eps / 2) := h_half.2
  rw [show star f x - ofRat (f a) = ofSeq (fun n => f (s n) - f a) from rfl] at hlo hhi
  rw [ofRat, ofSeq_lt_ofSeq] at hlo hhi
  -- But for ALL n, |f(s_n) - f(a)| ≥ eps, contradicting the bounds
  have h_all_bad : ∀ n, eps ≤ |f (s n) - f a| := fun n => (hs n).2
  -- Get the contradiction
  have hfalse : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), False := by
    filter_upwards [hlo, hhi] with n hlo_n hhi_n
    have hge := h_all_bad n
    -- |f(s n) - f a| ≥ eps means f(s n) - f a ≥ eps or f(s n) - f a ≤ -eps
    -- But we have -(eps/2) < f(s n) - f a < eps/2
    -- Since eps > 0, we have eps > eps/2 and -eps < -(eps/2)
    have hbound : |f (s n) - f a| < eps / 2 := by
      rw [abs_lt]
      constructor <;> linarith
    have : eps / 2 < eps := by linarith
    linarith
  exact (Filter.eventually_const.mp hfalse : False)

/-- The main equivalence: epsilon-delta continuity iff nonstandard continuity. -/
theorem continuousAt_iff_nsContinuousAt (f : ℚ → ℚ) (a : ℚ) :
    ContinuousAt f a ↔ NSContinuousAt f a :=
  ⟨continuousAt_implies_nsContinuousAt, nsContinuousAt_implies_continuousAt⟩

/-! ## Infinitesimal Algebra -/

/-- Zero is infinitesimal. -/
theorem infinitesimal_zero : Infinitesimal 0 := by
  intro q hq
  constructor
  · have h : ofRat (-q) < ofRat 0 := by rw [ofRat_lt_ofRat]; linarith
    simp only [ofRat] at h ⊢
    convert h using 1
  · have h : ofRat 0 < ofRat q := by rw [ofRat_lt_ofRat]; exact hq
    simp only [ofRat] at h ⊢
    convert h using 1

/-- Negation preserves infinitesimals. -/
theorem Infinitesimal.neg {x : ℚ*} (hx : Infinitesimal x) : Infinitesimal (-x) := by
  intro q hq
  obtain ⟨hlo, hhi⟩ := hx q hq
  constructor
  · rw [ofRat_neg]
    exact neg_lt_neg hhi
  · have h := neg_lt_neg hlo
    simp only [ofRat_neg, neg_neg] at h
    exact h

/-- Sum of infinitesimals is infinitesimal. -/
theorem Infinitesimal.add {x y : ℚ*} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x + y) := by
  intro q hq
  have hq2 : 0 < q / 2 := by linarith
  obtain ⟨hxlo, hxhi⟩ := hx (q / 2) hq2
  obtain ⟨hylo, hyhi⟩ := hy (q / 2) hq2
  constructor
  · have h1 : ofRat (-q) = ofRat (-(q/2)) + ofRat (-(q/2)) := by
      rw [← ofRat_add]; congr 1; ring
    rw [h1]
    exact add_lt_add hxlo hylo
  · have h2 : ofRat (q/2) + ofRat (q/2) = ofRat q := by
      rw [← ofRat_add]; congr 1; ring
    rw [← h2]
    exact add_lt_add hxhi hyhi

/-- Difference of infinitesimals is infinitesimal. -/
theorem Infinitesimal.sub {x y : ℚ*} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

/-- Product of infinitesimal and HFinite is infinitesimal. -/
theorem Infinitesimal.mul_hFinite {x y : ℚ*} (hx : Infinitesimal x) (hy : HFinite y) :
    Infinitesimal (x * y) := by
  sorry

/-- Product of HFinite and infinitesimal is infinitesimal. -/
theorem HFinite.mul_infinitesimal {x y : ℚ*} (hx : HFinite x) (hy : Infinitesimal y) :
    Infinitesimal (x * y) := by
  sorry

/-- Product of two infinitesimals is infinitesimal. -/
theorem Infinitesimal.mul {x y : ℚ*} (hx : Infinitesimal x) (hy : Infinitesimal y) :
    Infinitesimal (x * y) := by
  sorry

/-! ## HFinite Algebra -/

/-- Standard rationals are HFinite. -/
theorem hFinite_ofRat (q : ℚ) : HFinite (ofRat q) := by
  intro hinf
  rcases hinf with hpos | hneg
  · have := hpos q
    simp at this
  · have := hneg q
    simp at this

/-- Sum of HFinite is HFinite. -/
theorem HFinite.add {x y : ℚ*} (hx : HFinite x) (hy : HFinite y) : HFinite (x + y) := by
  intro hinf
  -- hx : ¬Infinite x means ¬InfinitePos x ∧ ¬InfiniteNeg x
  -- From ¬InfinitePos x we get ∃ qx, x ≤ ofRat qx
  -- From ¬InfiniteNeg x we get ∃ qx', ofRat qx' ≤ x
  simp only [HFinite, Infinite, not_or] at hx hy
  obtain ⟨hx_not_pos, hx_not_neg⟩ := hx
  obtain ⟨hy_not_pos, hy_not_neg⟩ := hy
  simp only [InfinitePos, InfiniteNeg, not_forall, not_lt] at hx_not_pos hx_not_neg hy_not_pos hy_not_neg
  obtain ⟨qx_hi, hx_hi⟩ := hx_not_pos
  obtain ⟨qx_lo, hx_lo⟩ := hx_not_neg
  obtain ⟨qy_hi, hy_hi⟩ := hy_not_pos
  obtain ⟨qy_lo, hy_lo⟩ := hy_not_neg
  rcases hinf with hpos | hneg
  · -- InfinitePos (x + y), so for all q, ofRat q < x + y
    have hbound : x + y ≤ ofRat (qx_hi + qy_hi) := by
      have h1 : ofRat qx_hi + ofRat qy_hi = ofRat (qx_hi + qy_hi) := by rw [← ofRat_add]
      rw [← h1]
      exact add_le_add hx_hi hy_hi
    have hcontra := hpos (qx_hi + qy_hi)
    exact not_lt.mpr hbound hcontra
  · -- InfiniteNeg (x + y), so for all q, x + y < ofRat q
    have hbound : ofRat (qx_lo + qy_lo) ≤ x + y := by
      have h1 : ofRat qx_lo + ofRat qy_lo = ofRat (qx_lo + qy_lo) := by rw [← ofRat_add]
      rw [← h1]
      exact add_le_add hx_lo hy_lo
    have hcontra := hneg (qx_lo + qy_lo)
    exact not_lt.mpr hbound hcontra

/-- Negation of HFinite is HFinite. -/
theorem HFinite.neg {x : ℚ*} (hx : HFinite x) : HFinite (-x) := by
  intro hinf
  apply hx
  rcases hinf with hpos | hneg
  · right
    intro q
    have := hpos (-q)
    simp only [ofRat_neg, neg_lt_neg_iff] at this
    exact this
  · left
    intro q
    have := hneg (-q)
    simp only [ofRat_neg, neg_lt_neg_iff] at this
    exact this

/-- Difference of HFinite is HFinite. -/
theorem HFinite.sub {x y : ℚ*} (hx : HFinite x) (hy : HFinite y) : HFinite (x - y) := by
  rw [sub_eq_add_neg]
  exact hx.add hy.neg

/-- Product of HFinite is HFinite. -/
theorem HFinite.mul {x y : ℚ*} (hx : HFinite x) (hy : HFinite y) : HFinite (x * y) := by
  sorry

/-- Infinitesimals are HFinite. -/
theorem Infinitesimal.hFinite {x : ℚ*} (hx : Infinitesimal x) : HFinite x := by
  intro hinf
  rcases hinf with hpos | hneg
  · -- InfinitePos x, so for all q, ofRat q < x
    -- But x is infinitesimal, so x < ofRat 1
    have h := (hx 1 one_pos).2
    have hp := hpos 1
    exact not_lt.mpr (le_of_lt h) hp
  · -- InfiniteNeg x, so for all q, x < ofRat q
    -- But x is infinitesimal, so ofRat (-1) < x
    have h := (hx 1 one_pos).1
    have hn := hneg (-1)
    simp only [ofRat_neg] at h
    exact not_lt.mpr (le_of_lt hn) h

/-! ## Infinite Properties -/

/-- Infinite positives are positive. -/
theorem InfinitePos.ne_zero {x : ℚ*} (hx : InfinitePos x) : x ≠ 0 :=
  hx.pos.ne'

/-- Inverse of nonzero infinitesimal is infinite. -/
theorem Infinitesimal.inv_infinite {x : ℚ*} (hx : Infinitesimal x) (hne : x ≠ 0) :
    Infinite x⁻¹ := by
  sorry

/-- Inverse of positive infinite is positive infinitesimal. -/
theorem InfinitePos.inv_infinitesimal {x : ℚ*} (hx : InfinitePos x) :
    Infinitesimal x⁻¹ := by
  -- For InfinitePos x: for all q, ofRat q < x
  -- Need to show x⁻¹ is infinitesimal: for all q > 0, |x⁻¹| < ofRat q
  intro q hq
  have hx_pos := hx.pos
  have hx_ne : x ≠ 0 := hx_pos.ne'
  constructor
  · -- ofRat (-q) < x⁻¹
    -- Since x > 0, x⁻¹ > 0 > -q
    have : (0 : ℚ*) < x⁻¹ := inv_pos_of_pos hx_pos
    calc ofRat (-q) < 0 := by rw [ofRat_lt_ofRat]; linarith
      _ < x⁻¹ := this
  · -- x⁻¹ < ofRat q
    -- Since x > ofRat (q⁻¹) and both positive, x⁻¹ < ofRat q
    have hqinv : ofRat (q⁻¹) < x := hx (q⁻¹)
    have hqinv_pos : (0 : ℚ*) < ofRat (q⁻¹) := by rw [ofRat_lt_ofRat]; positivity
    -- x⁻¹ < (ofRat (q⁻¹))⁻¹ = ofRat q
    have hinv : x⁻¹ < (ofRat (q⁻¹))⁻¹ := inv_lt_inv_of_lt hqinv_pos hqinv
    simp only [ofRat] at hinv ⊢
    convert hinv using 1
    simp only [ofSeq_eq_ofSeq]
    exact Eventually.of_forall fun _ => inv_inv q

/-- omega * epsilon is infinitely close to 1.
    Note: ω * ε ≠ 1 exactly since n/(n+1) ≠ 1, but n/(n+1) → 1. -/
theorem omega_mul_epsilon_infClose : InfClose (ω * ε) 1 := by
  -- ω * ε = ofSeq (fun n => n * (n+1)⁻¹) = ofSeq (fun n => n / (n+1))
  -- 1 = ofRat 1 = ofSeq (fun _ => 1)
  -- ω * ε - 1 = ofSeq (fun n => n/(n+1) - 1) = ofSeq (fun n => -1/(n+1))
  -- This is infinitesimal
  unfold InfClose Infinitesimal
  intro q hq
  -- Need: ofRat (-q) < ω * ε - 1 ∧ ω * ε - 1 < ofRat q
  have heq : ω * ε - 1 = ofSeq (fun n => n * (Nat.succ n : ℚ)⁻¹ - 1) := rfl
  rw [heq]
  constructor
  · -- ofRat (-q) < ofSeq (fun n => n/(n+1) - 1)
    rw [ofRat, ofSeq_lt_ofSeq]
    exact Eventually.of_forall fun n => by
      -- n/(n+1) - 1 = -1/(n+1) > -q since 1/(n+1) < q for large n
      have h1 : n * (Nat.succ n : ℚ)⁻¹ - 1 = -((Nat.succ n : ℚ)⁻¹) := by
        field_simp
        ring
      rw [h1]
      have h2 : 0 < (Nat.succ n : ℚ)⁻¹ := by positivity
      linarith
  · -- ofSeq (fun n => n/(n+1) - 1) < ofRat q
    rw [ofRat, ofSeq_lt_ofSeq]
    apply Nat.hyperfilter_le_atTop
    apply eventually_atTop.mpr
    obtain ⟨N, hN⟩ := exists_nat_gt q⁻¹
    use N
    intro n hn
    have h1 : n * (Nat.succ n : ℚ)⁻¹ - 1 = -((Nat.succ n : ℚ)⁻¹) := by
      field_simp
      ring
    rw [h1]
    have hN1_pos : (0 : ℚ) < N + 1 := by positivity
    have hn1_pos : (0 : ℚ) < n + 1 := by positivity
    have hinv_le : (Nat.succ n : ℚ)⁻¹ ≤ (N + 1 : ℚ)⁻¹ := by
      apply inv_anti₀ hN1_pos
      simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
      exact_mod_cast Nat.add_le_add_right hn 1
    have hinv_lt : (N + 1 : ℚ)⁻¹ < q := by
      rw [inv_lt_comm₀ hN1_pos hq]
      calc q⁻¹ < N := hN
        _ < N + 1 := by linarith
    linarith

/-- epsilon is infinitesimal. -/
theorem infinitesimal_epsilon : Infinitesimal ε := by
  intro q hq
  -- ε = ofSeq (fun n => (n+1)⁻¹)
  -- Need: ofRat (-q) < ε and ε < ofRat q
  constructor
  · -- ofRat (-q) < ε
    rw [epsilon, ofRat, ofSeq_lt_ofSeq]
    exact Eventually.of_forall fun n => by
      have : 0 < (Nat.succ n : ℚ)⁻¹ := by positivity
      linarith
  · -- ε < ofRat q
    -- Need to show: eventually (n+1)⁻¹ < q
    -- This holds for n large enough that (n+1)⁻¹ < q, i.e., n+1 > q⁻¹
    rw [epsilon, ofRat, ofSeq_lt_ofSeq]
    apply Nat.hyperfilter_le_atTop
    apply eventually_atTop.mpr
    -- Find N such that (N+1)⁻¹ < q
    obtain ⟨N, hN⟩ := exists_nat_gt q⁻¹
    use N
    intro n hn
    have hN1_pos : (0 : ℚ) < N + 1 := by positivity
    have hn1_pos : (0 : ℚ) < n + 1 := by positivity
    calc (Nat.succ n : ℚ)⁻¹ = (n + 1 : ℚ)⁻¹ := by norm_cast
      _ ≤ (N + 1 : ℚ)⁻¹ := by
        apply inv_anti₀ hN1_pos
        exact_mod_cast Nat.add_le_add_right hn 1
      _ < q := by
        rw [inv_lt_comm₀ hN1_pos hq]
        calc q⁻¹ < N := hN
          _ < N + 1 := by linarith

/-! ## Star Function Properties -/

/-- Star preserves addition. -/
theorem star_add (f g : ℚ → ℚ) (x : ℚ*) :
    star (fun q => f q + g q) x = star f x + star g x := by
  rcases ofSeq_surjective x with ⟨s, rfl⟩
  rfl

/-- Star preserves multiplication. -/
theorem star_mul (f g : ℚ → ℚ) (x : ℚ*) :
    star (fun q => f q * g q) x = star f x * star g x := by
  rcases ofSeq_surjective x with ⟨s, rfl⟩
  rfl

/-- Star preserves negation. -/
theorem star_neg (f : ℚ → ℚ) (x : ℚ*) :
    star (fun q => -f q) x = -star f x := by
  rcases ofSeq_surjective x with ⟨s, rfl⟩
  rfl

/-- Star of identity is identity. -/
theorem star_id (x : ℚ*) : star id x = x := by
  rcases ofSeq_surjective x with ⟨s, rfl⟩
  rfl

/-- Star of constant is constant. -/
theorem star_const (c : ℚ) (x : ℚ*) : star (fun _ => c) x = ofRat c := by
  rcases ofSeq_surjective x with ⟨s, rfl⟩
  rfl

/-! ## InfClose Properties -/

/-- x ≈ y implies x + z ≈ y + z. -/
theorem InfClose.add_right {x y : ℚ*} (h : InfClose x y) (z : ℚ*) : InfClose (x + z) (y + z) := by
  unfold InfClose at h ⊢
  have heq : (x + z) - (y + z) = x - y := by ring
  rw [heq]
  exact h

/-- x ≈ y implies z + x ≈ z + y. -/
theorem InfClose.add_left {x y : ℚ*} (h : InfClose x y) (z : ℚ*) : InfClose (z + x) (z + y) := by
  unfold InfClose at h ⊢
  have heq : (z + x) - (z + y) = x - y := by ring
  rw [heq]
  exact h

/-- x ≈ y and z ≈ w implies x + z ≈ y + w. -/
theorem InfClose.add {x y z w : ℚ*} (hxy : InfClose x y) (hzw : InfClose z w) :
    InfClose (x + z) (y + w) := by
  unfold InfClose at hxy hzw ⊢
  have heq : (x + z) - (y + w) = (x - y) + (z - w) := by ring
  rw [heq]
  exact hxy.add hzw

/-- x ≈ y implies -x ≈ -y. -/
theorem InfClose.neg {x y : ℚ*} (h : InfClose x y) : InfClose (-x) (-y) := by
  unfold InfClose at h ⊢
  have heq : (-x) - (-y) = -(x - y) := by ring
  rw [heq]
  exact h.neg

/-- x ≈ y and z ≈ w implies x - z ≈ y - w. -/
theorem InfClose.sub {x y z w : ℚ*} (hxy : InfClose x y) (hzw : InfClose z w) :
    InfClose (x - z) (y - w) := by
  unfold InfClose at hxy hzw ⊢
  have heq : (x - z) - (y - w) = (x - y) - (z - w) := by ring
  rw [heq]
  exact hxy.sub hzw

/-- HFinite x ≈ y and HFinite z ≈ w implies x * z ≈ y * w. -/
theorem InfClose.mul {x y z w : ℚ*} (hxy : InfClose x y) (hzw : InfClose z w)
    (hx : HFinite x) (hz : HFinite z) : InfClose (x * z) (y * w) := by
  sorry

/-! ## Sequence Extensions and Convergence

The key insight of nonstandard analysis: a sequence `s : ℕ → ℚ` can be extended
to `s* : ℕ* → ℚ*` (the "star extension"). This allows us to characterize
convergence and Cauchy properties using infinitesimals.
-/

/-- Star extension of a sequence `s : ℕ → ℚ` to `s* : ℕ* → ℚ*`.
    For standard n, (starSeq s) n = s n. For nonstandard N, it's defined via the ultrapower. -/
noncomputable def starSeq (s : ℕ → ℚ) : Hypernatural → ℚ* :=
  fun x => Quotient.liftOn x (fun f => ofSeq (s ∘ f))
    (fun f₁ f₂ hf => by
      apply ofSeq_eq_ofSeq.mpr
      filter_upwards [hf] with n hn
      simp [hn])

@[simp]
lemma starSeq_ofNat (s : ℕ → ℚ) (n : ℕ) : starSeq s (Hypernatural.ofNat n) = ofRat (s n) := by
  -- Hypernatural.ofNat n = const n = Germ of (fun _ => n)
  -- starSeq s (const n) = ofSeq (s ∘ (fun _ => n)) = ofSeq (fun _ => s n) = ofRat (s n)
  rfl

@[simp]
lemma starSeq_ofSeq (s : ℕ → ℚ) (f : ℕ → ℕ) :
    starSeq s (Hypernatural.ofSeq f) = ofSeq (s ∘ f) := rfl

/-! ### Nonstandard Characterization of Convergence -/

/-- Standard epsilon-delta definition of sequence convergence. -/
def SeqConvergesTo (s : ℕ → ℚ) (L : ℚ) : Prop :=
  ∀ eps : ℚ, 0 < eps → ∃ N : ℕ, ∀ n ≥ N, |s n - L| < eps

/-- Nonstandard characterization: s converges to L iff for all infinite N, s*(N) ≈ L. -/
def NSSeqConvergesTo (s : ℕ → ℚ) (L : ℚ) : Prop :=
  ∀ N : Hypernatural, Hypernatural.Infinite N → InfClose (starSeq s N) (ofRat L)

/-- Standard definition of Cauchy sequence. -/
def IsCauchy (s : ℕ → ℚ) : Prop :=
  ∀ eps : ℚ, 0 < eps → ∃ N : ℕ, ∀ m n, m ≥ N → n ≥ N → |s m - s n| < eps

/-- Nonstandard characterization of Cauchy: for all infinite M, N, s*(M) ≈ s*(N). -/
def NSIsCauchy (s : ℕ → ℚ) : Prop :=
  ∀ M N : Hypernatural, Hypernatural.Infinite M → Hypernatural.Infinite N →
    InfClose (starSeq s M) (starSeq s N)

/-! ### Equivalence Theorems -/

/-- Standard convergence implies nonstandard convergence. -/
theorem seqConvergesTo_implies_nsSeqConvergesTo {s : ℕ → ℚ} {L : ℚ}
    (h : SeqConvergesTo s L) : NSSeqConvergesTo s L := by
  intro N hN
  -- N is infinite, need to show starSeq s N ≈ ofRat L
  unfold InfClose Infinitesimal
  intro eps heps
  -- By convergence, ∃ N₀ such that ∀ n ≥ N₀, |s n - L| < eps
  obtain ⟨N₀, hN₀⟩ := h eps heps
  -- Since N is infinite, N > N₀, so eventually f(n) ≥ N₀
  rcases Hypernatural.ofSeq_surjective N with ⟨f, rfl⟩
  -- Eventually f(n) ≥ N₀ because N is infinite
  have hf_large : ∀ᶠ n in hyperfilter ℕ, N₀ ≤ f n := by
    have := hN N₀
    rw [Hypernatural.ofSeq_lt_ofSeq] at this
    filter_upwards [this] with n hn
    omega
  -- So eventually |s(f(n)) - L| < eps
  have h_bound : ∀ᶠ n in hyperfilter ℕ, |s (f n) - L| < eps := by
    filter_upwards [hf_large] with n hn
    exact hN₀ (f n) hn
  constructor
  · -- ofRat (-eps) < starSeq s (ofSeq f) - ofRat L
    change ofRat (-eps) < ofSeq (s ∘ f) - ofRat L
    rw [show ofSeq (s ∘ f) - ofRat L = ofSeq (fun n => s (f n) - L) from rfl]
    rw [ofRat, ofSeq_lt_ofSeq]
    filter_upwards [h_bound] with n hn
    rw [abs_lt] at hn
    linarith
  · -- starSeq s (ofSeq f) - ofRat L < ofRat eps
    change ofSeq (s ∘ f) - ofRat L < ofRat eps
    rw [show ofSeq (s ∘ f) - ofRat L = ofSeq (fun n => s (f n) - L) from rfl]
    rw [ofRat, ofSeq_lt_ofSeq]
    filter_upwards [h_bound] with n hn
    rw [abs_lt] at hn
    exact hn.2

/-- Nonstandard convergence implies standard convergence. -/
theorem nsSeqConvergesTo_implies_seqConvergesTo {s : ℕ → ℚ} {L : ℚ}
    (h : NSSeqConvergesTo s L) : SeqConvergesTo s L := by
  -- By contraposition: if s does not converge to L, we construct an infinite N
  -- such that s*(N) is not infinitely close to L
  by_contra hbad
  simp only [SeqConvergesTo, not_forall, not_exists, not_and, not_lt] at hbad
  obtain ⟨eps, heps_pos, hbad'⟩ := hbad
  -- For each k, pick n_k ≥ k with |s(n_k) - L| ≥ eps
  have hex : ∀ k : ℕ, ∃ n : ℕ, k ≤ n ∧ eps ≤ |s n - L| := by
    intro k
    have := hbad' k
    simp only [exists_prop] at this ⊢
    obtain ⟨n, hn1, hn2⟩ := this
    exact ⟨n, hn1, hn2⟩
  choose f hf using hex
  -- f is a sequence with f(k) ≥ k and |s(f(k)) - L| ≥ eps for all k
  -- So N = ofSeq f is infinite
  let N : Hypernatural := Hypernatural.ofSeq f
  have hN_infinite : Hypernatural.Infinite N := by
    intro k
    rw [Hypernatural.ofSeq_lt_ofSeq]
    exact Eventually.of_forall fun n => by
      have := (hf n).1
      omega
  -- By nonstandard convergence, starSeq s N ≈ ofRat L
  have hclose := h N hN_infinite
  -- But |s(f(k)) - L| ≥ eps for all k, contradiction
  unfold InfClose Infinitesimal at hclose
  have h_half := hclose (eps / 2) (by linarith)
  have hlo : ofRat (-(eps / 2)) < starSeq s N - ofRat L := h_half.1
  have hhi : starSeq s N - ofRat L < ofRat (eps / 2) := h_half.2
  change ofRat (-(eps / 2)) < ofSeq (s ∘ f) - ofRat L at hlo
  change ofSeq (s ∘ f) - ofRat L < ofRat (eps / 2) at hhi
  rw [show ofSeq (s ∘ f) - ofRat L = ofSeq (fun n => s (f n) - L) from rfl] at hlo hhi
  rw [ofRat, ofSeq_lt_ofSeq] at hlo hhi
  -- Get contradiction: we have |s(f(n)) - L| ≥ eps for all n
  have h_all_bad : ∀ n, eps ≤ |s (f n) - L| := fun n => (hf n).2
  have hfalse : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), False := by
    filter_upwards [hlo, hhi] with n hlo_n hhi_n
    have hge := h_all_bad n
    have hbound : |s (f n) - L| < eps / 2 := by
      rw [abs_lt]
      constructor <;> linarith
    have : eps / 2 < eps := by linarith
    linarith
  exact (Filter.eventually_const.mp hfalse : False)

/-- Convergence characterization: standard ↔ nonstandard. -/
theorem seqConvergesTo_iff_nsSeqConvergesTo (s : ℕ → ℚ) (L : ℚ) :
    SeqConvergesTo s L ↔ NSSeqConvergesTo s L :=
  ⟨seqConvergesTo_implies_nsSeqConvergesTo, nsSeqConvergesTo_implies_seqConvergesTo⟩

/-- Standard Cauchy implies nonstandard Cauchy. -/
theorem isCauchy_implies_nsIsCauchy {s : ℕ → ℚ} (h : IsCauchy s) : NSIsCauchy s := by
  intro M N hM hN
  -- M and N are infinite, need to show starSeq s M ≈ starSeq s N
  unfold InfClose Infinitesimal
  intro eps heps
  -- By Cauchy property, ∃ K such that ∀ m n ≥ K, |s m - s n| < eps
  obtain ⟨K, hK⟩ := h eps heps
  -- Since M and N are infinite, eventually f(n) ≥ K and g(n) ≥ K
  rcases Hypernatural.ofSeq_surjective M with ⟨f, rfl⟩
  rcases Hypernatural.ofSeq_surjective N with ⟨g, rfl⟩
  have hf_large : ∀ᶠ n in hyperfilter ℕ, K ≤ f n := by
    have := hM K
    rw [Hypernatural.ofSeq_lt_ofSeq] at this
    filter_upwards [this] with n hn
    omega
  have hg_large : ∀ᶠ n in hyperfilter ℕ, K ≤ g n := by
    have := hN K
    rw [Hypernatural.ofSeq_lt_ofSeq] at this
    filter_upwards [this] with n hn
    omega
  -- So eventually |s(f(n)) - s(g(n))| < eps
  have h_bound : ∀ᶠ n in hyperfilter ℕ, |s (f n) - s (g n)| < eps := by
    filter_upwards [hf_large, hg_large] with n hfn hgn
    exact hK (f n) (g n) hfn hgn
  constructor
  · -- ofRat (-eps) < starSeq s M - starSeq s N
    change ofRat (-eps) < ofSeq (s ∘ f) - ofSeq (s ∘ g)
    rw [show ofSeq (s ∘ f) - ofSeq (s ∘ g) = ofSeq (fun n => s (f n) - s (g n)) from rfl]
    rw [ofRat, ofSeq_lt_ofSeq]
    filter_upwards [h_bound] with n hn
    rw [abs_lt] at hn
    linarith
  · -- starSeq s M - starSeq s N < ofRat eps
    change ofSeq (s ∘ f) - ofSeq (s ∘ g) < ofRat eps
    rw [show ofSeq (s ∘ f) - ofSeq (s ∘ g) = ofSeq (fun n => s (f n) - s (g n)) from rfl]
    rw [ofRat, ofSeq_lt_ofSeq]
    filter_upwards [h_bound] with n hn
    rw [abs_lt] at hn
    exact hn.2

/-- Nonstandard Cauchy implies standard Cauchy. -/
theorem nsIsCauchy_implies_isCauchy {s : ℕ → ℚ} (h : NSIsCauchy s) : IsCauchy s := by
  -- By contraposition: if s is not Cauchy, we construct infinite M, N
  -- such that s*(M) is not infinitely close to s*(N)
  by_contra hbad
  simp only [IsCauchy, not_forall, not_exists, not_and, not_lt] at hbad
  obtain ⟨eps, heps_pos, hbad'⟩ := hbad
  -- For each k, pick m_k, n_k ≥ k with |s(m_k) - s(n_k)| ≥ eps
  have hex : ∀ k : ℕ, ∃ m n : ℕ, k ≤ m ∧ k ≤ n ∧ eps ≤ |s m - s n| := by
    intro k
    have := hbad' k
    simp only [not_forall, not_lt] at this
    obtain ⟨m, n, hm, hn, hmn⟩ := this
    exact ⟨m, n, hm, hn, hmn⟩
  choose f g hfg using hex
  -- f, g are sequences with f(k), g(k) ≥ k and |s(f(k)) - s(g(k))| ≥ eps
  -- So M = ofSeq f and N = ofSeq g are infinite
  let M : Hypernatural := Hypernatural.ofSeq f
  let N : Hypernatural := Hypernatural.ofSeq g
  have hM_infinite : Hypernatural.Infinite M := by
    intro k
    rw [Hypernatural.ofSeq_lt_ofSeq]
    exact Eventually.of_forall fun n => by
      have := (hfg n).1
      omega
  have hN_infinite : Hypernatural.Infinite N := by
    intro k
    rw [Hypernatural.ofSeq_lt_ofSeq]
    exact Eventually.of_forall fun n => by
      have := (hfg n).2.1
      omega
  -- By nonstandard Cauchy, starSeq s M ≈ starSeq s N
  have hclose := h M N hM_infinite hN_infinite
  -- But |s(f(k)) - s(g(k))| ≥ eps for all k, contradiction
  unfold InfClose Infinitesimal at hclose
  have h_half := hclose (eps / 2) (by linarith)
  have hlo : ofRat (-(eps / 2)) < starSeq s M - starSeq s N := h_half.1
  have hhi : starSeq s M - starSeq s N < ofRat (eps / 2) := h_half.2
  change ofRat (-(eps / 2)) < ofSeq (s ∘ f) - ofSeq (s ∘ g) at hlo
  change ofSeq (s ∘ f) - ofSeq (s ∘ g) < ofRat (eps / 2) at hhi
  rw [show ofSeq (s ∘ f) - ofSeq (s ∘ g) = ofSeq (fun n => s (f n) - s (g n)) from rfl] at hlo hhi
  rw [ofRat, ofSeq_lt_ofSeq] at hlo hhi
  -- Get contradiction: we have |s(f(n)) - s(g(n))| ≥ eps for all n
  have h_all_bad : ∀ n, eps ≤ |s (f n) - s (g n)| := fun n => (hfg n).2.2
  have hfalse : ∀ᶠ n in (hyperfilter ℕ : Filter ℕ), False := by
    filter_upwards [hlo, hhi] with n hlo_n hhi_n
    have hge := h_all_bad n
    have hbound : |s (f n) - s (g n)| < eps / 2 := by
      rw [abs_lt]
      constructor <;> linarith
    have : eps / 2 < eps := by linarith
    linarith
  exact (Filter.eventually_const.mp hfalse : False)

/-- Cauchy characterization: standard ↔ nonstandard. -/
theorem isCauchy_iff_nsIsCauchy (s : ℕ → ℚ) : IsCauchy s ↔ NSIsCauchy s :=
  ⟨isCauchy_implies_nsIsCauchy, nsIsCauchy_implies_isCauchy⟩

/-! ### Series and Summability -/

/-- Partial sums of a sequence. -/
def partialSum (s : ℕ → ℚ) : ℕ → ℚ := fun n => (Finset.range n).sum s

/-- A series converges if its partial sums converge. -/
def SeriesConverges (s : ℕ → ℚ) : Prop := ∃ L, SeqConvergesTo (partialSum s) L

/-- Nonstandard series convergence. -/
def NSSeriesConverges (s : ℕ → ℚ) : Prop := ∃ L, NSSeqConvergesTo (partialSum s) L

/-- Series convergence characterization. -/
theorem seriesConverges_iff_nsSeriesConverges (s : ℕ → ℚ) :
    SeriesConverges s ↔ NSSeriesConverges s := by
  simp only [SeriesConverges, NSSeriesConverges, seqConvergesTo_iff_nsSeqConvergesTo]

end Hyperrational
