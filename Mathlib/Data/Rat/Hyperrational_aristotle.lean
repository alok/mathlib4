/-
This file was edited by Aristotle.

Lean Toolchain version: leanprover/lean4:v4.20.0-rc5
Mathlib version: d62eab0cc36ea522904895389c301cf8d844fd69 (May 9, 2025)

The following was proved by Aristotle:

- theorem continuousAt_implies_nsContinuousAt {f : ℚ → ℚ} {a : ℚ}
    (hf : ContinuousAt f a) : NSContinuousAt f a

- theorem nsContinuousAt_implies_continuousAt {f : ℚ → ℚ} {a : ℚ}
    (hf : NSContinuousAt f a) : ContinuousAt f a
-/

/-
Copyright (c) 2024 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Mathlib.Order.Filter.FilterProduct
import Mathlib.Analysis.SpecificLimits.Basic


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
  -- The key insight: x - ofRat a is infinitesimal, so for any standard delta,
  -- |x - a| < delta holds ultrafilter-almost-everywhere.
  -- By epsilon-delta continuity, |f(x) - f(a)| < eps ultrafilter-almost-everywhere.
  -- By definition of hyperreal inequality, if $|x - a| < \delta$, then $|f(x) - f(a)| < \epsilon$.
  have h_ineq : ∀ x : ℚ, |x - a| < delta → |f x - f a| < eps := by
    -- Apply the hypothesis `hdelta` directly to conclude the proof.
    apply hdelta;
  obtain ⟨y, hy⟩ : ∃ y : ℕ → ℚ, x = ofSeq y := by
    simpa [ eq_comm ] using ofSeq_surjective x;
  have h_seq : ∀ᶠ n in hyperfilter ℕ, |y n - a| < delta := by
    aesop;
    have := hx delta hdelta_pos;
    erw [ ofSeq_lt_ofSeq, ofSeq_lt_ofSeq ] at this ; aesop;
    filter_upwards [ left, right ] with n hn₁ hn₂ using abs_lt.mpr ⟨ by linarith, by linarith ⟩;
  aesop;
  · have h_seq : ∀ᶠ n in hyperfilter ℕ, f (y n) - f a > -eps := by
      filter_upwards [ h_seq ] with n hn using by linarith [ abs_lt.mp ( h_ineq ( y n ) hn ) ] ;
    erw [ Hyperrational.ofSeq_lt_ofSeq ] ; aesop;
  · erw [ ofSeq_lt_ofSeq ] ; aesop;
    filter_upwards [ h_seq ] with n hn using lt_of_abs_lt ( h_ineq _ hn )

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
    -- This follows because |s_n - a| < 1/(n+1) and 1/(n+1) → 0
    -- Since $|s_n - a| < \frac{1}{n+1}$ and $\frac{1}{n+1} < q$ for sufficiently large $n$, we have $|s_n - a| < q$ for those $n$.
    have h_bound : ∀ᶠ n in hyperfilter ℕ, |s n - a| < q := by
      -- Since $|s_n - a| < \frac{1}{n+1}$ and $\frac{1}{n+1} < q$ for sufficiently large $n$, we have $|s_n - a| < q$ for those $n$. Therefore, the set $\{n \mid |s_n - a| < q\}$ is cofinite.
      have h_cofinite : ∀ᶠ n in Filter.atTop, |s n - a| < q := by
        exact Filter.eventually_atTop.mpr ⟨ ⌈q⁻¹⌉₊, fun n hn => lt_of_lt_of_le ( hs n |>.1 ) ( inv_le_of_inv_le₀ hq <| by linarith [ Nat.ceil_le.mp hn ] ) ⟩;
      norm_num +zetaDelta at *;
      exact Filter.mem_of_superset ( Filter.mem_hyperfilter_of_finite_compl ( Set.finite_iff_bddAbove.mpr ⟨ h_cofinite.choose, fun n hn => not_lt.mp fun contra => hn <| h_cofinite.choose_spec n contra.le ⟩ ) ) fun n hn => hn;
    constructor <;> refine' ofSeq_lt_ofSeq.mpr _;
    · filter_upwards [ h_bound ] with n hn using by linarith [ abs_lt.mp hn ] ;
    · filter_upwards [ h_bound ] with n hn using lt_of_le_of_lt ( le_abs_self _ ) hn
  -- By nonstandard continuity, f*(x) should be infinitely close to f(a)
  have hfx_close := hf x hx_close
  -- But by construction, |f(s_n) - f(a)| ≥ eps for all n, contradiction
  unfold InfClose Infinitesimal at hfx_close
  have h_half := hfx_close (eps / 2) (by linarith)
  -- The contradiction: f*(x) - f(a) is both < eps/2 and ≥ eps ultrafilter-a.e.
  -- Since each term in the sequence $f(s_n) - f(a)$ is at least $\epsilon$, the hyperrational constructed from this sequence should also be at least $\epsilon$.
  have h_seq_ge_eps : ∀ᶠ n in hyperfilter ℕ, f (s n) - f a ≥ eps := by
    have h_seq_ge_eps : ∀ᶠ n in hyperfilter ℕ, f (s n) - f a ≥ eps ∨ f (s n) - f a ≤ -eps := by
      exact Filter.Eventually.of_forall fun n => abs_cases ( f ( s n ) - f a ) |> Or.imp ( fun h => by linarith [ hs n ] ) fun h => by linarith [ hs n ] ;
    -- Since the hyperrational is greater than -eps/2, the sequence must be eventually greater than -eps/2.
    have h_seq_ge_eps : ∀ᶠ n in hyperfilter ℕ, f (s n) - f a > -eps / 2 := by
      have h_hyperrational : Hyperrational.ofRat (-eps / 2) < Hyperrational.star f x - Hyperrational.ofRat (f a) := by
        simpa only [ neg_div ] using h_half.1
      exact?;
    filter_upwards [ ‹∀ᶠ n in ( Filter.hyperfilter ℕ : Filter ℕ ), f ( s n ) - f a ≥ eps ∨ f ( s n ) - f a ≤ -eps›, h_seq_ge_eps ] with n hn hn' using Or.resolve_right hn fun h => by linarith;
  have h_hyperrational_ge_eps : star f x - ofRat (f a) ≥ ofRat eps := by
    exact h_seq_ge_eps;
  -- Combining the inequalities from h_hyperrational_ge_eps and h_half, we get a contradiction because ε is positive.
  have h_contradiction : ofRat eps ≤ star f x - ofRat (f a) ∧ star f x - ofRat (f a) < ofRat (eps / 2) := by
    exact ⟨ h_hyperrational_ge_eps, h_half.2 ⟩;
  exact h_contradiction.2.not_le ( le_trans ( ofRat_le_ofRat.mpr ( by linarith ) ) h_contradiction.1 )

/-- The main equivalence: epsilon-delta continuity iff nonstandard continuity. -/
theorem continuousAt_iff_nsContinuousAt (f : ℚ → ℚ) (a : ℚ) :
    ContinuousAt f a ↔ NSContinuousAt f a :=
  ⟨continuousAt_implies_nsContinuousAt, nsContinuousAt_implies_continuousAt⟩

end Hyperrational