
/-
Copyright (c) 2024 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Mathlib.Order.Filter.FilterProduct
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Construction of the hypernatural numbers as an ultraproduct of natural sequences.
-/


open scoped Classical
open Filter Germ Topology


/-- Hypernatural numbers on the ultrafilter extending the cofinite filter -/
def Hypernatural : Type :=
  Germ (hyperfilter ℕ : Filter ℕ) ℕ deriving Inhabited

namespace Hypernatural

@[inherit_doc] notation "ℕ*" => Hypernatural

noncomputable instance : LinearOrderedSemiring ℕ* :=
  inferInstanceAs (LinearOrderedSemiring (Germ _ _))

/-- Natural embedding `ℕ → ℕ*`. -/
@[coe] def ofNat : ℕ → ℕ* := const

-- -- TODO n identifier issue
-- instance : OfNat (ℕ*) n where
--   ofNat := Hypernatural.ofNat n

noncomputable instance : CoeTC ℕ ℕ* := ⟨ofNat⟩
-- No Repr for noncomputables, but this is annoying

@[simp, norm_cast]
theorem coe_eq_coe {a b : ℕ} : (a : ℕ*) = b ↔ a = b :=
  Germ.const_inj

theorem coe_ne_coe {a b : ℕ} : (a : ℕ*) ≠ b ↔ a ≠ b :=
  coe_eq_coe.not

@[simp, norm_cast]
theorem coe_eq_zero {a : ℕ} : (a : ℕ*) = 0 ↔ a = 0 :=
  coe_eq_coe

@[simp, norm_cast]
theorem coe_eq_one {a : ℕ} : (a : ℕ*) = 1 ↔ a = 1 :=
  coe_eq_coe

@[norm_cast]
theorem coe_ne_zero {a : ℕ} : (a : ℕ*) ≠ 0 ↔ a ≠ 0 :=
  coe_eq_zero.not

@[norm_cast]
theorem coe_ne_one {a : ℕ} : (a : ℕ*) ≠ 1 ↔ a ≠ 1 :=
  coe_ne_coe

@[simp, norm_cast]
theorem coe_one : ↑(1 : ℕ) = (1 : ℕ*) :=
  rfl

@[simp, norm_cast]
theorem coe_zero : ↑(0 : ℕ) = (0 : ℕ*) :=
  rfl

@[simp, norm_cast]
theorem coe_add (a b : ℕ) : ↑(a + b) = (a + b : ℕ*) :=
  rfl

@[simp, norm_cast]
theorem coe_mul (a b : ℕ) : ↑(a * b) = (a * b : ℕ*) :=
  rfl

-- @[simp, norm_cast]
-- theorem coe_div (a b : ℕ) : ↑(a / b) = (a / b : ℕ*) :=
--   rfl

-- @[simp, norm_cast]
-- theorem coe_sub (a b : ℕ) : ↑(a - b) = (a - b : ℕ*) :=
--   rfl

@[simp, norm_cast]
theorem coe_le_coe {a b : ℕ} : (a : ℕ*) ≤ b ↔ a ≤ b :=
  Germ.const_le_iff

@[simp, norm_cast]
theorem coe_lt_coe {a b : ℕ} : (a : ℕ*) < b ↔ a < b :=
  Germ.const_lt_iff

@[simp, norm_cast]
theorem coe_nonneg {a : ℕ} : 0 ≤ (a : ℕ*) ↔ 0 ≤ a :=
  coe_le_coe

@[simp, norm_cast]
theorem coe_pos {a : ℕ} : 0 < (a : ℕ*) ↔ 0 < a :=
  coe_lt_coe

@[simp, norm_cast]
theorem coe_max (a b : ℕ) : ((max a b : ℕ) : ℕ*) = max ↑a ↑b :=
  Germ.const_max _ _

@[simp, norm_cast]
theorem coe_min (a b : ℕ) : ((min a b : ℕ) : ℕ*) = min ↑a ↑b :=
  Germ.const_min _ _

/-- Construct a hypernatural number from a sequence of natural numbers. -/
def ofSeq (f : ℕ → ℕ) : ℕ* := (↑f : Germ (hyperfilter ℕ : Filter ℕ) ℕ)

theorem ofSeq_surjective : Function.Surjective ofSeq := Quot.exists_rep

theorem ofSeq_lt_ofSeq {f g : ℕ → ℕ} : ofSeq f < ofSeq g ↔ ∀ᶠ n in hyperfilter ℕ, f n < g n :=
  Germ.coe_lt

/-- A sample infinite hypernatural -/
noncomputable def omega : ℕ* := ofSeq Nat.cast

@[inherit_doc] scoped notation "ω" => Hypernatural.omega

theorem omega_pos : 0 < ω :=
  Germ.coe_pos.2 <| Nat.hyperfilter_le_atTop <| (eventually_gt_atTop 0).mono fun _ ↦
    Nat.cast_pos.2

theorem omega_ne_zero : ω ≠ 0 :=
  omega_pos.ne'

-- TODO: standard iff finite
def IsSt (n : ℕ*) (r : ℕ) :=
  ∀ δ : ℕ, 0 < δ → (r - δ : ℕ*) < n ∧ n < r + δ

noncomputable def st : ℕ* → ℕ := fun x => if h : ∃ r, IsSt x r then Classical.choose h else 0

/-- A hypernatural number is infinite if it is greater than all natural numbers. -/
def InfinitePos (n : ℕ*) :=
  ∀ m : ℕ, ↑m < n

-- -- TODO: finish
-- theorem infinitePos_omega : InfinitePos ω := by
--   intro m
--   unfold omega
--   unfold Nat.cast
--   unfold ofSeq
--   unfold NatCast.natCast
--   unfold instNatCastNat
--   unfold Semiring.toNatCast
--   unfold StrictOrderedSemiring.toSemiring
--   unfold LinearOrderedSemiring.toStrictOrderedSemiring
--   unfold instLinearOrderedSemiring


@[inherit_doc InfinitePos]
def Infinite (n : ℕ*) := InfinitePos n

-- protected theorem IsSt.lt {n : ℕ*} {r : ℕ} (h : IsSt n r) : n < r :=
--   (coe_lt_coe.2 (h.2 1 (Nat.one_pos))).trans_le (coe_le_coe.2 (h.1 r (Nat.cast_pos.2 r.prop)))

-- theorem IsSt.not_infinite {n : ℕ*} {r : ℕ} (h : IsSt n r) : Infinite n → r = 0 :=
--   fun h' => Nat.not_infinite_of_isSt h h'

end Hypernatural
