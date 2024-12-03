
/-
Copyright (c) 2024 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Mathlib.Order.Filter.FilterProduct
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Hypernatural
/-!
# Construction of the hyperintegers as an ultraproduct of integer sequences.
-/


open scoped Classical
open Filter Germ Topology

-- TODO represent with inductive (negSucc,etc)?
/-- Hyperintegers on the ultrafilter extending the cofinite filter -/
def Hyperinteger : Type :=
  Germ (hyperfilter ℕ : Filter ℕ) ℤ deriving Inhabited

namespace Hyperinteger

@[inherit_doc] notation "ℤ*" => Hyperinteger

noncomputable instance : LinearOrderedRing ℤ* :=
  inferInstanceAs (LinearOrderedRing (Germ _ _))

/-- Natural embedding `ℕ → ℕ*`. -/
@[coe] def ofInt : ℤ → ℤ* := const

instance : OfNat ℤ* n := ⟨ofInt n⟩

noncomputable instance : CoeTC ℤ ℤ* := ⟨ofInt⟩

noncomputable instance : CoeTC ℕ* ℤ* := sorry
#eval Int
@[simp, norm_cast]
theorem coe_eq_coe {a b : ℤ} : (a : ℤ*) = b ↔ a = b :=
  Germ.const_inj

@[simp, norm_cast]
theorem coe_eq_zero {a : ℤ} : (a : ℤ*) = 0 ↔ a = 0 :=
  coe_eq_coe

@[simp, norm_cast]
theorem coe_eq_one {a : ℤ} : (a : ℤ*) = 1 ↔ a = 1 :=
  coe_eq_coe

@[norm_cast]
theorem coe_ne_zero {a : ℤ} : (a : ℤ*) ≠ 0 ↔ a ≠ 0 :=
  coe_ne_coe

@[norm_cast]
theorem coe_ne_one {a : ℤ} : (a : ℤ*) ≠ 1 ↔ a ≠ 1 :=
  coe_ne_coe

@[simp, norm_cast]
theorem coe_one : ↑(1 : ℤ) = (1 : ℤ*) :=
  rfl

@[simp, norm_cast]
theorem coe_zero : ↑(0 : ℤ) = (0 : ℤ*) :=
  rfl

@[simp, norm_cast]
theorem coe_add (a b : ℤ) : ↑(a + b) = (a + b : ℤ*) :=
  rfl

@[simp, norm_cast]
theorem coe_mul (a b : ℕ) : ↑(a * b) = (a * b : ℕ*) :=
  rfl

@[simp, norm_cast]
theorem coe_div (a b : ℕ) : ↑(a / b) = (a / b : ℕ*) :=
  rfl

@[simp, norm_cast]
theorem coe_sub (a b : ℕ) : ↑(a - b) = (a - b : ℕ*) :=
  rfl

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
theorem coe_abs (a : ℕ) : ((|a| : ℕ) : ℕ*) = |↑a| :=
  const_abs a

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
  coe_pos.2 Nat.cast_pos.2

theorem omega_ne_zero : ω ≠ 0 :=
  omega_pos.ne'

-- TODO: standard iff finite
def IsSt (n : ℕ*) (r : ℕ) :=
  ∀ δ : ℕ, 0 < δ → (r - δ : ℕ*) < n ∧ n < r + δ

/-- The standard part of a hyperinteger. -/
noncomputable def st : ℕ* → ℕ := fun x => if h : ∃ r, IsSt x r then Classical.choose h else 0

/-- A hyperinteger is infinite positive if it is greater than all integers. -/
def InfinitePos (n : ℤ*) :=
  ∀ m : ℤ, ↑m < n

/-- A hyperinteger is infinite negative if it is less than all integers. -/
def InfiniteNeg (n : ℤ*) :=
  ∀ m : ℤ, n < ↑m

-- TODO: finish
theorem omega_infinitePos : InfinitePos ω :=
  fun m => coe_lt_coe.2 (Nat.cast_lt.2 m.prop)

@[inherit_doc InfinitePos]
def Infinite (n : ℕ*) := InfinitePos n ∨ InfiniteNeg n

end Hyperinteger
