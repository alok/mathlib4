/-
Copyright (c) 2024 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Mathlib.Order.Filter.FilterProduct
import Mathlib.Order.Filter.Ultrafilter.Hyperfilter
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Int.Order.Basic

/-!
# Hyperinteger numbers

We build the *hyperintegers* `ℤ*` as germs of integer sequences on the
`hyperfilter ℕ`, mirroring the constructions of `ℝ*` and `ℕ*`.
-/

open Classical
open Filter Germ Topology

/-- Hyperintegers on the ultrafilter extending the cofinite filter. -/
noncomputable def Hyperinteger : Type :=
  Germ (hyperfilter ℕ : Filter ℕ) ℤ

namespace Hyperinteger

/-- Notation for hyperintegers. -/
@[inherit_doc] notation "ℤ*" => Hyperinteger

noncomputable instance : Ring ℤ* :=
  inferInstanceAs (Ring (Germ _ _))

noncomputable instance : LinearOrder ℤ* :=
  inferInstanceAs (LinearOrder (Germ _ _))

/-- Natural embedding `ℤ → ℤ*`. -/
@[coe] noncomputable def ofInt : ℤ → ℤ* := const

noncomputable instance : CoeTC ℤ ℤ* := ⟨ofInt⟩

noncomputable instance instOfNat (n : ℕ) : OfNat ℤ* n := ⟨ofInt n⟩

noncomputable instance : Inhabited ℤ* := ⟨ofInt 0⟩

/-- Coercions from `ℤ` to `ℤ*` behave definitionally. -/
@[simp, norm_cast] theorem coe_eq_coe {a b : ℤ} : (a : ℤ*) = b ↔ a = b := Germ.const_inj

theorem coe_ne_coe {a b : ℤ} : (a : ℤ*) ≠ b ↔ a ≠ b := coe_eq_coe.not

@[simp, norm_cast] theorem coe_zero : ((0 : ℤ) : ℤ*) = 0 := rfl
@[simp, norm_cast] theorem coe_one : ((1 : ℤ) : ℤ*) = 1 := rfl
@[simp, norm_cast] theorem coe_add (a b : ℤ) : ((a + b : ℤ) : ℤ*) = a + b := rfl
@[simp, norm_cast] theorem coe_sub (a b : ℤ) : ((a - b : ℤ) : ℤ*) = a - b := rfl
@[simp, norm_cast] theorem coe_mul (a b : ℤ) : ((a * b : ℤ) : ℤ*) = a * b := rfl
@[simp, norm_cast] theorem coe_neg (a : ℤ) : ((-a : ℤ) : ℤ*) = -a := rfl
@[simp, norm_cast] theorem coe_le_coe {a b : ℤ} : (a : ℤ*) ≤ b ↔ a ≤ b := Germ.const_le_iff
@[simp, norm_cast] theorem coe_lt_coe {a b : ℤ} : (a : ℤ*) < b ↔ a < b := Germ.const_lt_iff

/-- Build a hyperinteger from a sequence. -/
noncomputable def ofSeq (f : ℕ → ℤ) : ℤ* := (↑f : Germ (hyperfilter ℕ : Filter ℕ) ℤ)

theorem ofSeq_surjective : Function.Surjective ofSeq := Quot.exists_rep

theorem ofSeq_eq_ofSeq {f g : ℕ → ℤ} : ofSeq f = ofSeq g ↔ ∀ᶠ n in hyperfilter ℕ, f n = g n :=
  Germ.coe_eq

theorem ofSeq_le_ofSeq {f g : ℕ → ℤ} : ofSeq f ≤ ofSeq g ↔ ∀ᶠ n in hyperfilter ℕ, f n ≤ g n :=
  Germ.coe_le

theorem ofSeq_lt_ofSeq {f g : ℕ → ℤ} : ofSeq f < ofSeq g ↔ ∀ᶠ n in hyperfilter ℕ, f n < g n :=
  Germ.coe_lt

/-- Positive infinity predicate. -/
def InfinitePos (x : ℤ*) : Prop := ∀ m : ℤ, (m : ℤ*) < x

/-- Negative infinity predicate. -/
def InfiniteNeg (x : ℤ*) : Prop := ∀ m : ℤ, x < (m : ℤ*)

/-- A hyperinteger is infinite if it is either positive or negative infinite. -/
def Infinite (x : ℤ*) : Prop := InfinitePos x ∨ InfiniteNeg x

/-- Standard-part predicate for hyperintegers: `IsSt x z` means `x` equals the standard integer `z`.

For discrete types like `ℤ*`, this is just equality (`IsSt x z ↔ x = z`), but provides
a uniform API with `Hyperreal.IsSt`. Equivalent to `Hyper.IsNearStandard` for discrete spaces. -/
def IsSt (x : ℤ*) (z : ℤ) : Prop := x = z

lemma isSt_iff_eq {x : ℤ*} {z : ℤ} : IsSt x z ↔ x = z := Iff.rfl

lemma IsSt.unique {x : ℤ*} {z w : ℤ} (hz : IsSt x z) (hw : IsSt x w) : z = w := by
  dsimp [IsSt] at hz hw
  simpa [hz] using hw

/-- Standard-part map: returns the standard integer if it exists, or `0`. -/
noncomputable def st (x : ℤ*) : ℤ := if h : ∃ z, IsSt x z then Classical.choose h else 0

lemma IsSt.st_eq {x : ℤ*} {z : ℤ} (hx : IsSt x z) : st x = z := by
  classical
  have h : ∃ z, IsSt x z := ⟨z, hx⟩
  have hx' : IsSt x (Classical.choose h) := Classical.choose_spec h
  have hchoose : Classical.choose h = z :=
    (IsSt.unique (x := x) (z := Classical.choose h) (w := z) hx' hx)
  simp [st, h, hchoose]

@[simp] lemma st_coe (z : ℤ) : st (z : ℤ*) = z := by
  classical
  simpa using (IsSt.st_eq (x := (z : ℤ*)) (z := z) rfl)

end Hyperinteger
