/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
module

import Mathlib.Data.Nat.Hypernatural
import Mathlib.Data.Int.Hyperinteger
import Mathlib.Data.Rat.Hyperrational
import Mathlib.Analysis.Real.Hyperreal

/-!
# Hypernumber tower

Coercions and simp lemmas for the tower `ℕ* → ℤ* → ℚ* → ℝ*`.
-/

open Filter Germ

namespace Hypernatural

/-- Cast a hypernatural to a hyperinteger. -/
noncomputable def castInt : ℕ* → ℤ* :=
  Germ.map (fun n : ℕ => (n : ℤ))

noncomputable instance : CoeTC ℕ* ℤ* := ⟨castInt⟩

@[simp, norm_cast]
theorem castInt_ofNat (n : ℕ) : ((n : ℕ*) : ℤ*) = (n : ℤ) := by
  simpa [castInt, Hypernatural.ofNat, Hyperinteger.ofInt] using
    (Germ.map_const (l := (nonstandardUltrafilter ℕ : Filter ℕ)) (a := n)
      (f := fun n : ℕ => (n : ℤ)))

@[simp]
theorem castInt_ofSeq (f : ℕ → ℕ) :
    ((Hypernatural.ofSeq f : ℕ*) : ℤ*) = Hyperinteger.ofSeq (fun n => (f n : ℤ)) := by
  rfl

end Hypernatural

namespace Hyperinteger

/-- Cast a hyperinteger to a hyperrational. -/
noncomputable def castRat : ℤ* → ℚ* :=
  Germ.map (fun z : ℤ => (z : ℚ))

noncomputable instance : CoeTC ℤ* ℚ* := ⟨castRat⟩

@[simp, norm_cast]
theorem castRat_ofInt (z : ℤ) : ((z : ℤ*) : ℚ*) = (z : ℚ) := by
  simpa [castRat, Hyperinteger.ofInt, Hyperrational.ofRat] using
    (Germ.map_const (l := (nonstandardUltrafilter ℕ : Filter ℕ)) (a := z)
      (f := fun z : ℤ => (z : ℚ)))

@[simp]
theorem castRat_ofSeq (f : ℕ → ℤ) :
    ((Hyperinteger.ofSeq f : ℤ*) : ℚ*) = Hyperrational.ofSeq (fun n => (f n : ℚ)) := by
  rfl

end Hyperinteger

namespace Hyperrational

/-- Cast a hyperrational to a hyperreal. -/
noncomputable def castReal : ℚ* → ℝ* :=
  Germ.map (fun q : ℚ => (q : ℝ))

noncomputable instance : CoeTC ℚ* ℝ* := ⟨castReal⟩

@[simp, norm_cast]
theorem castReal_ofRat (q : ℚ) : ((q : ℚ*) : ℝ*) = (q : ℝ) := by
  simpa [castReal, Hyperrational.ofRat, Hyperreal.ofReal] using
    (Germ.map_const (l := (nonstandardUltrafilter ℕ : Filter ℕ)) (a := q)
      (f := fun q : ℚ => (q : ℝ)))

@[simp]
theorem castReal_ofSeq (f : ℕ → ℚ) :
    ((Hyperrational.ofSeq f : ℚ*) : ℝ*) = Hyperreal.ofSeq (fun n => (f n : ℝ)) := by
  rfl

end Hyperrational
