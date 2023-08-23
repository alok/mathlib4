/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Adam Topaz
-/
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Opposite
import Mathlib.CategoryTheory.Abelian.Projective
import Mathlib.CategoryTheory.Functor.LeftDerived
import Mathlib.CategoryTheory.Linear.Yoneda

#align_import category_theory.abelian.ext from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Ext

We define `Ext R C n : Cᵒᵖ ⥤ C ⥤ Module R` for any `R`-linear abelian category `C`
by (left) deriving in the first argument of the bifunctor `(X, Y) ↦ Module.of R (unop X ⟶ Y)`.

## Implementation

It's not actually necessary here to assume `C` is abelian,
but the hypotheses, involving both `C` and `Cᵒᵖ`, are quite lengthy,
and in practice the abelian case is hopefully enough.

PROJECT: State the alternative definition in terms of
right deriving in the second argument, and show these agree.
-/


noncomputable section

open CategoryTheory

variable (R : Type*) [Ring R] (C : Type*) [Category C] [Abelian C] [Linear R C]
  [EnoughProjectives C]

/-- `Ext R C n` is defined by deriving in the first argument of `(X, Y) ↦ Module.of R (unop X ⟶ Y)`
(which is the second argument of `linearYoneda`).
-/

-- Porting note: the lemmas `Ext_obj` and `Ext_map` generated by `@[simps]` were
-- being rejected by the type-checking linter; it's unclear exactly why.
-- In any case, these lemmas were not actually used downstream in mathlib3,
-- and seem unlikely to be directly useful (rather than lemmas in terms of resolutions),
-- and so have been removed during porting:
-- @[simps! obj map]

-- Porting note: the mathlib3 proofs of `map_id` and `map_comp` were timing out,
-- but `aesop_cat` is fast if we leave them out.
def Ext (n : ℕ) : Cᵒᵖ ⥤ C ⥤ ModuleCat R :=
  Functor.flip
    { obj := fun Y => (((linearYoneda R C).obj Y).rightOp.leftDerived n).leftOp
      -- Porting note: if we use dot notation for any of
      -- `NatTrans.leftOp` / `NatTrans.rightOp` / `NatTrans.leftDerived`
      -- then `aesop_cat` can not discharge the `map_id` and `map_comp` goals.
      -- This should be investigated further.
      map := fun f =>
        NatTrans.leftOp (NatTrans.leftDerived (NatTrans.rightOp ((linearYoneda R C).map f)) n) }
set_option linter.uppercaseLean3 false in
#align Ext Ext

open ZeroObject

/-- If `X : C` is projective and `n : ℕ`, then `Ext^(n + 1) X Y ≅ 0` for any `Y`. -/
def extSuccOfProjective (X Y : C) [Projective X] (n : ℕ) :
    ((Ext R C (n + 1)).obj (Opposite.op X)).obj Y ≅ 0 :=
  let E := (((linearYoneda R C).obj Y).rightOp.leftDerivedObjProjectiveSucc n X).unop.symm
  E ≪≫
    { hom := 0
      inv := 0
      hom_inv_id := by
        let Z : (ModuleCat R)ᵒᵖ := 0
        rw [← (0 : 0 ⟶ Z.unop).unop_op, ← (0 : Z.unop ⟶ 0).unop_op, ← unop_id, ← unop_comp]
        aesop }
set_option linter.uppercaseLean3 false in
#align Ext_succ_of_projective extSuccOfProjective
