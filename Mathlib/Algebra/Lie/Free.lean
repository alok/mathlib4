/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.FreeNonUnitalNonAssocAlgebra
import Mathlib.Algebra.Lie.NonUnitalNonAssocAlgebra
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.UniversalEnveloping

#align_import algebra.lie.free from "leanprover-community/mathlib"@"841ac1a3d9162bf51c6327812ecb6e5e71883ac4"

/-!
# Free Lie algebras

Given a commutative ring `R` and a type `X` we construct the free Lie algebra on `X` with
coefficients in `R` together with its universal property.

## Main definitions

  * `FreeLieAlgebra`
  * `FreeLieAlgebra.lift`
  * `FreeLieAlgebra.of`
  * `FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra`

## Implementation details

### Quotient of free non-unital, non-associative algebra

We follow [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*](bourbaki1975) and construct
the free Lie algebra as a quotient of the free non-unital, non-associative algebra. Since we do not
currently have definitions of ideals, lattices of ideals, and quotients for
`NonUnitalNonAssocSemiring`, we construct our quotient using the low-level `Quot` function on
an inductively-defined relation.

### Alternative construction (needs PBW)

An alternative construction of the free Lie algebra on `X` is to start with the free unital
associative algebra on `X`, regard it as a Lie algebra via the ring commutator, and take its
smallest Lie subalgebra containing `X`. I.e.:
`LieSubalgebra.lieSpan R (FreeAlgebra R X) (Set.range (FreeAlgebra.ι R))`.

However with this definition there does not seem to be an easy proof that the required universal
property holds, and I don't know of a proof that avoids invoking the Poincaré–Birkhoff–Witt theorem.
A related MathOverflow question is [this one](https://mathoverflow.net/questions/396680/).

## Tags

lie algebra, free algebra, non-unital, non-associative, universal property, forgetful functor,
adjoint functor
-/


universe u v w

noncomputable section

variable (R : Type u) (X : Type v) [CommRing R]

-- mathport name: exprlib
/- We save characters by using Bourbaki's name `lib` (as in «libre») for
`FreeNonUnitalNonAssocAlgebra` in this file. -/
local notation "lib" => FreeNonUnitalNonAssocAlgebra

-- mathport name: «exprlib.lift»
local notation "lib.lift" => FreeNonUnitalNonAssocAlgebra.lift

-- mathport name: «exprlib.of»
local notation "lib.of" => FreeNonUnitalNonAssocAlgebra.of

-- mathport name: «exprlib.lift_of_apply»
local notation "lib.lift_of_apply" => FreeNonUnitalNonAssocAlgebra.lift_of_apply

-- mathport name: «exprlib.lift_comp_of»
local notation "lib.lift_comp_of" => FreeNonUnitalNonAssocAlgebra.lift_comp_of

namespace FreeLieAlgebra

/-- The quotient of `lib R X` by the equivalence relation generated by this relation will give us
the free Lie algebra. -/
inductive Rel : lib R X → lib R X → Prop
  | lie_self (a : lib R X) : Rel (a * a) 0
  | leibniz_lie (a b c : lib R X) : Rel (a * (b * c)) (a * b * c + b * (a * c))
  | smul (t : R) {a b : lib R X} : Rel a b → Rel (t • a) (t • b)
  | add_right {a b : lib R X} (c : lib R X) : Rel a b → Rel (a + c) (b + c)
  | mul_left (a : lib R X) {b c : lib R X} : Rel b c → Rel (a * b) (a * c)
  | mul_right {a b : lib R X} (c : lib R X) : Rel a b → Rel (a * c) (b * c)
#align free_lie_algebra.rel FreeLieAlgebra.Rel

variable {R X}

theorem Rel.addLeft (a : lib R X) {b c : lib R X} (h : Rel R X b c) : Rel R X (a + b) (a + c) := by
  rw [add_comm _ b, add_comm _ c]; exact h.add_right _
#align free_lie_algebra.rel.add_left FreeLieAlgebra.Rel.addLeft

theorem Rel.neg {a b : lib R X} (h : Rel R X a b) : Rel R X (-a) (-b) := by
  simpa only [neg_one_smul] using h.smul (-1)
#align free_lie_algebra.rel.neg FreeLieAlgebra.Rel.neg

theorem Rel.subLeft (a : lib R X) {b c : lib R X} (h : Rel R X b c) : Rel R X (a - b) (a - c) := by
  simpa only [sub_eq_add_neg] using h.neg.addLeft a
#align free_lie_algebra.rel.sub_left FreeLieAlgebra.Rel.subLeft

theorem Rel.subRight {a b : lib R X} (c : lib R X) (h : Rel R X a b) : Rel R X (a - c) (b - c) := by
  simpa only [sub_eq_add_neg] using h.add_right (-c)
#align free_lie_algebra.rel.sub_right FreeLieAlgebra.Rel.subRight

theorem Rel.smulOfTower {S : Type*} [Monoid S] [DistribMulAction S R] [IsScalarTower S R R] (t : S)
    (a b : lib R X) (h : Rel R X a b) : Rel R X (t • a) (t • b) := by
  rw [← smul_one_smul R t a, ← smul_one_smul R t b]
  exact h.smul _
#align free_lie_algebra.rel.smul_of_tower FreeLieAlgebra.Rel.smulOfTower

end FreeLieAlgebra

/-- The free Lie algebra on the type `X` with coefficients in the commutative ring `R`. -/
def FreeLieAlgebra :=
  Quot (FreeLieAlgebra.Rel R X)
#align free_lie_algebra FreeLieAlgebra

instance : Inhabited (FreeLieAlgebra R X) := by rw [FreeLieAlgebra]; infer_instance

namespace FreeLieAlgebra

instance {S : Type*} [Monoid S] [DistribMulAction S R] [IsScalarTower S R R] :
    SMul S (FreeLieAlgebra R X) where smul t := Quot.map ((· • ·) t) (Rel.smulOfTower t)

instance {S : Type*} [Monoid S] [DistribMulAction S R] [DistribMulAction Sᵐᵒᵖ R]
    [IsScalarTower S R R] [IsCentralScalar S R] : IsCentralScalar S (FreeLieAlgebra R X)
    where op_smul_eq_smul t := Quot.ind fun a => congr_arg (Quot.mk _) (op_smul_eq_smul t a)

instance : Zero (FreeLieAlgebra R X) where zero := Quot.mk _ 0

instance : Add (FreeLieAlgebra R X)
    where add := Quot.map₂ (· + ·) (fun _ _ _ => Rel.addLeft _) fun _ _ _ => Rel.add_right _

instance : Neg (FreeLieAlgebra R X) where neg := Quot.map Neg.neg fun _ _ => Rel.neg

instance : Sub (FreeLieAlgebra R X)
    where sub := Quot.map₂ Sub.sub (fun _ _ _ => Rel.subLeft _) fun _ _ _ => Rel.subRight _

instance : AddGroup (FreeLieAlgebra R X) :=
  Function.Surjective.addGroup (Quot.mk _) (surjective_quot_mk _) rfl (fun _ _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

instance : AddCommSemigroup (FreeLieAlgebra R X) :=
  Function.Surjective.addCommSemigroup (Quot.mk _) (surjective_quot_mk _) fun _ _ => rfl

instance : AddCommGroup (FreeLieAlgebra R X) :=
  { (inferInstance : AddGroup (FreeLieAlgebra R X)),
    (inferInstance :  AddCommSemigroup (FreeLieAlgebra R X)) with }

instance {S : Type*} [Semiring S] [Module S R] [IsScalarTower S R R] :
    Module S (FreeLieAlgebra R X) :=
  Function.Surjective.module S ⟨⟨Quot.mk (Rel R X), rfl⟩, fun _ _ => rfl⟩
    (surjective_quot_mk _) (fun _ _ => rfl)

/-- Note that here we turn the `Mul` coming from the `NonUnitalNonAssocSemiring` structure
on `lib R X` into a `Bracket` on `FreeLieAlgebra`. -/
instance : LieRing (FreeLieAlgebra R X) where
  bracket := Quot.map₂ (· * ·) (fun _ _ _ => Rel.mul_left _) fun _ _ _ => Rel.mul_right _
  add_lie := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; change Quot.mk _ _ = Quot.mk _ _; simp_rw [add_mul]
  lie_add := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; change Quot.mk _ _ = Quot.mk _ _; simp_rw [mul_add]
  lie_self := by rintro ⟨a⟩; exact Quot.sound (Rel.lie_self a)
  leibniz_lie := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; exact Quot.sound (Rel.leibniz_lie a b c)

instance : LieAlgebra R (FreeLieAlgebra R X) where
  lie_smul := by
    rintro t ⟨a⟩ ⟨c⟩
    change Quot.mk _ (a • t • c) = Quot.mk _ (t • a • c)
    rw [← smul_comm]

variable {X}

/-- The embedding of `X` into the free Lie algebra of `X` with coefficients in the commutative ring
`R`. -/
def of : X → FreeLieAlgebra R X := fun x => Quot.mk _ (lib.of R x)
#align free_lie_algebra.of FreeLieAlgebra.of

variable {L : Type w} [LieRing L] [LieAlgebra R L]

/-- An auxiliary definition used to construct the equivalence `lift` below. -/
def liftAux (f : X → CommutatorRing L) :=
  lib.lift R f
#align free_lie_algebra.lift_aux FreeLieAlgebra.liftAux

theorem liftAux_map_smul (f : X → L) (t : R) (a : lib R X) :
    liftAux R f (t • a) = t • liftAux R f a :=
  NonUnitalAlgHom.map_smul _ t a
#align free_lie_algebra.lift_aux_map_smul FreeLieAlgebra.liftAux_map_smul

theorem liftAux_map_add (f : X → L) (a b : lib R X) :
    liftAux R f (a + b) = liftAux R f a + liftAux R f b :=
  NonUnitalAlgHom.map_add _ a b
#align free_lie_algebra.lift_aux_map_add FreeLieAlgebra.liftAux_map_add

theorem liftAux_map_mul (f : X → L) (a b : lib R X) :
    liftAux R f (a * b) = ⁅liftAux R f a, liftAux R f b⁆ :=
  NonUnitalAlgHom.map_mul _ a b
#align free_lie_algebra.lift_aux_map_mul FreeLieAlgebra.liftAux_map_mul

theorem liftAux_spec (f : X → L) (a b : lib R X) (h : FreeLieAlgebra.Rel R X a b) :
    liftAux R f a = liftAux R f b := by
  induction h
  case lie_self a' => simp only [liftAux_map_mul, NonUnitalAlgHom.map_zero, lie_self]
  case leibniz_lie a' b' c' =>
    simp only [liftAux_map_mul, liftAux_map_add, sub_add_cancel, lie_lie]
  case smul t a' b' _ h₂ => simp only [liftAux_map_smul, h₂]
  case add_right a' b' c' _ h₂ => simp only [liftAux_map_add, h₂]
  case mul_left a' b' c' _ h₂ => simp only [liftAux_map_mul, h₂]
  case mul_right a' b' c' _ h₂ => simp only [liftAux_map_mul, h₂]
#align free_lie_algebra.lift_aux_spec FreeLieAlgebra.liftAux_spec

/-- The quotient map as a `NonUnitalAlgHom`. -/
def mk : lib R X →ₙₐ[R] CommutatorRing (FreeLieAlgebra R X) where
  toFun := Quot.mk (Rel R X)
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
#align free_lie_algebra.mk FreeLieAlgebra.mk

/-- The functor `X ↦ FreeLieAlgebra R X` from the category of types to the category of Lie
algebras over `R` is adjoint to the forgetful functor in the other direction. -/
def lift : (X → L) ≃ (FreeLieAlgebra R X →ₗ⁅R⁆ L) where
  toFun f :=
    { toFun := fun c => Quot.liftOn c (liftAux R f) (liftAux_spec R f)
      map_add' := by rintro ⟨a⟩ ⟨b⟩; rw [← liftAux_map_add]; rfl
      map_smul' := by rintro t ⟨a⟩; rw [← liftAux_map_smul]; rfl
      map_lie' := by rintro ⟨a⟩ ⟨b⟩; rw [← liftAux_map_mul]; rfl }
  invFun F := F ∘ of R
  left_inv f := by
    ext x;
    simp only [liftAux, of, Quot.liftOn_mk, LieHom.coe_mk, Function.comp_apply, lib.lift_of_apply]
  right_inv F := by
    ext ⟨a⟩
    let F' := F.toNonUnitalAlgHom.comp (mk R)
    exact NonUnitalAlgHom.congr_fun (lib.lift_comp_of R F') a
#align free_lie_algebra.lift FreeLieAlgebra.lift

@[simp]
theorem lift_symm_apply (F : FreeLieAlgebra R X →ₗ⁅R⁆ L) : (lift R).symm F = F ∘ of R := rfl
#align free_lie_algebra.lift_symm_apply FreeLieAlgebra.lift_symm_apply

variable {R}

@[simp]
theorem of_comp_lift (f : X → L) : lift R f ∘ of R = f := (lift R).left_inv f
#align free_lie_algebra.of_comp_lift FreeLieAlgebra.of_comp_lift

@[simp]
theorem lift_unique (f : X → L) (g : FreeLieAlgebra R X →ₗ⁅R⁆ L) : g ∘ of R = f ↔ g = lift R f :=
  (lift R).symm_apply_eq
#align free_lie_algebra.lift_unique FreeLieAlgebra.lift_unique

@[simp]
theorem lift_of_apply (f : X → L) (x) : lift R f (of R x) = f x := by
  rw [← @Function.comp_apply _ _ _ (lift R f) (of R) x, of_comp_lift]
#align free_lie_algebra.lift_of_apply FreeLieAlgebra.lift_of_apply

@[simp]
theorem lift_comp_of (F : FreeLieAlgebra R X →ₗ⁅R⁆ L) : lift R (F ∘ of R) = F := by
  rw [← lift_symm_apply]; exact (lift R).apply_symm_apply F
#align free_lie_algebra.lift_comp_of FreeLieAlgebra.lift_comp_of

@[ext]
theorem hom_ext {F₁ F₂ : FreeLieAlgebra R X →ₗ⁅R⁆ L} (h : ∀ x, F₁ (of R x) = F₂ (of R x)) :
    F₁ = F₂ :=
  have h' : (lift R).symm F₁ = (lift R).symm F₂ := by ext; simp [h]
  (lift R).symm.injective h'
#align free_lie_algebra.hom_ext FreeLieAlgebra.hom_ext

variable (R X)

/-- The universal enveloping algebra of the free Lie algebra is just the free unital associative
algebra. -/
@[simps!]
def universalEnvelopingEquivFreeAlgebra :
    UniversalEnvelopingAlgebra R (FreeLieAlgebra R X) ≃ₐ[R] FreeAlgebra R X :=
  AlgEquiv.ofAlgHom (UniversalEnvelopingAlgebra.lift R <| FreeLieAlgebra.lift R <| FreeAlgebra.ι R)
    (FreeAlgebra.lift R <| UniversalEnvelopingAlgebra.ι R ∘ FreeLieAlgebra.of R) (by ext; simp)
    (by ext; simp)
#align free_lie_algebra.universal_enveloping_equiv_free_algebra FreeLieAlgebra.universalEnvelopingEquivFreeAlgebra

end FreeLieAlgebra
