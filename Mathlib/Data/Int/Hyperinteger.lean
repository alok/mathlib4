
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



/-! # Complements on filter products -/



namespace Filter.Germ

/-! # Complements on filter germs -/


variable {ι α β : Type*} (l : Filter ι) (ul : Ultrafilter ι)

-- local notation `∀*` binders `, ` r:(scoped p, filter.eventually p l) := r
/-- Germs on a filter `l` for a type `α` -/
local notation "α*" => l.Germ α
/-- Germs on a filter `l` for a type `β` -/
local notation "β*" => l.Germ β


/-- ## Germ equality -/
lemma eq_def' : ((· = ·) : α* → α* → Prop) = LiftRel (· = ·) :=
by
  ext ⟨f⟩ ⟨g⟩
  exact coe_eq

/-! ## Product of germs -/

/-- Equivalence between the product of germs and the germ of the product -/
def prod_equiv : α* × β* ≃ l.Germ (α × β) where
  toFun := Function.uncurry <|
    Quotient.map₂' (fun f g i => ⟨f i, g i⟩) fun f f' hff' g g' hgg' => by
      filter_upwards [hff', hgg']
      intro i hfi hgi
      simp [hfi, hgi]
  invFun i := ⟨
    Quotient.map' (fun f => Prod.fst ∘ f) (fun f f' hff' => by
      filter_upwards [hff']
      intro i hfi
      simp [hfi]) i,
    Quotient.map' (fun f => Prod.snd ∘ f) (fun g g' hgg' => by
      filter_upwards [hgg']
      intro i hgi
      simp [hgi]) i⟩
  left_inv := by
    rintro ⟨⟨f⟩, ⟨g⟩⟩
    rfl
  right_inv := by
    rintro ⟨f⟩
    convert rfl

/-- Equivalence between the product of germs and the germ of the product along a filter `l`. -/
local notation "⋈" => (prod_equiv l : α* × β* → l.Germ (α × β))

@[simp]
theorem prod_equiv_coe (f : ι → α) (g : ι → β) :
  ⋈ ((f : α*), (g : β*)) = ↑(fun i ↦ (f i, g i)) := rfl

lemma lift_rel_iff_lift_pred_uncurry (r : α → β → Prop) (x : α*) (y : β*) :
    LiftRel r x y ↔ LiftPred (Function.uncurry r) (⋈ (x, y)) := by
  refine x.induction_on₂ y fun f g => by rfl

lemma lift_rel_iff_lift_pred_uncurry' (r : α → β → Prop) (x : α*) (y : β*) :
    LiftRel r x y ↔ LiftPred (Function.uncurry r) (⋈ (x, y)) :=
  lift_rel_iff_lift_pred_uncurry l r x y

lemma lift_rel_symm (r : α → β → Prop) (x : α*) (y : β*) :
    LiftRel r x y ↔ LiftRel (fun a b => r b a) y x := by
  refine x.induction_on₂ y fun f g => by rfl

/-! ## Transfer lemmas -/

/-! ### Forall rules -/

lemma forall_iff_forall_lift_pred [l.NeBot] (p : α → Prop) :
    (∀ x, p x) ↔ (∀ x : α*, LiftPred p x) := by
  constructor
  · intro h x
    refine x.induction_on fun f => by
      exact Filter.Eventually.of_forall fun x => h (f x)
  · intro h x
    exact liftPred_const_iff.mp (h ↑x)

/-! ### Exists rules -/

lemma exists_iff_exists_lift_pred [l.NeBot] (p : α → Prop) :
    (∃ x, p x) ↔ (∃ x : α*, LiftPred p x) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨↑x, liftPred_const hx⟩
  · rintro ⟨x, hx⟩
    revert hx
    refine x.induction_on fun f hf => by
      obtain ⟨i, hi⟩ := hf.exists
      exact ⟨f i, hi⟩

lemma lift_pred_exists_iff_exists_lift_rel [l.NeBot] (r : α → β → Prop) (x : α*) :
    LiftPred (fun x => ∃ y : β, r x y) x ↔ ∃ y : β*, LiftRel r x y := by
  refine x.induction_on fun f => by
    simp
    constructor
    · intro h
      obtain ⟨g, hg⟩ := h.choice
      exact ⟨g, hg⟩
    · rintro ⟨y, hy⟩
      revert hy
      refine y.induction_on fun g hg => by
        filter_upwards [hg]
        intro i hi
        exact ⟨g i, hi⟩

lemma lift_pred_exists_iff_exists_lift_pred [l.NeBot] (r : α → β → Prop) (x : α*) :
    LiftPred (fun x => ∃ y : β, r x y) x ↔ ∃ y : β*, LiftPred (Function.uncurry r) (⋈ (x, y)) := by
  conv_rhs => congr; ext; rw [← lift_rel_iff_lift_pred_uncurry]
  exact lift_pred_exists_iff_exists_lift_rel l r x

lemma lift_pred_exists_iff_exists_lift_pred' [l.NeBot] (r : α → β → Prop) (x : α*) :
    LiftPred (fun x => ∃ y : β, r x y) x ↔ ∃ y : β*, LiftPred (Function.uncurry r) (⋈ (x, y)) :=
  lift_pred_exists_iff_exists_lift_pred l r x

/-! ### Eq rules -/

lemma lift_pred_eq_iff_eq_map (f g : α → β) (x : α*) :
    LiftPred (fun x => f x = g x) x ↔ Germ.map f x = Germ.map g x := by
  refine x.induction_on fun u => by
    -- rw [Filter.Germ.eq_def]
    -- rfl
    sorry
/-! ### And rules -/

lemma lift_pred_and_iff_and_lift_pred [l.NeBot] (p q : α → Prop) (x : α*) :
    LiftPred (fun x => p x ∧ q x) x ↔ LiftPred p x ∧ LiftPred q x := by
  refine x.induction_on fun f => eventually_and

/-! ### Exists rules for Props -/

lemma lift_pred_exists_prop_iff_and_lift_pred [l.NeBot] (p q : α → Prop) (x : α*) :
    LiftPred (fun x => ∃ _ : p x, q x) x ↔ LiftPred p x ∧ LiftPred q x := by
  conv in (Exists _) => rw [exists_prop]
  exact lift_pred_and_iff_and_lift_pred l p q x


-- variable {ι α β : Type*} (l : Ultrafilter ι)

-- local notation "∀* " binders ", " r:(scoped p, Filter.Eventually p l) => r
-- set_option quotPrecheck false in
/-- Germs on an ultrafilter `ul` for a type `α` -/
local notation "α**" => ul.Germ α
/-- Germs on an ultrafilter `ul` for a type `β` -/
local notation "β**" => ul.Germ β
/-- Equivalence between the product of germs and the germ of the product along an ultrafilter -/
local notation "⋈*" => (prod_equiv (ul : Ultrafilter ι) : α** × β** → ul.Germ (α × β))

/-! ## Transfer lemmas -/

/-! ### Not rules -/

lemma lift_pred_not_iff_not_lift_pred (p : α → Prop) (x : α**) :
  LiftPred (fun x => ¬ p x) x ↔ ¬ LiftPred p x := by
  refine x.induction_on fun f => by
    simp only [quot_mk_eq_coe, liftPred_coe, not_eventually, Ultrafilter.frequently_iff_eventually]

lemma lift_rel_not_iff_not_lift_rel (r : α → β → Prop) (x : α**) (y : β**) :
  LiftRel (fun x y => ¬ r x y) x y ↔ ¬ LiftRel r x y := by
  refine x.induction_on₂ y fun f g => by
    simp only [quot_mk_eq_coe, liftRel_coe, not_eventually, Ultrafilter.frequently_iff_eventually]

/-! ### Ne rules -/

lemma lift_pred_ne_iff_ne_map (f g : α → β) (x : α**) :
  LiftPred (fun x => f x ≠ g x) x ↔ Germ.map f x ≠ Germ.map g x := by
  refine x.induction_on fun u => by
    -- simp only [quot_mk_eq_coe, liftPred_coe, map_coe, not_eventually, Ultrafilter.frequently_iff_eventually]
    sorry



/-! ### Imp rules -/

lemma lift_pred_imp_iff_imp_lift_pred (p q : α → Prop) (x : α**) :
  LiftPred (fun x => p x → q x) x ↔ (LiftPred p x → LiftPred q x) := by
  refine x.induction_on fun f => by
    sorry

/-! ### Forall rules -/

lemma lift_pred_forall_iff_forall_lift_rel (r : α → β → Prop) (x : α**) :
  LiftPred (fun x => ∀ (y : β), r x y) x ↔ ∀ (y : β**), LiftRel r x y := by
  rw [← not_iff_not, ← lift_pred_not_iff_not_lift_pred]
  push_neg
  simp_rw [← lift_rel_not_iff_not_lift_rel]
  exact lift_pred_exists_iff_exists_lift_rel ul r x

lemma lift_pred_forall_iff_forall_lift_pred (r : α → β → Prop) (x : α**) :
  LiftPred (fun x => ∀ (y : β), r x y) x ↔ ∀ (y : β**), LiftPred (Function.uncurry r) (⋈* (x, y)) := by
  convert lift_pred_forall_iff_forall_lift_rel ul r x
  ext
  exact forall_congr fun y => by rw [← lift_rel_iff_lift_pred_uncurry]

lemma lift_pred_forall_iff_forall_lift_pred' (r : α → β → Prop) (x : α**) :
  LiftPred (fun x => ∀ (y : β), r x y) x ↔ ∀ (y : β**), LiftPred (Function.uncurry r) (⋈* (x, y)) :=
  lift_pred_forall_iff_forall_lift_pred ul r x

/-! ### Or rules -/

lemma lift_pred_or_iff_or_lift_pred (p q : α → Prop) (x : α**) :
  LiftPred (fun x => p x ∨ q x) x ↔ LiftPred p x ∨ LiftPred q x := by
  refine x.induction_on fun f => Ultrafilter.eventually_or

/-! ### Lt rules -/

lemma lift_pred_lt_iff_lt_map [Preorder β] (f g : α → β) (x : α**) :
  LiftPred (fun x => f x < g x) x ↔ Germ.map f x < Germ.map g x := by
  refine x.induction_on fun f => by
    rw [Filter.Germ.lt_def]
    rfl

end Filter.Germ


-- TODO represent with inductive (negSucc,etc)?
-- /-- Hyperintegers on the ultrafilter extending the cofinite filter -/
def Hyperinteger : Type :=
  Germ (hyperfilter ℕ : Filter ℕ) ℤ deriving Inhabited




namespace Hyperinteger

@[inherit_doc] notation "ℤ*" => Hyperinteger

noncomputable instance : LinearOrderedCommRing ℤ* :=
  inferInstanceAs (LinearOrderedCommRing (Germ _ _))






#synth LinearOrderedRing ℤ

/-- Natural embedding `ℕ → ℕ*`. -/
@[coe] def ofInt : ℤ → ℤ* := const

instance : OfNat ℤ* n where
  ofNat := ofInt n

noncomputable instance : CoeTC ℤ ℤ* := ⟨ofInt⟩

noncomputable instance : CoeTC ℕ* ℤ* := sorry

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
