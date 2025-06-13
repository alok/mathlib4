/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Order.Filter.Germ.OrderedMonoid
import Mathlib.Tactic.Nonstandard.ForMathlib.FilterBasic

/-! # Complements on filter germs -/

open Filter Function

namespace Filter.Germ

variable {ι α β : Type*} (l : Filter ι)

lemma eq_def' : ((· = ·) : l.Germ α → l.Germ α → Prop) = LiftRel (· = ·) := by
  ext ⟨f⟩ ⟨g⟩
  exact coe_eq

/-! ## Product of germs -/

def prodEquiv : l.Germ α × l.Germ β ≃ l.Germ (α × β) where
  toFun := uncurry (Quotient.map₂ (fun f g i => ⟨f i, g i⟩)
    (by
      intros f f' hff' g g' hgg'
      filter_upwards [hff', hgg'] with i hfi hgi
      simp [hfi, hgi]))
  invFun i := 
    ⟨Quotient.map (fun f => Prod.fst ∘ f) 
      (by
        intros f f' hff'
        filter_upwards [hff'] with i hfi
        simp [hfi]) i, 
    Quotient.map (fun f => Prod.snd ∘ f) 
      (by
        intros g g' hgg'
        filter_upwards [hgg'] with i hgi
        simp [hgi]) i⟩
  left_inv := by rintro ⟨⟨f⟩, ⟨g⟩⟩; rfl
  right_inv := by 
    rintro ⟨f⟩
    rfl

@[simp] lemma prodEquiv_coe (f : ι → α) (g : ι → β) : 
  prodEquiv l ((f : l.Germ α), (g : l.Germ β)) = ↑(fun (i : ι) => (f i, g i)) :=
rfl

lemma liftRel_iff_liftPred_uncurry (r : α → β → Prop) (x : l.Germ α) (y : l.Germ β) : 
  LiftRel r x y ↔ LiftPred (uncurry r) (prodEquiv l (x, y)) := by
  refine x.inductionOn₂ y (fun f g => ?_)
  rfl

lemma liftRel_iff_liftPred_uncurry' (r : α → β → Prop) (x : l.Germ α) (y : l.Germ β) : 
  LiftRel r x y ↔ LiftPred (fun u : α × β => r u.1 u.2) (prodEquiv l (x, y)) :=
liftRel_iff_liftPred_uncurry l r x y

lemma liftRel_symm (r : α → β → Prop) (x : l.Germ α) (y : l.Germ β) : 
  LiftRel r x y ↔ LiftRel (fun a b => r b a) y x := by
  refine x.inductionOn₂ y (fun f g => ?_)
  rfl

/-! ## Transfer lemmas -/

/-! ### Forall rules -/

lemma forall_iff_forall_liftPred [l.NeBot] (p : α → Prop) : 
  (∀ x, p x) ↔ (∀ x : l.Germ α, LiftPred p x) := by
  constructor
  · intro h x
    refine x.inductionOn (fun f => ?_)
    exact Eventually.of_forall (fun x => h (f x))
  · intro h x
    exact Filter.Germ.liftPred_const_iff.mp (h ↑x)

lemma forall_forall_iff_forall_forall_liftRel [l.NeBot] (r : α → β → Prop) :
  (∀ x y, r x y) ↔ (∀ (x : l.Germ α) (y : l.Germ β), LiftRel r x y) := by
  constructor
  · intro h x y
    refine x.inductionOn₂ y (fun f g => ?_)
    exact Eventually.of_forall (fun n => h (f n) (g n))
  · intro h x y
    have : LiftRel r (↑x : l.Germ α) (↑y : l.Germ β) := h ↑x ↑y
    simpa using this

lemma forall_forall_eq_iff_forall_forall_eq {ι α : Type*} {l : Filter ι} [l.NeBot] :
  (∀ x y : α, x = y) ↔ (∀ x y : l.Germ α, x = y) := by
  constructor
  · intro h x y
    refine x.inductionOn₂ y (fun f g => ?_)
    simp only [Filter.Germ.eq_def']
    exact Eventually.of_forall (fun n => h (f n) (g n))
  · intro h x y
    have : (↑x : l.Germ α) = ↑y := h ↑x ↑y
    simpa using this

/-! ### Exists rules -/

lemma exists_iff_exists_liftPred [l.NeBot] (p : α → Prop) : 
  (∃ x, p x) ↔ (∃ x : l.Germ α, LiftPred p x) := by
  constructor
  · intro ⟨x, hx⟩
    exact ⟨↑x, Filter.Germ.liftPred_const hx⟩
  · rintro ⟨x, hx⟩
    revert hx
    refine x.inductionOn (fun f => ?_)
    intro hf
    obtain ⟨i, hi⟩ := hf.exists
    exact ⟨f i, hi⟩

lemma liftPred_exists_iff_exists_liftRel [l.NeBot] (r : α → β → Prop) (x : l.Germ α) : 
  LiftPred (fun x => ∃ (y : β), r x y) x ↔ ∃ (y : l.Germ β), LiftRel r x y := by
  refine x.inductionOn (fun f => ?_)
  rw [Filter.Germ.liftPred_coe]
  constructor
  · intro h
    obtain ⟨g, hg⟩ := h.choice
    exact ⟨g, hg⟩
  · rintro ⟨y, hy⟩
    revert hy
    refine y.inductionOn (fun g => ?_)
    intro hg
    filter_upwards [hg] with i hi
    exact ⟨g i, hi⟩

lemma liftPred_exists_iff_exists_liftPred [l.NeBot] (r : α → β → Prop) (x : l.Germ α) : 
  LiftPred (fun x => ∃ (y : β), r x y) x ↔ 
    ∃ (y : l.Germ β), LiftPred (uncurry r) (prodEquiv l (x, y)) := by
  conv_rhs => congr; ext; rw [← liftRel_iff_liftPred_uncurry]
  exact liftPred_exists_iff_exists_liftRel l r x

lemma liftPred_exists_iff_exists_liftPred' [l.NeBot] (r : α → β → Prop) (x : l.Germ α) : 
  LiftPred (fun x => ∃ (y : β), r x y) x ↔ 
    ∃ (y : l.Germ β), LiftPred (fun u : α × β => r u.1 u.2) (prodEquiv l (x, y)) :=
liftPred_exists_iff_exists_liftPred l r x

/-! ### Eq rules -/

lemma liftPred_eq_iff_eq_map (f g : α → β) (x : l.Germ α) :
  LiftPred (fun x => f x = g x) x ↔ Germ.map f x = Germ.map g x := by
  refine x.inductionOn (fun u => ?_)
  simp only [liftPred_coe, map_coe, coe_eq]
  rfl

/-! ### And rules -/

lemma liftPred_and_iff_and_liftPred [l.NeBot] (p q : α → Prop) (x : l.Germ α) :
  LiftPred (fun x => p x ∧ q x) x ↔ LiftPred p x ∧ LiftPred q x := by
  refine x.inductionOn (fun f => ?_)
  exact eventually_and

/-! ### Not rules -/

-- We'll add a simpler version of liftPred_not later if needed

/-! ### Exists rules for Props -/

lemma liftPred_exists_prop_iff_and_liftPred [l.NeBot] (p q : α → Prop) (x : l.Germ α) :
  LiftPred (fun x => ∃ (_ : p x), q x) x ↔ LiftPred p x ∧ LiftPred q x := by
  conv_lhs => arg 1; ext; rw [exists_prop]
  exact liftPred_and_iff_and_liftPred l p q x

/-! ### Logical connectives -/

lemma and_iff_and_liftPred [l.NeBot] (p q : α → Prop) :
  (∀ x, p x ∧ q x) ↔ (∀ x : l.Germ α, LiftPred p x ∧ LiftPred q x) := by
  constructor
  · intro h x
    exact ⟨(forall_iff_forall_liftPred l _).mp (fun a => (h a).1) x,
            (forall_iff_forall_liftPred l _).mp (fun a => (h a).2) x⟩
  · intro h x
    exact ⟨(forall_iff_forall_liftPred l _).mpr (fun g => (h g).1) x,
            (forall_iff_forall_liftPred l _).mpr (fun g => (h g).2) x⟩

lemma or_iff_or_liftPred [l.NeBot] (p q : α → Prop) :
  (∃ x, p x ∨ q x) ↔ (∃ x : l.Germ α, LiftPred p x ∨ LiftPred q x) := by
  constructor
  · intro ⟨x, hx⟩
    use ↑x
    cases hx with
    | inl h => left; exact liftPred_const h
    | inr h => right; exact liftPred_const h
  · intro ⟨x, hx⟩
    revert hx
    refine x.inductionOn (fun f => ?_)
    intro hf
    cases hf with
    | inl h => 
      obtain ⟨i, hi⟩ := h.exists
      exact ⟨f i, Or.inl hi⟩
    | inr h =>
      obtain ⟨i, hi⟩ := h.exists
      exact ⟨f i, Or.inr hi⟩

lemma not_iff_not_liftPred [l.NeBot] (p : α → Prop) :
  (∀ x, ¬p x) ↔ (∀ x : l.Germ α, ¬LiftPred p x) := by
  constructor
  · intro h x
    intro hx
    revert hx
    refine x.inductionOn (fun f => ?_)
    intro hf
    obtain ⟨i, hi⟩ := hf.exists
    exact h (f i) hi
  · intro h x
    by_contra px
    exact h ↑x (liftPred_const px)

lemma imp_iff_imp_liftPred [l.NeBot] (p q : α → Prop) :
  (∀ x, p x → q x) ↔ (∀ x : l.Germ α, LiftPred p x → LiftPred q x) := by
  constructor
  · intro h x hp
    revert hp
    refine x.inductionOn (fun f => ?_)
    intro hpf
    exact hpf.mono (fun a ha => h (f a) ha)
  · intro h x px
    exact liftPred_const_iff.mp (h ↑x (liftPred_const px))

/-! ### Relation rules with constants -/

lemma liftRel_const_left_iff_liftPred [l.NeBot] (r : α → β → Prop) (a : α) (y : l.Germ β) :
  LiftRel r ↑a y ↔ LiftPred (r a ·) y := by
  refine y.inductionOn (fun g => ?_)
  rfl

lemma liftRel_const_right_iff_liftPred [l.NeBot] (r : α → β → Prop) (x : l.Germ α) (b : β) :
  LiftRel r x ↑b ↔ LiftPred (fun a => r a b) x := by
  refine x.inductionOn (fun f => ?_)
  rfl

lemma const_le_iff_liftPred [Preorder α] [l.NeBot] (a : α) (x : l.Germ α) :
  ↑a ≤ x ↔ LiftPred (fun b => a ≤ b) x := by
  refine x.inductionOn (fun f => ?_)
  simp only [Filter.Germ.le_def, liftRel_coe]
  rfl

lemma le_const_iff_liftPred [Preorder α] [l.NeBot] (x : l.Germ α) (a : α) :
  x ≤ ↑a ↔ LiftPred (fun b => b ≤ a) x := by
  refine x.inductionOn (fun f => ?_)
  simp only [Filter.Germ.le_def, liftRel_coe]
  rfl

-- Skip lt lemmas for now as they involve the subtle relationship between ∃ᶠ and ∀ᶠ

lemma const_eq_iff_liftPred [l.NeBot] (a : α) (x : l.Germ α) :
  ↑a = x ↔ LiftPred (fun b => a = b) x := by
  refine x.inductionOn (fun f => ?_)
  simp only [Filter.Germ.eq_def', liftRel_coe]
  rfl

lemma eq_const_iff_liftPred [l.NeBot] (x : l.Germ α) (a : α) :
  x = ↑a ↔ LiftPred (fun b => b = a) x := by
  refine x.inductionOn (fun f => ?_)
  simp only [Filter.Germ.eq_def', liftRel_coe]
  rfl

-- For now, we'll skip the ne lemmas as they require more careful handling
-- They involve the relationship between ∃ᶠ and ∀ᶠ which is subtle

/-! ### Combined forall rules with relations -/

lemma forall_le_const_iff_forall_germ_le [Preorder α] [l.NeBot] (a : α) :
  (∀ x, a ≤ x) ↔ (∀ x : l.Germ α, ↑a ≤ x) := by
  simp only [const_le_iff_liftPred]
  exact forall_iff_forall_liftPred l (a ≤ ·)

lemma forall_const_le_iff_forall_germ_le [Preorder α] [l.NeBot] (a : α) :
  (∀ x, x ≤ a) ↔ (∀ x : l.Germ α, x ≤ ↑a) := by
  simp only [le_const_iff_liftPred]
  exact forall_iff_forall_liftPred l (· ≤ a)

-- Skip lt rules for now

lemma forall_eq_const_iff_forall_germ_eq [l.NeBot] (a : α) :
  (∀ x, a = x) ↔ (∀ x : l.Germ α, ↑a = x) := by
  simp only [const_eq_iff_liftPred]
  exact forall_iff_forall_liftPred l (a = ·)

lemma forall_const_eq_iff_forall_germ_eq [l.NeBot] (a : α) :
  (∀ x, x = a) ↔ (∀ x : l.Germ α, x = ↑a) := by
  simp only [eq_const_iff_liftPred]
  exact forall_iff_forall_liftPred l (· = a)

-- Skip ne rules for now

-- Exists relation theorems for direct transfer without LiftPred
lemma exists_le_const_iff_exists_germ_le [Preorder α] [l.NeBot] (a : α) :
  (∃ x, a ≤ x) ↔ (∃ x : l.Germ α, ↑a ≤ x) := by
  simp only [const_le_iff_liftPred]
  exact exists_iff_exists_liftPred l (a ≤ ·)

lemma exists_const_le_iff_exists_germ_le [Preorder α] [l.NeBot] (a : α) :
  (∃ x, x ≤ a) ↔ (∃ x : l.Germ α, x ≤ ↑a) := by
  simp only [le_const_iff_liftPred]
  exact exists_iff_exists_liftPred l (· ≤ a)

lemma exists_eq_const_iff_exists_germ_eq [l.NeBot] (a : α) :
  (∃ x, a = x) ↔ (∃ x : l.Germ α, ↑a = x) := by
  simp only [const_eq_iff_liftPred]
  exact exists_iff_exists_liftPred l (a = ·)

lemma exists_const_eq_iff_exists_germ_eq [l.NeBot] (a : α) :
  (∃ x, x = a) ↔ (∃ x : l.Germ α, x = ↑a) := by
  simp only [eq_const_iff_liftPred]
  exact exists_iff_exists_liftPred l (· = a)

/-! ### Arithmetic operation rules -/

section Arithmetic

variable {ι α β : Type*} {l : Filter ι} [l.NeBot]

lemma map_add_iff_add_map [Add α] (f g : l.Germ α) :
  Germ.map (· + ·) (prodEquiv l (f, g)) = f + g := by
  refine f.inductionOn₂ g (fun a b => ?_)
  simp [prodEquiv_coe, map_coe]
  rfl

lemma map_mul_iff_mul_map [Mul α] (f g : l.Germ α) :
  Germ.map (· * ·) (prodEquiv l (f, g)) = f * g := by
  refine f.inductionOn₂ g (fun a b => ?_)
  simp [prodEquiv_coe, map_coe]
  rfl

lemma map_sub_iff_sub_map [Sub α] (f g : l.Germ α) :
  Germ.map (· - ·) (prodEquiv l (f, g)) = f - g := by
  refine f.inductionOn₂ g (fun a b => ?_)
  simp [prodEquiv_coe, map_coe]
  rfl

lemma map_div_iff_div_map [Div α] (f g : l.Germ α) :
  Germ.map (· / ·) (prodEquiv l (f, g)) = f / g := by
  refine f.inductionOn₂ g (fun a b => ?_)
  simp [prodEquiv_coe, map_coe]
  rfl

lemma const_add [Add α] (a b : α) : (↑(a + b) : l.Germ α) = ↑a + ↑b := by
  rfl

lemma const_mul [Mul α] (a b : α) : (↑(a * b) : l.Germ α) = ↑a * ↑b := by
  rfl

lemma const_sub [Sub α] (a b : α) : (↑(a - b) : l.Germ α) = ↑a - ↑b := by
  rfl

lemma const_div [Div α] (a b : α) : (↑(a / b) : l.Germ α) = ↑a / ↑b := by
  rfl

lemma const_zero [Zero α] : (↑(0 : α) : l.Germ α) = 0 := rfl

lemma const_one [One α] : (↑(1 : α) : l.Germ α) = 1 := rfl

end Arithmetic

end Filter.Germ