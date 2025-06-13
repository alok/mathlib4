import Mathlib.Order.Filter.Germ.Basic
import Mathlib.Tactic.Nonstandard.Complements.Germ
import Mathlib.Order.Filter.Ultrafilter.Defs

/* # Complements on filter products */

open Filter Function

namespace Filter.Germ

variable {ι α β : Type*} (l : Ultrafilter ι)

/* ## Transfer lemmas */

/* ### Not rules */

lemma liftPred_not_iff_not_liftPred (p : α → Prop) (x : (l : Filter ι).Germ α) : 
  LiftPred (fun x => ¬ p x) x ↔ ¬ LiftPred p x := by
  refine x.inductionOn (fun f => ?_)
  rw [liftPred_coe, liftPred_coe, Ultrafilter.eventually_not]

lemma liftRel_not_iff_not_liftRel (r : α → β → Prop) 
    (x : (l : Filter ι).Germ α) (y : (l : Filter ι).Germ β) : 
  LiftRel (fun x y => ¬ r x y) x y ↔ ¬ LiftRel r x y := by
  refine x.inductionOn₂ y (fun f g => ?_)
  rw [liftRel_coe, liftRel_coe, Ultrafilter.eventually_not]

/* ### Ne rules */

lemma liftPred_ne_iff_ne_map (f g : α → β) (x : (l : Filter ι).Germ α) :
  LiftPred (fun x => f x ≠ g x) x ↔ Germ.map f x ≠ Germ.map g x := by
  refine x.inductionOn (fun u => ?_)
  rw [liftPred_coe, map_coe, map_coe]
  simp only [ne_eq, coe_eq]
  rw [Ultrafilter.eventually_not]
  simp only [EventuallyEq]
  rfl

/* ### Imp rules */

lemma liftPred_imp_iff_imp_liftPred (p q : α → Prop) (x : (l : Filter ι).Germ α) :
  LiftPred (fun x => p x → q x) x ↔ (LiftPred p x → LiftPred q x) := by
  refine x.inductionOn (fun f => ?_)
  rw [liftPred_coe, liftPred_coe]
  exact Ultrafilter.eventually_imp

/* ### Forall rules */

lemma liftPred_forall_iff_forall_liftRel (r : α → β → Prop) (x : (l : Filter ι).Germ α) : 
  LiftPred (fun x => ∀ (y : β), r x y) x ↔ ∀ (y : (l : Filter ι).Germ β), LiftRel r x y := by
  rw [← not_iff_not, ← liftPred_not_iff_not_liftPred]
  push_neg
  simp_rw [← liftRel_not_iff_not_liftRel]
  haveI : NeBot (l : Filter ι) := inferInstance
  exact liftPred_exists_iff_exists_liftRel (l : Filter ι) (fun x y => ¬r x y) x

lemma liftPred_forall_iff_forall_liftPred (r : α → β → Prop) (x : (l : Filter ι).Germ α) : 
  LiftPred (fun x => ∀ (y : β), r x y) x ↔ 
    ∀ (y : (l : Filter ι).Germ β), LiftPred (uncurry r) (prodEquiv (l : Filter ι) (x, y)) := by
  convert liftPred_forall_iff_forall_liftRel l r x
  simp only [liftRel_iff_liftPred_uncurry]

lemma liftPred_forall_iff_forall_liftPred' (r : α → β → Prop) (x : (l : Filter ι).Germ α) : 
  LiftPred (fun x => ∀ (y : β), r x y) x ↔ 
    ∀ (y : (l : Filter ι).Germ β), 
      LiftPred (fun u : α × β => r u.1 u.2) (prodEquiv (l : Filter ι) (x, y)) :=
liftPred_forall_iff_forall_liftPred l r x

/* ### Or rules */

lemma liftPred_or_iff_or_liftPred (p q : α → Prop) (x : (l : Filter ι).Germ α) :
  LiftPred (fun x => p x ∨ q x) x ↔ LiftPred p x ∨ LiftPred q x := by
  refine x.inductionOn (fun f => ?_)
  rw [liftPred_coe, liftPred_coe, liftPred_coe]
  exact Ultrafilter.eventually_or

/* ### Lt rules */

lemma liftPred_lt_iff_lt_map [Preorder β] (f g : α → β) (x : (l : Filter ι).Germ α) :
  LiftPred (fun x => f x < g x) x ↔ Germ.map f x < Germ.map g x := by
  refine x.inductionOn (fun u => ?_)
  rw [liftPred_coe, map_coe, map_coe]
  -- Use the definition of < in terms of ≤
  -- Convert to using < = ≤ ∧ ¬≥
  simp only [lt_iff_le_not_ge]
  -- For ultrafilters, eventually (p and q) iff (eventually p) and (eventually q)
  have h_and : (∀ᶠ (x : ι) in ↑l, f (u x) ≤ g (u x) ∧ ¬g (u x) ≤ f (u x)) ↔ 
      ((∀ᶠ (x : ι) in ↑l, f (u x) ≤ g (u x)) ∧ (∀ᶠ (x : ι) in ↑l, ¬g (u x) ≤ f (u x))) := by
    constructor
    · intro h
      constructor
      · filter_upwards [h] with i hi; exact hi.1
      · filter_upwards [h] with i hi; exact hi.2
    · intro ⟨h1, h2⟩
      filter_upwards [h1, h2] with i hi1 hi2
      exact ⟨hi1, hi2⟩
  rw [h_and]
  -- Now use Ultrafilter.eventually_not and simplify
  simp only [coe_le, EventuallyLE, Function.comp_apply, lt_iff_le_not_ge]
  rw [Ultrafilter.eventually_not]

end Filter.Germ