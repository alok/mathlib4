/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
module

public import Mathlib.Order.Filter.Germ.Basic
public import Mathlib.Order.Filter.Curry

/-!
# Germs over curried filters

This file relates germs over a curried filter to iterated germs.
-/

@[expose] public section

namespace Filter

namespace Germ

variable {α β γ : Type*} {l : Filter α} {m : Filter β}

/-- Germs over the curried filter correspond to iterated germs. -/
noncomputable def curryEquiv (l : Filter α) (m : Filter β) (γ : Type*) :
    Germ (l.curry m) γ ≃ Germ l (Germ m γ) := by
  classical
  let rep (f : α → Germ m γ) : α → β → γ :=
    fun a => Classical.choose (Quot.exists_rep (f a))
  have rep_spec (f : α → Germ m γ) (a : α) :
      ((rep f a : β → γ) : Germ m γ) = f a :=
    Classical.choose_spec (Quot.exists_rep (f a))
  let forwardFun : (α × β → γ) → α → Germ m γ :=
    fun f a => (fun b => f (a, b) : Germ m γ)
  have forward_rel :
      ∀ f g, f =ᶠ[l.curry m] g → forwardFun f =ᶠ[l] forwardFun g := by
    intro f g hfg
    have hfg' : ∀ᶠ a in l, ∀ᶠ b in m, f (a, b) = g (a, b) := by
      simpa [Filter.eventually_curry_iff] using hfg
    refine hfg'.mono ?_
    intro a ha
    exact (Germ.coe_eq (l := m) (f := fun b => f (a, b)) (g := fun b => g (a, b))).2 ha
  let forward : Germ (l.curry m) γ → Germ l (Germ m γ) :=
    Quotient.map forwardFun (by intro f g hfg; exact forward_rel f g hfg)
  let backwardFun : (α → Germ m γ) → Germ (l.curry m) γ :=
    fun f => (fun p : α × β => rep f p.1 p.2 : Germ (l.curry m) γ)
  have backward_rel :
      ∀ f g, f =ᶠ[l] g → backwardFun f = backwardFun g := by
    intro f g hfg
    apply (Germ.coe_eq (l := l.curry m)
      (f := fun p : α × β => rep f p.1 p.2)
      (g := fun p : α × β => rep g p.1 p.2)).2
    have hfg' : ∀ᶠ a in l, ∀ᶠ b in m, rep f a b = rep g a b := by
      refine hfg.mono ?_
      intro a ha
      have hrep : (rep f a : Germ m γ) = (rep g a : Germ m γ) := by
        calc
          (rep f a : Germ m γ) = f a := rep_spec f a
          _ = g a := ha
          _ = (rep g a : Germ m γ) := (rep_spec g a).symm
      exact (Germ.coe_eq (l := m) (f := rep f a) (g := rep g a)).1 hrep
    simpa [Filter.eventually_curry_iff] using hfg'
  let backward : Germ l (Germ m γ) → Germ (l.curry m) γ :=
    Quotient.lift backwardFun (by intro f g hfg; exact backward_rel f g hfg)
  refine
    { toFun := forward
      invFun := backward
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    refine Quotient.inductionOn x ?_
    intro f
    apply (Germ.coe_eq (l := l.curry m)
      (f := fun p : α × β => rep (forwardFun f) p.1 p.2)
      (g := f)).2
    have hrep : ∀ a, ∀ᶠ b in m, rep (forwardFun f) a b = f (a, b) := by
      intro a
      have hrep' : (rep (forwardFun f) a : Germ m γ) = forwardFun f a :=
        rep_spec (forwardFun f) a
      exact (Germ.coe_eq (l := m)
        (f := rep (forwardFun f) a)
        (g := fun b => f (a, b))).1 (by simpa [forwardFun] using hrep')
    have hrep' : ∀ᶠ a in l, ∀ᶠ b in m, rep (forwardFun f) a b = f (a, b) :=
      Filter.Eventually.of_forall hrep
    simpa [Filter.eventually_curry_iff] using hrep'
  · intro x
    refine Quotient.inductionOn x ?_
    intro f
    apply (Germ.coe_eq (l := l) (f := forwardFun (fun p : α × β => rep f p.1 p.2)) (g := f)).2
    have hrep : ∀ a, forwardFun (fun p : α × β => rep f p.1 p.2) a = f a := by
      intro a
      simpa [forwardFun] using rep_spec f a
    exact Filter.Eventually.of_forall hrep

end Germ

end Filter
