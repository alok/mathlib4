/-
Copyright (c) 2023 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Mathlib.Data.Polynomial.Degree.Definitions

/-!

# `compute_degree_le` a tactic for computing degrees of polynomials

This file defines the tactic `compute_degree_le`.

Using `compute_degree_le` when the goal is of the form `natDegree f ≤ d` or `degree f ≤ d`,
tries to solve the goal.
It may leave a side-goal of the form `d' ≤ d`, in case it is not entirely successful.

See the doc-string for more details.

##  Future work

* Deal with equalities, instead of inequalities (i.e. implement `compute_degree`).
* Add support for proving goals of the from `natDegree f ≠ 0` and `degree f ≠ 0`.
* Make sure that `degree` and `natDegree` are equally supported.

##  Implementation details

We start with a goal of the form `natDegree f ≤ d` or `degree f ≤ d`.
Recurse into `f` breaking apart sums, products and powers.  Take care of numerals,
`C a, X (^ n), monomial a n` separately.
-/

open Polynomial

namespace Mathlib.Tactic.ComputeDegree

section mylemmas

/-!
###  Simple lemmas about `natDegree` and `degree`

The lemmas in this section deduce inequalities of the form `natDegree f ≤ d` and `degree f ≤ d`,
using inequalities of the same shape.
This allows a recursive application of the `compute_degree_le` tactic on a goal,
and on all the resulting subgoals.
-/

variable {R : Type _}

section semiring
variable [Semiring R]

section Lemmas__in_a_dependent_PR

theorem natDegree_add_le_of_le {a b : Nat} {f g : R[X]} (hf : natDegree f ≤ a) (hg : natDegree g ≤ b) :
    natDegree (f + g) ≤ max a b :=
(f.natDegree_add_le g).trans $ max_le_max ‹_› ‹_›

theorem natDegree_mul_le_of_le {a b : Nat} {f g : R[X]} (hf : natDegree f ≤ a) (hg : natDegree g ≤ b) :
    natDegree (f * g) ≤ a + b :=
natDegree_mul_le.trans $ add_le_add ‹_› ‹_›

theorem natDegree_pow_le_of_le {a : Nat} (b : Nat) {f : R[X]} (hf : natDegree f ≤ a) :
    natDegree (f ^ b) ≤ b * a :=
natDegree_pow_le.trans (Nat.mul_le_mul rfl.le ‹_›)

theorem degree_add_le_of_le {a b : WithBot Nat} {f g : R[X]} (hf : degree f ≤ a) (hg : degree g ≤ b) :
    degree (f + g) ≤ max a b :=
(f.degree_add_le g).trans $ max_le_max ‹_› ‹_›

theorem degree_mul_le_of_le {a b : WithBot Nat} {f g : R[X]} (hf : degree f ≤ a) (hg : degree g ≤ b) :
    degree (f * g) ≤ a + b :=
(f.degree_mul_le _).trans $ add_le_add ‹_› ‹_›

theorem degree_pow_le_of_le {a : WithBot Nat} (b : Nat) {f : R[X]} (hf : degree f ≤ a) :
    degree (f ^ b) ≤ b * a := by
  apply (degree_pow_le _ _).trans
  rw [nsmul_eq_mul]
  induction b with
    | zero => simp [degree_one_le]
    | succ n hn =>
      rw [Nat.cast_succ, add_mul, add_mul, one_mul, one_mul]
      exact (add_le_add_left hf _).trans (add_le_add_right hn _)

theorem degree_nat_cast_le (n : Nat) : degree (n : R[X]) ≤ 0 := degree_le_of_natDegree_le (by simp)

theorem degree_zero_le : degree (0 : R[X]) ≤ 0 := natDegree_eq_zero_iff_degree_le_zero.mp rfl

end Lemmas__in_a_dependent_PR

theorem natDegree_C_le (a : R) : natDegree (C a) ≤ 0 := (natDegree_C a).le
theorem natDegree_nat_cast_le (n : Nat) : natDegree (n : R[X]) ≤ 0 := (natDegree_nat_cast _).le
theorem natDegree_zero_le : natDegree (0 : R[X]) ≤ 0 := natDegree_zero.le
theorem natDegree_one_le : natDegree (1 : R[X]) ≤ 0 := natDegree_one.le

end semiring

section ring
variable [Ring R]

section Lemmas__in_a_dependent_PR

theorem natDegree_neg_le_of_le {a : Nat} {f : R[X]} (hf : natDegree f ≤ a) : natDegree (- f) ≤ a :=
f.natDegree_neg.le.trans ‹_›

theorem natDegree_sub_le_of_le {a b : Nat} {f g : R[X]} (hf : natDegree f ≤ a) (hg : natDegree g ≤ b) :
    natDegree (f - g) ≤ max a b :=
(f.natDegree_sub_le g).trans $ max_le_max ‹_› ‹_›

theorem degree_neg_le_of_le {a : WithBot Nat} {f : R[X]} (hf : degree f ≤ a) : degree (- f) ≤ a :=
f.degree_neg.le.trans ‹_›

theorem degree_sub_le_of_le {a b : WithBot Nat} {f g : R[X]} (hf : degree f ≤ a) (hg : degree g ≤ b) :
    degree (f - g) ≤ max a b :=
(f.degree_sub_le g).trans $ max_le_max ‹_› ‹_›

theorem degree_int_cast_le (n : Int) : degree (n : R[X]) ≤ 0 := degree_le_of_natDegree_le (by simp)

end Lemmas__in_a_dependent_PR

theorem natDegree_int_cast_le (n : Int) : natDegree (n : R[X]) ≤ 0 := (natDegree_int_cast _).le

end ring

end mylemmas

section Tactic

open Lean

/-- `isDegLE e` checks whether `e` is an `Expr`ession representing an inequality whose LHS is
the `natDegree/degree` of a polynomial with coefficients in a semiring `R`.
If `e` represents
*  `natDegree f ≤ d`, then it returns `(true,  f)`;
*  `degree f ≤ d`,    then it returns `(false, f)`;
*  anything else, then it throws an error.
-/
def isDegLE (e : Expr) : CoreM (Bool × Expr) := do
  match e.consumeMData.getAppFnArgs with
    -- check that the target is an inequality `≤`...
    | (``LE.le, #[_, _, lhs, _rhs]) => match lhs.getAppFnArgs with
      -- and that the LHS is `natDegree ...` or `degree ...`
      | (``degree, #[_R, _iSR, pol])    => return (false, pol)
      | (``natDegree, #[_R, _iSR, pol]) => return (true, pol)
      | (na, _) => throwError (m!"Expected an inequality of the form\n\n" ++
        f!"  'f.natDegree ≤ d'  or  'f.degree ≤ d',\n\ninstead, {na} appears on the LHS")
    |  (na, _)  => throwError m!"Expected an inequality instead of '{na}', '{e}'"

/--  `getPolsName pol π` takes as input
*  the `Expr`ession `pol`, assuming that it represents a `Polynomial`;
*  the function `π : Name × Name → Name`, typically `π` equals `Prod.fst` for a goal of type
   `natDegree f ≤ d` or `π` equals `Prod.snd` for a goal of type `degree f ≤ d`.

If `pol` is an `.app`, then it returns the list of arguments of `pol` that also represent
`Polynomial`s, together with the `Name` of the theorem that `cDegCore` applies.

The only exception is when `pol` represents `↑(polFun _) : α → Polynomial _`,
and `polFun` is not `monomial` or `C`.
In this case, the output is data for error-reporting in `cDegCore`.
-/
def getPolsName (pol : Expr) (π : Name × Name → Name) : List Expr × Name :=
match pol.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, f, g])           => ([f,g], π (``natDegree_add_le_of_le, ``degree_add_le_of_le))
  | (``HSub.hSub, #[_, _, _, _, f, g])           => ([f,g], π (``natDegree_sub_le_of_le, ``degree_sub_le_of_le))
  | (``HMul.hMul, #[_, _, _, _, f, g])           => ([f,g], π (``natDegree_mul_le_of_le, ``degree_mul_le_of_le))
  | (``HPow.hPow, #[_, _, _, _, f, _n])          => ([f], π (``natDegree_pow_le_of_le, ``degree_pow_le_of_le))
  | (``Neg.neg,   #[_, _, f])                    => ([f], π (``natDegree_neg_le_of_le, ``degree_neg_le_of_le))
  | (``Polynomial.X, _)                          => ([], π (``natDegree_X_le, ``degree_X_le))
  -- can I avoid the tri-splitting `n = 0`, `n = 1`, and generic `n`?
  | (``OfNat.ofNat, #[_, (.lit (.natVal 0)), _]) => ([], π (``natDegree_zero_le, ``degree_zero_le))
  | (``OfNat.ofNat, #[_, (.lit (.natVal 1)), _]) => ([], π (``natDegree_one_le, ``degree_one_le))
  | (``OfNat.ofNat, _)                           => ([], π (``natDegree_nat_cast_le, ``degree_nat_cast_le))
  | (``Nat.cast, _)                              => ([], π (``natDegree_nat_cast_le, ``degree_nat_cast_le))
  | (``NatCast.natCast, _)                       => ([], π (``natDegree_nat_cast_le, ``degree_nat_cast_le))
  | (``Int.cast, _)                              => ([], π (``natDegree_int_cast_le, ``degree_int_cast_le))
  | (``IntCast.intCast, _)                       => ([], π (``natDegree_int_cast_le, ``degree_int_cast_le))
  -- deal with `monomial` and `C`
  | (``FunLike.coe, #[_, _, _, _, polFun, _c]) => match polFun.getAppFnArgs with
    | (``monomial, _) => ([], π (``natDegree_monomial_le, ``degree_monomial_le))
    | (``C, _)        => ([], π (``natDegree_C_le, ``degree_C_le))
    | _               => ([polFun], .anonymous)
  -- possibly, all that's left is the case where `pol` is an `fvar` and its `Name` is `.anonymous`
  | _ => ([], π (``le_rfl, ``le_rfl))

/-- `cDegCore (pol, mv) π` takes as input
*  a pair of an `Expr`ession `pol` and an `MVarId` `mv`, where
*  *  `pol` represents a polynomial;
*  *  `mv` represents a goal;
*  a function `π : Name × Name → Name`, typically `π` equals `Prod.fst` for a goal of type
   `natDegree f ≤ d` or `π` equals `Prod.snd` for a goal of type `degree f ≤ d`.

`cDegCore` assumes that `mv` has type `natDegree f ≤ ?_` or `degree f ≤ ?_`.
Note that the RHS of the inequality is a meta-variable: the exact value of `?_` is determined
along the way.
`cDegCore`  recurses into the shape of `pol` to produce a proof of `natDegree f ≤ d` or of
`degree f ≤ d`, where `d` is an appropriately constructed element of `ℕ` or `WithBot ℕ`.

Hopefully, the tactic should not really fail when the inputs are as specified.

The optional `db` flag is for debugging: if `db = true`, then the tactic prints useful information.
-/
partial
def cDegCore (polMV : Expr × MVarId) (π : Name × Name → Name) (db : Bool := false) :
    MetaM (List (Expr × MVarId)) := do
let (pol, mv) := polMV
let polEx := ← (pol.getAppFn :: pol.getAppArgs.toList).mapM Meta.ppExpr
if db then
  if pol.ctorName != "app" then logInfo m!"* pol.ctorName: {pol.ctorName}\n"
  else logInfo m!"* getAppFnArgs\n{polEx}\n* pol head app\n{pol.getAppFnArgs.1}"
let (pols, na) := getPolsName pol π
if na.isAnonymous then throwError m!"'compute_degree_le' is undefined for {← Meta.ppExpr pols[0]!}"
let once := pols.zip (← mv.applyConst na)
return (← once.mapM fun x => cDegCore x π db).join

/-- Allows the syntax expressions
* `compute_degree_le`,
* `compute_degree_le !`,
* `compute_degree_le -debug`
* `compute_degree_le ! -debug`.
-/
syntax (name := computeDegreeLE) "compute_degree_le" "!"? "-debug"? : tactic

/--  Allows writing `compute_degree_le!` with no space preceding `!`. -/
macro "compute_degree_le!" dbg:"-debug"? : tactic => `(tactic| compute_degree_le ! $[-debug%$dbg]?)

open Elab.Tactic in
/--
`compute_degree_le` is a tactic to solve goals of the form `natDegree f ≤ d` or `degree f ≤ d`.

The tactic first replaces `natDegree f ≤ d` with `d' ≤ d`,
where `d'` is an internally computed guess for which the tactic proves the inequality
`natDegree f ≤ d'`.

Next, it applies `norm_num` to `d'`, in the hope of closing also the `d' ≤ d` goal.

The variant `compute_degree_le!` first applies `compute_degree_le`.
Then it uses `norm_num` on the whole inequality `d' ≤ d` and tries `assumption`.

There is also a "debug-mode", where the tactic prints some information.
This is activated by using `compute_degree_le -debug` or `compute_degree_le! -debug`.
-/
elab_rules : tactic | `(tactic| compute_degree_le $[!%$str]? $[-debug%$debug]?) => focus do
  let (isNatDeg?, lhs) := ← isDegLE (← getMainTarget)
  let π := if isNatDeg? then Prod.fst else Prod.snd
  -- * if the original goal is `natDegree f ≤ d`, then
  --   `le_goals = [⊢ natDegree f ≤ ?_,  ⊢ ?_ ≤ d,  ⊢ ℕ]`
  -- * if the original goal is `degree f ≤ d`, then
  --   `le_goals = [⊢ degree f ≤ ?_,     ⊢ ?_ ≤ d,  ⊢ WithBot ℕ]`
  let le_goals := ← (← getMainGoal).applyConst ``le_trans
  let nfle_pf := ← cDegCore (← instantiateMVars lhs, le_goals[0]!) π (db := debug.isSome)
  setGoals [le_goals[1]!]
  if debug.isSome then logInfo m!"Computed proof:\n{nfle_pf}"
  if str.isSome then evalTactic (← `(tactic| norm_num <;> try assumption))
  else evalTactic (← `(tactic| conv_lhs => norm_num))

end Tactic

end Mathlib.Tactic.ComputeDegree
