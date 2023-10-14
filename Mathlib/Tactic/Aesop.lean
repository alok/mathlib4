/-
Copyright (c) Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Aesop
import Mathlib.Tactic.Relation.Rfl
import Std.Tactic.Ext

/-!
# Configuration of `aesop` for Mathlib.

We add `ext` and `intro` as unsafe rules (so they can be backtracked if they don't work out).
Adding `intro` has the effect of allowing looking inside default transparency definitions for
lambdas.

We add Mathlib's version of `rfl`.
-/

namespace Std.Tactic.Ext
open Lean Elab Tactic

/-- A wrapper for `ext` that we can pass to `aesop`. -/
def extCore' : TacticM Unit := do
  evalTactic (← `(tactic| ext))

end Std.Tactic.Ext

-- We turn on `ext` inside `aesop`, as an unsafe tactic.
attribute [aesop unsafe tactic] Std.Tactic.Ext.extCore'

open Lean Elab Tactic in
def Aesop.intro : TacticM Unit := do evalTactic (← `(tactic| intro))

-- We turn on `intro` inside `aesop` as an unsafe rule,
-- so we can attempt introductions through default reducibility definitions.
attribute [aesop unsafe tactic] Aesop.intro

-- We turn on the mathlib version of `rfl` inside `aesop`.
attribute [aesop safe tactic] Mathlib.Tactic.rflTac
