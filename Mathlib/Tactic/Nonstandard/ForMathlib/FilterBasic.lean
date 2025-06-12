import Mathlib.Order.Filter.Basic

namespace Filter

/-- This lemma already exists in Mathlib4 as `Eventually.choice`. 
This is a demonstration of how the Lean 3 version would be ported to Lean 4. -/
theorem eventually_choice' {α β : Type*} {r : α → β → Prop} {l : Filter α} 
    [l.NeBot] (h : ∀ᶠ x in l, ∃ y, r x y) : ∃ f : α → β, ∀ᶠ x in l, r x (f x) := by
  -- Classical reasoning is now automatic in Lean 4, no need for explicit `classical`
  -- The Lean 4 standard library provides the `choose!` tactic which handles the choice function
  haveI : Nonempty β := let ⟨_, hx⟩ := h.exists; hx.nonempty
  choose! f hf using fun x (hx : ∃ y, r x y) => hx
  exact ⟨f, h.mono hf⟩

/-- Alternative proof using the classical choice function directly, 
mimicking the Lean 3 proof structure more closely. -/
theorem eventually_choice'' {α β : Type*} {r : α → β → Prop} {l : Filter α} 
    [l.NeBot] (h : ∀ᶠ x in l, ∃ y, r x y) : ∃ f : α → β, ∀ᶠ x in l, r x (f x) := by
  -- We need β to be nonempty
  haveI : Nonempty β := by
    obtain ⟨x, hx⟩ := h.exists
    obtain ⟨y, _⟩ := hx
    exact ⟨y⟩
  -- Define the choice function using Classical.choose
  classical
  use fun x => if hx : ∃ y, r x y then Classical.choose hx 
              else Classical.choice ‹Nonempty β›
  -- Prove the property holds eventually
  filter_upwards [h] with x hx
  rw [dif_pos hx]
  exact Classical.choose_spec hx

end Filter