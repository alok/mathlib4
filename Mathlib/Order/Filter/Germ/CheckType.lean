import Mathlib.Order.Filter.Germ.Star

variable {ι : Type*} [Infinite ι] {α : Type*} [Field α] [IsStrictOrderedRing α]

def check_type : IsStrictOrderedRing (Hyper ι α) :=
  { instIsOrderedRingHyper, (Filter.Germ.instNontrivial : Nontrivial (Hyper ι α)) with
    le_of_add_le_add_left := sorry
    mul_lt_mul_of_pos_left := _
    mul_lt_mul_of_pos_right := sorry }
