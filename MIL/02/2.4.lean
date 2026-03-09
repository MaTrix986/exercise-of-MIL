import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
-- import Mathlib.Analysis.Complex.Exponential

import Mathlib.Tactic
import Mathlib.Util.Delaborators

variable (a b c d e f : ℝ)


#check min

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)


example : min a b = min b a := by
  apply le_antisymm
  . show min a b ≤ min b a
    apply le_min
    . apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left


example : max a b = max b a := by


  have h : ∀ x y : ℝ, max x y ≤ max y x := by
    intro x y
    apply max_le
    apply le_max_right
    apply le_max_left

  apply le_antisymm
  apply h a b
  apply h b a


example : min (min a b) c = min a (min b c) := by

  apply le_antisymm
  . apply le_min
    . apply le_trans
      apply min_le_left
      apply min_le_left

    . apply le_min
      . apply le_trans
        apply min_le_left
        apply min_le_right
      . apply min_le_right

  . apply le_min
    . apply le_min
      . apply min_le_left
      . apply le_trans
        . apply min_le_right
        . apply min_le_left

    . apply le_trans
      . apply min_le_right
      . apply min_le_right


-- It's a bit hard to come up with 'le_trans'

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  . apply add_le_add_left
    apply min_le_left
  . apply add_le_add_left
    apply min_le_right

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  . apply aux
  have h : min (a + c) (b + c) = min (a + c) (b + c) - c + c := by rw [sub_add_cancel]
  have h1 := aux (a + c) (b + c) (-c)
  rw [add_neg_cancel_right, add_neg_cancel_right] at h1

  rw [h]
  apply add_le_add_left

  apply h1

#check abs_add_le
#check add_sub_cancel_right
#check sub_add_cancel

example : |a| - |b| ≤ |a - b| := by
  have h := abs_add_le (a - b) b
  rw [sub_add_cancel] at h
  linarith


variable (x y z : ℝ)


example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  . apply dvd_add
    . apply dvd_mul_of_dvd_right
      apply dvd_mul_right
    . apply dvd_mul_left

  . apply dvd_mul_of_dvd_right
    exact h

variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)


example : Nat.gcd m n = Nat.gcd n m := by
  have h : ∀ x y : ℕ, Nat.gcd x y ∣ Nat.gcd y x := by
    intro x y
    apply Nat.dvd_gcd
    . apply gcd_dvd_right
    . apply gcd_dvd_left
  apply dvd_antisymm
  apply h
  apply h
