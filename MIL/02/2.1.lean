import Mathlib.Data.Real.Basic
import Mathlib.Tactic


example (a b c: ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_comm a c]
  rw [mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc]
  rw [mul_comm a b]
  rw [mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm]
  rw [← mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc a]
  rw [mul_comm a]
  rw [mul_assoc b]


example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a b c]
  rw [h]
  rw [mul_assoc a e f]


example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp]
  rw [mul_comm]
  rw [hyp']
  rw [sub_self]

section

variable (a b c d e f g : ℝ)

#check a
#check mul_comm a b

#check (a : ℝ)



example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

end

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

variable (a b c d e : ℝ)

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * c)]
  rw [add_comm (b * c)]
  rw [← add_assoc]

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
  calc
    (a + b) * (c + d) = a * c + b * c + (a * d + b * d) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * c + (b * c + a * d) + b * d := by
      rw [← add_assoc, add_assoc (a * c)]
    _ = a * c + (a * d + b * c) + b * d := by
      rw [add_comm (b * c)]
    _ = a * c + a * d + b * c + b * d := by
      rw [← add_assoc]

example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  rw [add_mul, mul_sub, mul_sub, add_sub]
  rw [mul_comm a b, sub_add, sub_self, sub_zero]
  rw [pow_two, pow_two]

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp


-- Tactic 'ring' is by 'import Mathlib.Tactic'

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring


example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]

-- Some theorems hold in simular algebraic structure


variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)


variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring
