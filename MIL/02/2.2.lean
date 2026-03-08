import Mathlib.Data.Real.Basic
import Mathlib.Tactic


namespace MyRing


-- {} means 'R' is an implicit argument
variable {R : Type*} [Ring R]

-- Ring axioms
#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)


theorem add_zero (a: R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_right_neg, add_zero]

-- {} means 'a', 'b', 'c' are  implicit arguments, which can be omitted in reference (not definition).
-- 'add_right_cancal' should be referred as 'add_right_cancel h' instead of 'add_right_cancel a b c h', because 'h' has implied 'a', 'b', 'c'

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← neg_add_cancel_left a b]
  rw [← neg_add_cancel_left a c]
  rw [h]

theorem add_right_cancel  {a b c : R} (h : a + b = c + b) : a = c := by
  rw [← neg_add_cancel_left b a]
  rw [← neg_add_cancel_left b c]
  rw [add_comm a b, add_comm c b] at h
  rw [h]

#check (0 : R)


theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]
  -- or 'apply add_left_cancel h'

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 * a + 0 := by
    rw [← add_mul, add_zero, add_zero]
  apply add_left_cancel h


theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  rw [← add_right_neg a] at h
  rw [add_left_cancel h]

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  rw [← neg_add_cancel b] at h
  rw [add_right_cancel h]

-- Must declare -0 ∈ R in that Lean does not know which '0' it is
theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  apply neg_eq_of_add_eq_zero
  rw [neg_add_cancel]

#check sub_eq_add_neg


theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg]
  rw [add_right_neg]

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  nth_rw 2 3 [← one_mul a]
  rw [← add_mul, one_add_one_eq_two]



end MyRing




namespace MyGroup

variable (G : Type*) [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  have h : (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 1 := by
    rw [mul_assoc, ← mul_assoc a⁻¹ a, inv_mul_cancel, one_mul, inv_mul_cancel]
  rw [← h, ← mul_assoc, inv_mul_cancel, one_mul]

theorem mul_one (a : G) : a * 1 = a := by
  rw [← inv_mul_cancel a, ← mul_assoc]
  rw [mul_inv_cancel, one_mul]


theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have h : b⁻¹ * a⁻¹ = (a * b)⁻¹ * (a * b) * b⁻¹ * a⁻¹ := by
    rw [inv_mul_cancel, one_mul]
  rw [h, mul_assoc (a * b)⁻¹, mul_assoc a b ]
  rw [mul_inv_cancel, mul_one, mul_assoc]
  rw [mul_inv_cancel, mul_one]

-- You can use 'noncomm_ring', 'ring', 'group', 'abel' to replace the tedious proofs


end MyGroup
