import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Basic
-- import Mathlib.Analysis.Complex.Exponential

import Mathlib.Tactic
import Mathlib.Util.Delaborators

-- PartialOrder

variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)

-- Lattice
variable {α : Type*} [Lattice α]

variable { x y z : α}

#check x < y -- is a 'prop'
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

-- ⊓, ⊔ is Lattice

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  . apply le_inf
    apply inf_le_right
    apply inf_le_left
  . apply le_inf
    apply inf_le_right
    apply inf_le_left


example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  . apply le_inf
    . apply le_trans
      apply inf_le_left
      apply inf_le_left
    . apply le_inf
      . apply le_trans
        apply inf_le_left
        apply inf_le_right
      . apply inf_le_right
  . apply le_inf
    . apply le_inf
      . apply inf_le_left
      . apply le_trans
        apply inf_le_right
        apply inf_le_left
    . apply le_trans
      apply inf_le_right
      apply inf_le_right

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  apply inf_le_left
  apply le_inf
  apply le_refl
  apply le_sup_left


theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  apply sup_le
  apply le_refl
  apply inf_le_left
  apply le_sup_left

-- DistribLattic

variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))


variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h]
  rw [inf_comm (a ⊔ b)]
  rw [inf_sup_self]
  rw [inf_comm (a ⊔ b)]
  rw [h]
  rw [← sup_assoc]
  rw [inf_comm c a]
  rw [sup_inf_self]
  rw [inf_comm]



example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h]
  rw [sup_comm (a ⊓ b)]
  rw [sup_inf_self]
  rw [sup_comm (a ⊓ b)]
  rw [h]
  rw [← inf_assoc]
  rw [sup_comm c a]
  rw [inf_sup_self]
  rw [sup_comm]

--

variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

theorem aux1 (h : a ≤ b) : 0 ≤ b - a := by
  rw [← sub_self a]
  rw [sub_eq_add_neg, sub_eq_add_neg]
  apply add_le_add_left
  exact h

theorem aux2 (h : 0 ≤ b - a) : a ≤ b := by
  rw [← add_zero a]
  rw [← sub_add_cancel b a]
  rw [add_comm (b - a)]
  apply add_le_add_right
  exact h


example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h1 : 0 ≤ (b - a) * c := mul_nonneg (aux1 _ _ h) h'
  rw [sub_mul] at h1
  exact aux2 _ _ h1
