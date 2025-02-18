import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)

#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat
  apply le_inf
  apply inf_le_right
  apply inf_le_left


example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  have hx : x ⊓ y ⊓ z ≤ x := by
    apply le_trans
    show x ⊓ y ⊓ z ≤ x ⊓ y; apply inf_le_left
    show x ⊓ y ≤ x; apply inf_le_left
  have hy : x ⊓ y ⊓ z ≤ y := by
    apply le_trans
    show x ⊓ y ⊓ z ≤ x ⊓ y; apply inf_le_left
    show x ⊓ y ≤ y; apply inf_le_right
  have hx' : x ⊓ (y ⊓ z) ≤ x := by apply inf_le_left
  have hy' : x ⊓ (y ⊓ z) ≤ y := by
    apply le_trans
    show x ⊓ (y ⊓ z) ≤ y ⊓ z; apply inf_le_right
    show y ⊓ z ≤ y; apply inf_le_left
  have hz' : x ⊓ (y ⊓ z) ≤ z := by
    apply le_trans
    apply inf_le_right; apply inf_le_right
  have hz : x ⊓ y ⊓ z ≤ z := by apply inf_le_right
  apply le_antisymm
  . apply le_inf
    apply hx
    apply le_inf
    apply hy
    apply hz
  . apply le_inf
    apply le_inf
    apply hx'
    apply hy'
    apply hz'


example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat
  apply sup_le
  apply le_sup_right
  apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  have hx : x ≤ x ⊔ (y ⊔ z) := by
    apply le_sup_left
  have hy : y ≤ x ⊔ (y ⊔ z) := by
    apply le_trans
    show y ≤ y ⊔ z
    apply le_sup_left
    show y ⊔ z ≤ x ⊔ (y ⊔ z)
    apply le_sup_right
  have hz : z ≤ x ⊔ (y ⊔ z) := by
    apply le_trans
    show z ≤ y ⊔ z
    apply le_sup_right
    apply le_sup_right
  have hx' : x ≤ x ⊔ y ⊔ z := by
    apply le_trans
    show x ≤ x ⊔ y
    apply le_sup_left
    apply le_sup_left
  have hy' : y ≤ x ⊔ y ⊔ z := by
    apply le_trans
    show y ≤ x ⊔ y
    apply le_sup_right
    apply le_sup_left
  have hz' : z ≤ x ⊔ y ⊔ z := by apply le_sup_right
  apply le_antisymm
  . apply sup_le
    apply sup_le
    apply hx
    apply hy
    apply hz
  . apply sup_le
    apply hx'
    apply sup_le
    apply hy'
    apply hz'


theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  . apply inf_le_left
  . apply le_inf
    apply le_refl
    show x ≤ x ⊔ y
    apply le_sup_left


theorem absorb2 : x ⊔ x ⊓ y = x := by
  have h : x ⊔ x ⊓ y ≤ x := by
    apply sup_le
    apply le_refl
    apply inf_le_left
  have h' : x ≤ x ⊔ x ⊓ y := by
    apply le_sup_left
  apply le_antisymm
  apply h
  apply h'

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h]
  rw [inf_comm (a ⊔ b), absorb1]
  rw [@inf_comm _ _ (a ⊔ b)]
  rw [h]
  rw [← sup_assoc]
  rw [@inf_comm _ _ c]
  rw [absorb2]
  rw [@inf_comm _ _ c]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h]
  rw [@sup_comm _ _ (a ⊓ b), absorb2]
  rw [@sup_comm _ _ (a ⊓ b)]
  rw [h, ← inf_assoc, @sup_comm _ _ c]
  rw [absorb1, @sup_comm _ _ c]

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  have h' : a - a ≤ b - a := by
    rw [sub_eq_add_neg, sub_eq_add_neg]
    apply add_le_add_right
    apply h
  rw [← add_right_neg a, ← sub_eq_add_neg]
  apply h'

example (h: 0 ≤ b - a) : a ≤ b := by
  rw [← add_zero a, ← sub_add_cancel b a, add_comm (b - a)]
  apply add_le_add_left
  apply h

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  sorry

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  sorry

end
