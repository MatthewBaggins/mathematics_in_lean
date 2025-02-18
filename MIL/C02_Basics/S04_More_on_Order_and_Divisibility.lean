import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

#check (le_max_left a b : a ≤ max a b)
#check (le_max_right a b : b ≤ max a b)
#check (max_le : a ≤ c → b ≤ c → max a b ≤ c)

example : min a b = min b a := by
  have h {x y : ℝ} : min x y ≤ min y x := by
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

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
  apply h
  apply h

example : min (min a b) c = min a (min b c) := by
  have ha : min (min a b) c ≤ a := by
    apply le_trans
    show min (min a b) c ≤ min a b
    apply min_le_left
    show min a b ≤ a
    apply min_le_left
  have hb : min (min a b) c ≤ b := by
    apply le_trans
    apply min_le_left
    apply min_le_right
  have hc : min (min a b) c ≤ c := by apply min_le_right
  have ha' : min a (min b c) ≤ a := by apply min_le_left
  have hb' : min a (min b c) ≤ b := by
    apply le_trans
    show min a (min b c) ≤ min b c
    apply min_le_right
    show min b c ≤ b
    apply min_le_left
  have hc' : min a (min b c) ≤ c := by
    apply le_trans
    apply min_le_right
    apply min_le_right
  apply le_antisymm
  . apply le_min
    apply ha
    apply le_min
    apply hb
    apply hc
  . apply le_min
    apply le_min
    apply ha'
    apply hb'
    apply hc'

example : max (max a b) c = max a (max b c) := by
  have ha : a ≤ max a (max b c) := by
    apply le_max_left
  have hb : b ≤ max a (max b c) := by
    apply le_trans
    show b ≤ max b c
    apply le_max_left
    show max b c ≤ max a (max b c)
    apply le_max_right
  have hc : c ≤ max a (max b c) := by
    apply le_trans
    show c ≤ max b c
    apply le_max_right
    show max b c ≤ max a (max b c)
    apply le_max_right
  have ha' : a ≤ max (max a b) c := by
    apply le_trans
    show a ≤ max a b; apply le_max_left
    show max a b ≤ max (max a b) c; apply le_max_left
  have hb' : b ≤ max (max a b) c := by
    apply le_trans
    show b ≤ max a b; apply le_max_right
    show max a b ≤ max (max a b) c; apply le_max_left
  have hc' : c ≤ max (max a b) c := by apply le_max_right
  apply le_antisymm
  . apply max_le
    apply max_le
    apply ha
    apply hb
    apply hc
  . apply max_le
    apply ha'
    apply max_le
    apply hb'
    apply hc'

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  have hac : min a b + c ≤ a + c := by
    apply add_le_add_right
    apply min_le_left
  have hbc : min a b + c ≤ b + c := by
    apply add_le_add_right
    apply min_le_right
  apply le_min
  apply hac
  apply hbc

example : min a b + c = min (a + c) (b + c) := by
  sorry

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| :=
  calc
    |a| - |b| = |a - b + b| - |b| := by rw [sub_add_cancel]
    _ ≤ |a - b| + |b| - |b| := by
      apply sub_le_sub_right
      apply abs_add
    _ ≤ |a - b| := by rw [add_sub_cancel_right]


example : |a| - |b| ≤ |a - b| :=
  calc
    |a| - |b| = |(a - b) + b| - |b| := by rw [sub_add_cancel]
    _ ≤ |a - b| + |b| - |b| := by
      apply sub_le_sub_right -- what's happening here?
      apply abs_add
    _ ≤ |a - b| := by rw [add_sub_cancel_right]


end

section
variable (w x y z : ℕ)

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
  . apply dvd_trans
    apply h
    apply dvd_mul_left

end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

-- example : Nat.gcd m n = Nat.gcd n m := by
example : m.gcd n = n.gcd m := by
  apply Nat.dvd_antisymm
  repeat
  apply Nat.dvd_gcd
  apply Nat.gcd_dvd_right
  apply Nat.gcd_dvd_left



end
