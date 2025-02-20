import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 x with xnonneg | xneg
  . intro xltabsy
    rcases le_or_gt 0 y with ynonneg | yneg
    . left
      have : |y| = y := abs_of_nonneg ynonneg
      apply lt_of_lt_of_eq xltabsy this
    . right
      have : |y| = -y := abs_of_neg yneg
      apply lt_of_lt_of_eq xltabsy this
  . intro xltabsy
    rcases le_or_gt 0 y with ynonneg | yneg
    . left; apply lt_of_lt_of_le xneg ynonneg
    . right
      have : |y| = -y := abs_of_neg yneg
      apply lt_of_lt_of_eq xltabsy this

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with ynonneg | yneg
  . rw [abs_of_nonneg ynonneg]
    intros; left; assumption
  . rw [abs_of_neg yneg]
    intros; right; assumption


example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with ynonneg | yneg
  . rw [abs_of_nonneg ynonneg]
    intros; left; assumption
  . rw [abs_of_neg yneg]
    intros; right; assumption

namespace MyAbs

example (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with xnonneg | xneg
  . rw [abs_of_nonneg xnonneg]
  . have : 0 ≤ |x| := abs_nonneg x
    have : x < |x| := by
      apply lt_of_lt_of_le
      exact xneg
      exact this
    linarith

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  . rw [abs_of_nonneg h]
  . rw [abs_of_neg h]; linarith


theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with xnonneg | xneg
  . rw [abs_of_nonneg xnonneg]; linarith
  . rw [abs_of_neg xneg]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x+y) with hnonneg | hneg
  . rw [abs_of_nonneg hnonneg]
    apply add_le_add (le_abs_self x) (le_abs_self y)
  . rw [abs_of_neg hneg]
    rw [neg_add]
    apply add_le_add (neg_le_abs_self x) (neg_le_abs_self y)


theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  rcases le_or_gt 0 y with ynonneg | yneg
  . constructor
    . intro xltabsy
      rw [abs_of_nonneg ynonneg] at xltabsy
      left; exact xltabsy
    . rw [abs_of_nonneg ynonneg]
      rintro (xlty | xltny)
      . exact xlty
      . linarith
  . constructor
    . intro xltabsy
      rw [abs_of_neg yneg] at xltabsy
      right; exact xltabsy
    . rw [abs_of_neg yneg]
      rintro (xlty | xltny)
      . linarith
      . linarith



theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  rcases le_or_gt 0 x with xnonneg | xneg
  . rw [abs_of_nonneg xnonneg]
    constructor
    . intros; constructor <;> linarith
    . intros; linarith
  . rw [abs_of_neg xneg]
    constructor
    . intros; constructor <;> linarith
    . intros; linarith


end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt0 | xeq0 | xgt0
  . left; exact xlt0
  . exfalso; exact h xeq0
  . right; exact xgt0


example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with mdn | mdk
  . exact Dvd.dvd.mul_right mdn k
  . exact Dvd.dvd.mul_left mdk n

example {z : ℝ}
    (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1)
    : z ≥ 0 := by
  rcases h with ⟨x, y, rfl | rfl⟩
  <;> linarith [sq_nonneg x, sq_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : x ^ 2 - 1 = 0 := by linarith
  have : (x + 1) * (x - 1) = 0 := by linarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h' | h'
  . right; linarith
  . left; linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have : x^2 - y^2 = 0 := by linarith
  have : (x+y)*(x-y) = 0 := by linarith
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h' | h'
  . right; linarith
  . left; linarith


section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have : x^2 - 1 = 0 := by rw [← h, sub_self]
  have : (x+1)*(x-1) = 0 := by rw [← this]; ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h' | h'
  . right; exact eq_neg_iff_add_eq_zero.mpr h'
  . left; exact eq_of_sub_eq_zero h'


example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have : x^2-y^2 = 0 := by rw [← h, sub_self]
  have : (x+y)*(x-y) = 0 := by rw [← this]; ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h' | h'
  . right; exact eq_neg_iff_add_eq_zero.mpr h'
  . left; exact eq_of_sub_eq_zero h'

end

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  . assumption
  . exfalso; exact h h'


example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  . intro h
    by_cases h' : P
    . right; exact h h'
    . left; exact h'
  . rintro (hnp | hq)
    . intro hp
      exfalso; exact hnp hp
    . intros; exact hq
