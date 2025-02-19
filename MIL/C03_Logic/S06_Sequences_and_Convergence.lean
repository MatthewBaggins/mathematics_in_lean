import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add
    {s t : ℕ → ℝ} {a b : ℝ}
    (cs : ConvergesTo s a)
    (ct : ConvergesTo t b)
    : ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  rw [← sub_sub, sub_eq_add_neg, sub_eq_add_neg]
  rw [add_assoc, add_assoc, ← add_assoc (t n), add_comm (t n), ← add_assoc, ← add_assoc, add_assoc (s n + -a)]
  rw [← sub_eq_add_neg, ← sub_eq_add_neg]
  calc
    |s n - a + (t n - b)| ≤ |s n - a| + |(t n - b)| := by
      apply abs_add
    _ < |s n - a| + (ε / 2) := by
      have : n ≥ Nt := by exact le_of_max_le_right hn
      apply add_lt_add_left
      apply ht n this
    _ < (ε / 2) + (ε / 2) := by
      have : n ≥ Ns := by exact le_of_max_le_left hn
      apply add_lt_add_right
      apply hs n this
    _ = ε := by linarith



theorem convergesTo_mul_const
    {s : ℕ → ℝ} {a : ℝ} (c : ℝ)
    (cs : ConvergesTo s a)
    : ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  dsimp
  let ε' := ε / |c|
  have ε'pos : 0 < ε' := by apply div_pos εpos acpos
  rcases cs ε' ε'pos with ⟨N, hN⟩
  use N
  intro n hn
  calc
    |c * s n - c * a| = |c * (s n - a)| := by rw [mul_sub]
    _ = |c| * |s n - a| := by apply abs_mul
    _ < |c| * ε' := by
      apply (mul_lt_mul_left acpos).mpr
      apply hN
      exact hn
    _ = |c| * (ε / |c|) := by linarith
    _ = ε := mul_div_cancel₀ ε (abs_ne_zero.mpr h)




theorem exists_abs_le_of_convergesTo
    {s : ℕ → ℝ} {a : ℝ}
    (cs : ConvergesTo s a)
    : ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n hn
  calc
    |s n| = |s n + 0| := by rw [add_zero]
    _ = |s n + (- a + a)| := by rw [neg_add_cancel]
    _ = |s n + -a + a| := by rw [← add_assoc]
    _ = |s n -a + a| := by rfl
    _ ≤ |s n - a| + |a| := by apply abs_add
    _ < 1 + |a| := by
      apply add_lt_add_right
      apply h n hn
    _ = |a| + 1 := by apply add_comm


theorem aux
    {s t : ℕ → ℝ} {a : ℝ}
    (cs : ConvergesTo s a)
    (ct : ConvergesTo t 0)
    : ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  let ε' := ε / B
  have ε'pos : ε' > 0 := div_pos εpos Bpos
  rcases ct _ ε'pos with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n ngt
  have ngeN₀ : n ≥ N₀ := le_of_max_le_left ngt
  have ngeN₁ : n ≥ N₁ := le_of_max_le_right ngt
  calc
    |s n * t n - 0| = |s n * (t n - 0)| := by ring
    _ = |s n| * |t n - 0| := by apply abs_mul
    _ < B * ε' := by
        apply mul_lt_mul''
        . apply h₀
          apply ngeN₀
        . apply h₁
          apply ngeN₁
        apply abs_nonneg
        apply abs_nonneg
    _ = B * (ε / B) := by linarith
    _ = ε := by
      apply mul_div_cancel₀
      exact Ne.symm (ne_of_lt Bpos)


theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique
    {s : ℕ → ℝ} {a b : ℝ}
    (sa : ConvergesTo s a)
    (sb : ConvergesTo s b)
    : a = b
    := by
  by_contra abne
  have : |a - b| > 0 := abs_sub_pos.mpr abne
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    apply hNa
    apply le_max_left
  have absb : |s N - b| < ε := by
    apply hNb
    apply le_max_right
  have : |a - b| < |a - b| := by
    calc
      |a - b| = |a + 0 - b| := by rw [add_zero]
      _ ≤ |a + (- s N + s N) - b| := by rw [neg_add_cancel]
      _ = |a + - s N + s N - b| := by rw [← add_assoc]
      _ = |a - s N + s N - b| := by rfl
      _ = |(a - s N) + (s N - b)| := by rw [← add_sub]
      _ ≤ |a - s N| + |s N - b| := by apply abs_add
      _ = |s N - a| + |s N - b| := by rw [abs_sub_comm (s N) a]
      _ < ε + ε := add_lt_add absa absb
      _ = |a - b|/2 + |a - b|/2 := by rfl
      _ = |a - b| := by ring
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
