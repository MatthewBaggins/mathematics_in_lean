import MIL.Common
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic

namespace C06S01
noncomputable section

@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

#check Point.ext

example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  ext
  repeat' assumption

def myPoint1 : Point where
  x := 2
  y := -1
  z := 4

def myPoint2 : Point :=
  ⟨2, -1, 4⟩

def myPoint3 :=
  Point.mk 2 (-1) 4

structure Point' where build ::
  x : ℝ
  y : ℝ
  z : ℝ

#check Point'.build 2 (-1) 4

namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def add' (a b : Point) : Point where
  x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z

#check add myPoint1 myPoint2
#check myPoint1.add myPoint2

end Point

#check Point.add myPoint1 myPoint2
#check myPoint1.add myPoint2

namespace Point

protected theorem add_comm (a b : Point) : add a b = add b a := by
  rw [add]
  rw [add]
  ext
  repeat
  dsimp; apply add_comm
  -- ext <;> dsimp
  -- repeat' apply add_comm

example (a b : Point) : add a b = add b a := by simp [add, add_comm]

theorem add_x (a b : Point) : (a.add b).x = a.x + b.x :=
  rfl

def addAlt : Point → Point → Point
  | Point.mk x₁ y₁ z₁, Point.mk x₂ y₂ z₂ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

def addAlt' : Point → Point → Point
  | ⟨x₁, y₁, z₁⟩, ⟨x₂, y₂, z₂⟩ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

theorem addAlt_x (a b : Point) : (a.addAlt b).x = a.x + b.x := by
  rfl

theorem addAlt_comm (a b : Point) : addAlt a b = addAlt b a := by
  rw [addAlt, addAlt]
  -- the same proof still works, but the goal view here is harder to read
  ext <;> dsimp
  repeat' apply add_comm

protected theorem add_assoc (a b c : Point) : (a.add b).add c = a.add (b.add c) := by
  rw [add, add, add, add]
  ext
  repeat
  dsimp; apply add_assoc

def smul (r : ℝ) (a : Point) : Point :=
  ⟨r * a.x, r * a.y, r * a.z⟩


theorem smul_distrib
    (r : ℝ) (a b : Point)
    : (smul r a).add (smul r b) = smul r (a.add b)
    := by
  rw [add, add, smul, smul, smul]
  ext
  repeat
  dsimp; rw [← mul_add]

#check mul_add

end Point

structure StandardTwoSimplex where
  x : ℝ
  y : ℝ
  z : ℝ
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  z_nonneg : 0 ≤ z
  sum_eq : x + y + z = 1

theorem weighted_avg_nonneg
    (lambda : Real) (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
    (x y : Real) (x_nonneg : 0 ≤ x) (y_nonneg : 0 ≤ y)
    : 0 ≤ lambda * x + (1 - lambda) * y
    := by
  have lambda_x_nonneg : 0 ≤ lambda * x := mul_nonneg lambda_nonneg x_nonneg
  have one_minus_lambda_nonneg : 0 ≤ 1 - lambda := sub_nonneg_of_le lambda_le
  have lambda_y_nonneg : 0 ≤ (1 - lambda) * y := mul_nonneg one_minus_lambda_nonneg y_nonneg
  exact add_nonneg lambda_x_nonneg lambda_y_nonneg

namespace StandardTwoSimplex

def swapXy (a : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := a.y
  y := a.x
  z := a.z
  x_nonneg := a.y_nonneg
  y_nonneg := a.x_nonneg
  z_nonneg := a.z_nonneg
  sum_eq := by rw [add_comm a.y a.x, a.sum_eq]

noncomputable section

def midpoint (a b : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := (a.x + b.x) / 2
  y := (a.y + b.y) / 2
  z := (a.z + b.z) / 2
  x_nonneg := div_nonneg (add_nonneg a.x_nonneg b.x_nonneg) (by norm_num)
  y_nonneg := div_nonneg (add_nonneg a.y_nonneg b.y_nonneg) (by norm_num)
  z_nonneg := div_nonneg (add_nonneg a.z_nonneg b.z_nonneg) (by norm_num)
  sum_eq := by field_simp; linarith [a.sum_eq, b.sum_eq]


def weightedAverage (lambda : Real) (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
    (a b : StandardTwoSimplex) : StandardTwoSimplex where
  x := lambda * a.x + (1 - lambda) * b.x
  y := lambda * a.y + (1 - lambda) * b.y
  z := lambda * a.z + (1 - lambda) * b.z
  x_nonneg := weighted_avg_nonneg lambda lambda_nonneg lambda_le a.x b.x a.x_nonneg b.x_nonneg
  y_nonneg := weighted_avg_nonneg lambda lambda_nonneg lambda_le a.y b.y a.y_nonneg b.y_nonneg
  z_nonneg := weighted_avg_nonneg lambda lambda_nonneg lambda_le a.z b.z a.z_nonneg b.z_nonneg
  sum_eq := by
    calc
      lambda * a.x + (1 - lambda) * b.x + (lambda * a.y + (1 - lambda) * b.y) + (lambda * a.z + (1 - lambda) * b.z)
        = ((lambda * a.x + (1 - lambda) * b.x) + lambda * a.y)
        + (1 - lambda) * b.y + lambda * a.z + (1 - lambda) * b.z := by
          rw [← add_assoc, ← add_assoc]
      _ = lambda * (a.x + a.y) + (1 - lambda) * b.x + (1 - lambda) * b.y
        + lambda * a.z + (1 - lambda) * b.z := by
          rw [add_assoc (lambda * a.x),
              add_comm ((1 - lambda) * b.x),
              ← add_assoc,
              mul_add]
      _ = lambda * (a.x + a.y) + (1 - lambda) * (b.x + b.y)
        + lambda * a.z + (1 - lambda) * b.z := by
          rw [add_assoc (lambda * (a.x + a.y)),
              ← mul_add (1 - lambda)]
      _ = lambda * (a.x + a.y) + lambda * a.z
        + (1 - lambda) * (b.x + b.y) + (1 - lambda) * b.z := by
          rw [add_assoc (lambda * (a.x + a.y)),
              add_comm ((1 - lambda) * (b.x + b.y)),
              ← add_assoc]
      _ = lambda * (a.x + a.y + a.z) + (1 - lambda) * (b.x + b.y + b.z) := by
          rw [← mul_add, add_assoc, ← mul_add]
      _ = 1 := by rw [a.sum_eq, mul_one, b.sum_eq, mul_one]; ring

end

end StandardTwoSimplex

open BigOperators


structure StandardSimplex (n : ℕ) where
  V : Fin n → ℝ
  NonNeg : ∀ i : Fin n, 0 ≤ V i
  sum_eq_one : (∑ i, V i) = 1

namespace StandardSimplex

def midpoint (n : ℕ) (a b : StandardSimplex n) : StandardSimplex n
    where
  V i := (a.V i + b.V i) / 2
  NonNeg := by
    intro i
    apply div_nonneg
    · linarith [a.NonNeg i, b.NonNeg i]
    norm_num
  sum_eq_one := by
    simp [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
      a.sum_eq_one, b.sum_eq_one]
    field_simp

def weightedAverage {n : ℕ} (lambda : Real) (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
    (a b : StandardSimplex n) : StandardSimplex n where
  V i := lambda * (a.V i) + (1 - lambda) * (b.V i)

  NonNeg i := by
    simp
    show lambda * a.V i + (1 - lambda) * b.V i ≥ 0
    apply weighted_avg_nonneg
    exact lambda_nonneg
    exact lambda_le
    apply a.NonNeg
    apply b.NonNeg

  sum_eq_one := by
    simp
    have sum_dist : ∑ x, (lambda * a.V x) = lambda * (∑ x, a.V x)
                  := Eq.symm (Finset.mul_sum Finset.univ a.V lambda)
    have sum_dist' : ∑ x, ((1-lambda) * b.V x) = (1-lambda) * (∑ x, b.V x)
                   := Eq.symm (Finset.mul_sum Finset.univ b.V (1-lambda))
    calc
          ∑ x, (lambda * a.V x + (1 - lambda) * b.V x)
        = (∑ x, lambda * a.V x) + (∑ x, (1-lambda) * b.V x)
        := Finset.sum_add_distrib
      _ = lambda * (∑ x, a.V x) + (1-lambda) * (∑ x, b.V x)
        := by rw [sum_dist, sum_dist']
      _ = 1
        := by rw [a.sum_eq_one,  b.sum_eq_one]; ring

end StandardSimplex

structure IsLinear (f : ℝ → ℝ) where
  is_additive : ∀ x y, f (x + y) = f x + f y
  preserves_mul : ∀ x c, f (c * x) = c * f x

section
variable (f : ℝ → ℝ) (linf : IsLinear f)

#check linf.is_additive
#check linf.preserves_mul

end

def Point'' :=
  ℝ × ℝ × ℝ

def IsLinear' (f : ℝ → ℝ) :=
  (∀ x y, f (x + y) = f x + f y) ∧
  (∀ x c, f (c * x) = c * f x)

def PReal :=
  { y : ℝ // 0 < y }

section
variable (x : PReal)

#check x.val
#check x.property
#check x.1
#check x.2

end

def StandardTwoSimplex' :=
  { p : ℝ × ℝ × ℝ // 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.1 + p.2.1 + p.2.2 = 1 }

def StandardSimplex' (n : ℕ) :=
  { v : Fin n → ℝ // (∀ i : Fin n, 0 ≤ v i) ∧ (∑ i, v i) = 1 }

def StdSimplex := Σ n : ℕ, StandardSimplex n

section
variable (s : StdSimplex)

#check s.fst
#check s.snd

#check s.1
#check s.2

end
