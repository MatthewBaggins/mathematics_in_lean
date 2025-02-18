import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬ (b < a) := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  -- linarith
  have h' : f x < f x := by apply lt_of_le_of_lt this hx
  apply lt_irrefl (f x) h'

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  rintro ⟨a, flba⟩
  rcases h a with ⟨x, hb⟩
  have : a ≤ f x := flba x
  linarith

example : ¬FnHasUb fun x ↦ x := by
  rintro ⟨a, ha⟩
  have : a + 1 ≤ a := ha (a + 1)
  linarith


#check (not_le_of_gt : a > b → ¬(a ≤ b))
#check (not_lt_of_ge : a ≥ b → ¬(a < b))
#check (lt_of_not_ge : ¬(a ≥ b) → a < b)
#check (le_of_not_gt : ¬(a > b) → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro ageb
  have : f a ≥ f b := by
    apply h
    apply ageb
  linarith

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro monof
  have : f a ≤ f b := by apply monof h
  linarith

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    intro x y xley
    linarith
  have h' : f 1 ≤ f 0 := le_refl _
  have : 1 ≤ (0 : ℝ) := h monof h'
  linarith

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro xgt0
  have : x < x := h x xgt0
  apply lt_irrefl x this
  -- linarith

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x hpx
  have : ∃ x, P x := ⟨x, hpx⟩
  apply h this

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  rintro ⟨x, hpx⟩
  have hnpx : ¬P x := h x
  apply hnpx hpx

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  have : ∃ x, ¬P x := ⟨x, h''⟩
  apply h' this

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro h'
  rcases h with ⟨x, hnpx⟩
  have hpx : P x := h' x
  apply hnpx hpx


example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q := by
  by_contra h'
  apply h h'

example (h : Q) : ¬¬Q := by
  intro h'
  apply h' h

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a
  by_contra h'
  have fub : FnHasUb f := by
    use a
    intro x
    by_contra h''
    have : f x > a := lt_of_not_ge h''
    exact h' ⟨x, this⟩
  apply h fub

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  by_contra h'
  push_neg at h'
  have monof : Monotone f := by
    intro x y xley
    apply h' x y xley
  apply h monof

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end
