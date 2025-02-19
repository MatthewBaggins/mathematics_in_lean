import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

section
variable {α : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rintro x ⟨xs, xu⟩
  have xt : x ∈ t := h xs
  exact ⟨xt, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rintro x ⟨xs, xu⟩
  have xt : x ∈ t := h xs
  exact ⟨xt, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  · right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  . constructor
    exact xs
    left; exact xt
  . constructor
    exact xs;
    right; exact xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  · show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, xntu⟩
  have xnt : x ∉ t := by
    intro xt
    have : x ∈ t ∪ u := by left; exact xt
    apply xntu this
  have xnu : x ∉ u := by
    intro xu
    have : x ∈ t ∪ u := by right; exact xu
    apply xntu this
  constructor
  constructor
  exact xs
  exact xnt
  exact xnu


example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
  Set.ext fun x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s := by
    apply Subset.antisymm
    . intro x ⟨h, h'⟩
      exact ⟨h', h⟩
    . intro x ⟨h, h'⟩
      exact ⟨h', h⟩

example : s ∩ (s ∪ t) = s := by
  apply Subset.antisymm
  . intro x ⟨xs, xst⟩
    exact xs
  . intro x xs
    exact ⟨xs, Or.inl xs⟩


example : s ∪ s ∩ t = s := by
  apply Subset.antisymm
  . intro x
    rintro (xs | ⟨xs, xt⟩)
    exact xs; exact xs
  . intro x xs
    left; exact xs

example : s \ t ∪ t = s ∪ t := by
  ext x
  constructor
  . rintro (⟨xs, xnt⟩ | xt)
    . left; exact xs
    . right; exact xt
  . by_cases h : x ∈ t
    . rintro (xs | xt)
      . right; exact h
      . right; exact h
    . rintro (xs | xt)
      . left; exact ⟨xs, h⟩
      . right; exact xt

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  constructor
  . rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩)
    . constructor
      . left; exact xs
      . intro ⟨xs, xt⟩; exact xnt xt
    . constructor
      . right; exact xt
      . rintro ⟨xs, xt⟩; exact xns xs
  . rintro ⟨(xs | xt), xnst⟩
    . left
      constructor
      exact xs
      intro xt; exact xnst ⟨xs, xt⟩
    . right
      constructor
      exact xt
      intro xs; exact xnst ⟨xs, xt⟩

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  -- rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n
  rintro ⟨nprime, nge2⟩
  have h : n = 2 ∨ n % 2 = 1 := Nat.Prime.eq_two_or_odd nprime
  have : n % 2 = 1 := by
    rcases h with (neq2 | nodd)
    . have : n > 2 := by exact nge2
      have : n ≠ 2 := by exact Ne.symm (Nat.ne_of_lt nge2)
      exfalso; exact this neq2
    . exact nodd
  have : Odd n := Nat.odd_iff.mpr this
  exact Nat.not_even_iff_odd.mpr this

#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]

end

section

variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  -- use x, xs
  exact ⟨x, xs, prime_x⟩

section
variable (ssubt : s ⊆ t)

example
    (h₀ : ∀ x ∈ t, ¬Even x)
    (h₁ : ∀ x ∈ t, Prime x)
    : ∀ x ∈ s, ¬Even x ∧ Prime x
    := by
  rintro x xs
  have xt : x ∈ t := ssubt xs
  exact ⟨h₀ x xt, h₁ x xt⟩

example
    (h : ∃ x ∈ s, ¬Even x ∧ Prime x)
    : ∃ x ∈ t, Prime x
    := by
  rcases h with ⟨x, xs, ⟨xneven, xprime⟩⟩
  use x
  constructor
  exact ssubt xs
  exact xprime

end

end

section
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff]
  simp only [mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff]
  simp only [mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i


example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp only [mem_union]
  simp only [mem_iInter]
  constructor
  . rintro (xs | xI)
    . intro i; right; exact xs
    . intro i; left
      exact xI i
  . intro h
    by_cases xs : x ∈ s
    . left; exact xs
    . right
      intro i
      cases h i
      . assumption
      . contradiction





def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  sorry

end

section

open Set

variable {α : Type*} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl

end
