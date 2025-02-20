import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

section
variable {α : Type*}
variable (s t u : Set α)
open Set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x ⟨xs, xu⟩
  have xt : x ∈ t := h xs
  exact ⟨xt, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, (xt | xu)⟩
  . left; exact ⟨xs, xt⟩
  . right; exact ⟨xs, xu⟩

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  . constructor
    exact xs
    left; exact xt
  . constructor
    exact xs
    right; exact xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  constructor
  exact xs
  intro h
  rcases h with xt | xu
  . exfalso; exact xnt xt
  . exfalso; exact xnu xu

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, xntu⟩
  constructor
  . constructor; exact xs
    intro xt
    have xtu : x ∈ t ∪ u := by left; exact xt
    exfalso; exact xntu xtu
  . intro xu
    have xtu : x ∈ t ∪ u := by right; exact xu
    exfalso; exact xntu xtu

example : s ∩ t = t ∩ s := by
  ext x
  constructor
  . rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  . rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩


example : s ∩ t = t ∩ s :=
  Set.ext fun x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

example : s ∩ (s ∪ t) = s := by
  ext x
  constructor
  . rintro ⟨xs, _⟩; exact xs
  . intro xs
    constructor
    exact xs
    left; exact xs


example : s ∪ s ∩ t = s := by
  ext x
  constructor
  . rintro (xs | ⟨xs, xt⟩) <;> exact xs
  . intro xs; left; exact xs

example : s \ t ∪ t = s ∪ t := by
  ext x
  constructor
  . rintro (⟨xs, xnt⟩ | xt)
    . left; exact xs
    . right; exact xt
  . by_cases h : x ∈ t
    . intro; right; exact h
    . rintro (xs | xt)
      . left; constructor; exact xs; exact h
      . right; exact xt

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  constructor
  . rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩)
    . constructor
      left; exact xs
      intro ⟨xs, xt⟩; exfalso; exact xnt xt
    . constructor
      right; exact xt
      intro ⟨xs, xt⟩; exfalso; exact xns xs
  . rintro ⟨xs | xt, xnst⟩
    . left; constructor; exact xs; intro xt; exact xnst ⟨xs, xt⟩
    . right; constructor; exact xt; intro xs; exact xnst ⟨xs, xt⟩

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens]
  rw [odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  apply em

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n ⟨nprime, ngt2⟩ neven
  have nodd : Odd n := by
    rcases Nat.Prime.eq_two_or_odd nprime with neq2 | nodd
    . have nne2 : n ≠ 2 := by exact Ne.symm (Nat.ne_of_lt ngt2)
      exfalso; exact nne2 neq2
    . exact Nat.odd_iff.mpr nodd
  have nneven : ¬ Even n := Nat.not_even_iff_odd.mpr nodd
  exact nneven neven

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

example
    (h₀ : ∀ x ∈ s, ¬Even x)
    (h₁ : ∀ x ∈ s, Prime x)
    : ∀ x ∈ s, ¬Even x ∧ Prime x :=
    by
  intro x xs
  exact ⟨h₀ x xs, h₁ x xs⟩

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, xneven, xprime⟩
  exact ⟨x, xs, xprime⟩

section
variable (ssubt : s ⊆ t)

example
    (h₀ : ∀ x ∈ t, ¬Even x)
    (h₁ : ∀ x ∈ t, Prime x)
    : ∀ x ∈ s, ¬Even x ∧ Prime x
    := by
  intro x xs
  have xneven : ¬ Even x := by
    apply h₀
    apply ssubt xs
  have xprime : Prime x := by
    apply h₁
    apply ssubt xs
  exact ⟨xneven, xprime⟩

example
    (h : ∃ x ∈ s, ¬Even x ∧ Prime x)
    : ∃ x ∈ t, Prime x
    := by
  rcases h with ⟨x, xs, xneven, xprime⟩
  have xt : x ∈ t := ssubt xs
  exact ⟨x, xt, xprime⟩

end

end

section
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  . rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, ⟨xAi, xs⟩⟩
  . rintro ⟨i, ⟨xAi, xs⟩⟩
    constructor; exact xs; exact ⟨i, xAi⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  . intro h
    have hA : ∀ (i : I), x ∈ A i := by intro i; exact (h i).1
    have hB : ∀ (i : I), x ∈ B i := by intro i; exact (h i).2
    exact ⟨hA, hB⟩
  . intro ⟨hA, hB⟩
    intro i
    exact ⟨hA i, hB i⟩

example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp only [mem_iInter, mem_union]
  constructor
  . rintro (xs | hA)
    . intro i; right; exact xs
    . intro i; left; exact hA i
  . intro h
    by_cases xs : x ∈ s
    . left; exact xs
    . right; intro i
      have : x ∈ A i ∨ x ∈ s := h i
      rcases this with xAi | xs
      . assumption
      . contradiction

def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  rw [mem_iUnion₂]
  simp

example
    : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x }
    := by
  ext x
  simp


example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  simp
  intro x h
  exact Nat.eq_one_iff_not_exists_prime_dvd.mpr h

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  apply eq_univ_of_forall
  intro x
  simp
  rcases Nat.exists_infinite_primes x with ⟨p, pge, primep⟩
  use p
  constructor
  apply primep
  apply pge

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
