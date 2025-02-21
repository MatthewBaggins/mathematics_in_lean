import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y
  constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  . intro h x xs
    have : f x ∈ f '' s := mem_image_of_mem f xs
    exact h this
  . intro h y ymem
    rcases ymem with ⟨x, xs, fxeqy⟩
    rw [← fxeqy]
    apply h xs


example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x ⟨y, ys, fyeqfx⟩
  have xeqy : x = y := h (Eq.symm fyeqfx)
  have : x ∈ s := mem_of_eq_of_mem xeqy ys
  exact this

example : f '' (f ⁻¹' u) ⊆ u := by
  intro y ⟨x, h, fxeqy⟩
  rw [← fxeqy]
  apply h

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  rintro y yu
  rcases h y with ⟨x, fxeqy⟩
  rw [← fxeqy]
  apply mem_image_of_mem
  apply mem_preimage.mpr
  apply mem_of_eq_of_mem fxeqy yu

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro y yfs
  rcases (mem_image f s y).mp yfs with ⟨x, xs, fxeqy⟩
  rw [← fxeqy]
  have xt : x ∈ t := h xs
  have : f x ∈ f '' t := by
    apply mem_image_of_mem
    exact xt
  exact this

#check mem_image

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x h'
  have : f x ∈ u := h'
  apply h h'

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  . rintro (h | h)
    . left; apply h
    . right; apply h
  . rintro (h | h)
    . left; apply h
    . right; apply h

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, ⟨xs, xt⟩, fxeqy⟩
  rw [← fxeqy]
  constructor
  . apply mem_image_of_mem; exact xs
  . apply mem_image_of_mem; exact xt

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨yfs, yft⟩
  rcases (mem_image f s y).mp yfs with ⟨x, xs, fxeqy⟩
  rcases (mem_image f t y).mp yft with ⟨x', x't, fx'eqy⟩
  have fxeqfx' : f x = f x' := Eq.trans fxeqy (Eq.symm fx'eqy)
  have xeqx' : x = x' := h fxeqfx'
  have xt : x ∈ t := mem_of_eq_of_mem (h fxeqfx') x't
  have xst : x ∈ s ∩ t := ⟨xs, xt⟩
  have : f x ∈ f '' (s ∩ t) := mem_image_of_mem f xst
  exact mem_of_eq_of_mem (Eq.symm fxeqy) this


example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro y ⟨yfs, ynft⟩
  rcases (mem_image f s y).mp yfs with ⟨x, xs, fxeqy⟩
  rw [← fxeqy]
  have fxnft : f x ∉ f '' t := by
    rw [← fxeqy] at ynft
    exact ynft
  have xnt : x ∉ t := by
    intro xt
    have fxft : f x ∈ f '' t := by
      apply mem_image_of_mem
      apply xt
    exfalso; exact fxnft fxft
  have xst : x ∈ s \ t := ⟨xs, xnt⟩
  apply mem_image_of_mem
  exact xst

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  intro x ⟨xfu, xnfv⟩
  have fxu : f x ∈ u := mem_preimage.mp xfu
  have fxnv : f x ∉ v := λ fxv ↦ xnfv fxv
  apply mem_preimage.mpr
  exact ⟨fxu, fxnv⟩

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  sorry




#check mem_image
#check mem_preimage
#check mem_image_of_mem
#check mem_of_eq_of_mem


example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  sorry

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  sorry

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  sorry

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  sorry

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  sorry

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  sorry

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  sorry

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  sorry

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  sorry

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  sorry

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f :=
  sorry

example : Surjective f ↔ RightInverse (inverse f) f :=
  sorry

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S
  sorry
  have h₃ : j ∉ S
  sorry
  contradiction

-- COMMENTS: TODO: improve this
end
