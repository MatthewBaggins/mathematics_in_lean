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
  have : f x ∈ f '' s := by
    apply mem_image_of_mem
    apply xs
  apply mem_preimage.mpr this

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  . intro h x xs
    apply mem_preimage.mpr
    apply h
    apply mem_image_of_mem
    apply xs
  . intro h y yfs
    rcases (mem_image f s y).mp yfs with ⟨x, xs, fxeqy⟩
    have h' : x ∈ f⁻¹' v := h xs
    have : f x ∈ f '' (f⁻¹' v) := by
      apply mem_image_of_mem
      apply h'
    apply mem_of_eq_of_mem
    apply Eq.symm fxeqy
    apply h'

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x xffs
  have : f x ∈ f '' s := by
    apply mem_preimage.mp
    apply xffs
  rcases (mem_image f s (f x)).mp this with ⟨x', x's, fx'eqy⟩
  have xeqx' : x = x' := h (Eq.symm fx'eqy)
  have xs : x ∈ s := mem_of_eq_of_mem xeqx' x's
  exact xs

example : f '' (f ⁻¹' u) ⊆ u := by
  intro y yffu
  rcases (mem_image f (f ⁻¹' u) y).mp yffu with ⟨x, xfu, fxeqy⟩
  rw [← fxeqy]
  have : f x ∈ u := xfu
  exact this

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y yu
  rcases h y with ⟨x, fxeqy⟩
  rw [← fxeqy]
  rw [← fxeqy] at yu
  apply mem_image_of_mem
  apply yu


example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro y yfs
  rcases (mem_image f s y).mp yfs with ⟨x, xs, fxeqy⟩
  have xt : x ∈ t := h xs
  rw [← fxeqy]
  apply mem_image_of_mem
  exact xt

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x xfiu
  have fxu : f x ∈ u := xfiu
  have fxv : f x ∈ v := h fxu
  have : x ∈ f⁻¹' v := mem_preimage.mpr fxv
  exact this

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x
  constructor
  . intro xfiu
    have h : f x ∈ u ∪ v := xfiu
    rcases h with (hu | hv)
    . left; exact mem_preimage.mpr hu
    . right; exact mem_preimage.mpr hv
  . intro h
    have : f x ∈ u ∪ v := h
    exact this

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro y ⟨x, ⟨xs, xt⟩, fxeqy⟩
  rw [← fxeqy]
  have : f x ∈ f '' s ∩ f '' t := by
    constructor
    . apply mem_image_of_mem; exact xs
    . apply mem_image_of_mem; exact xt
  exact this

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro y ⟨yfs, yft⟩
  rcases (mem_image f s y).mp yfs with ⟨x, xs, fxeqy⟩
  rcases (mem_image f t y).mp yft with ⟨x', x't, fx'eqy⟩
  have fxeqfx' : f x = f x' := by
    apply Eq.trans
    exact fxeqy
    exact Eq.symm fx'eqy
  have xeqx' : x = x' := h fxeqfx'
  rw [← fxeqy]
  have xt : x ∈ t := mem_of_eq_of_mem xeqx' x't
  have xst : x ∈ s ∩ t := ⟨xs, xt⟩
  have : f x ∈ f '' (s ∩ t) := by
    apply mem_image_of_mem
    exact xst
  exact this

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro y ⟨yfs, ynft⟩
  rcases (mem_image f s y).mp yfs with ⟨x, xs, fxeqy⟩
  have xnt : x ∉ t := by
    intro xt
    have fxft : f x ∈ f '' t := by
      apply mem_image_of_mem
      exact xt
    rw [← fxeqy] at ynft
    apply ynft
    exact fxft
  have : x ∈ s \ t := ⟨xs, xnt⟩
  have : f x ∈ f '' (s \ t) := by apply mem_image_of_mem; exact this
  rw [← fxeqy]
  exact this

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  intro x ⟨xfiu, xnfiv⟩
  have fxu : f x ∈ u := xfiu
  have fxnv : f x ∉ v := xnfiv
  have : f x ∈ u \ v := ⟨xfiu, xnfiv⟩
  have : x ∈ f⁻¹' (u \ v) := mem_preimage.mpr this
  exact this

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext y
  constructor
  . intro ⟨yfs, yv⟩
    rcases (mem_image f s y).mp yfs with ⟨x, xs, fxeqy⟩
    have xfiv : x ∈ f⁻¹' v := by
      apply mem_preimage.mpr
      rw [fxeqy]
      exact yv
    have : x ∈ s ∩ f⁻¹' v := ⟨xs, xfiv⟩
    rw [← fxeqy]
    have : f x ∈ f '' (s ∩ f⁻¹' v) := by
      apply mem_image_of_mem
      exact this
    exact this
  . intro h
    rcases (mem_image f _ y).mp h with ⟨x, ⟨xs, xfiv⟩, fxeqy⟩
    rw [← fxeqy]
    have fxv : f x ∈ v := xfiv
    have fxfs : f x ∈ f '' s := by
      apply mem_image_of_mem
      exact xs
    exact ⟨fxfs, fxv⟩

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  intro y ⟨x, ⟨xs, xfiu⟩, fxeqy⟩
  rw [← fxeqy]
  have fxfs : f x ∈ f '' s := by apply mem_image_of_mem; exact xs
  have fxu : f x ∈ u := xfiu
  have : f x ∈ f '' s ∩ u := ⟨fxfs, fxu⟩
  exact this

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intro x ⟨xs, xfiu⟩
  have : f x ∈ f '' s ∩ u := by
    constructor
    . apply mem_image_of_mem; exact xs
    . apply xfiu
  have : x ∈ f⁻¹' (f '' s ∩ u) := by
    apply mem_preimage.mpr
    exact this
  exact this

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  intro x h
  rcases h with xs | xfiu
  . have fxfs : f x ∈ f '' s := by apply mem_image_of_mem; exact xs
    have : f x ∈ f '' s ∪ u := by left; exact fxfs
    apply mem_preimage.mpr
    exact this
  . have fxu : f x ∈ u := xfiu
    have : f x ∈ f '' s ∪ u := by right; exact fxu
    exact this

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  simp
  constructor
  . intro h
    rcases h with ⟨x, ⟨i, xAi⟩, fxeqy⟩
    use i
    use x
  . rintro ⟨i, x, xAi, fxeqy⟩
    use x
    constructor
    use i
    exact fxeqy

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  simp
  intro i x
  simp
  intro h
  have xAi : x ∈ A i := h i
  constructor
  use xAi

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y
  simp
  intro h
  rcases h i with ⟨x, xAi, fxeqy⟩
  have : ∀ (i : I), x ∈ A i := by
    intro i'
    rcases h i' with ⟨x', x'Ai, fx'eqy⟩
    have fxeqfx' : f x = f x' := Eq.trans fxeqy (Eq.symm fx'eqy)
    have xeqx' : x = x' := injf fxeqfx'
    apply mem_of_eq_of_mem
    exact xeqx'
    exact x'Ai
  exact ⟨x, this, fxeqy⟩


example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  simp only [mem_iUnion]
  constructor
  . intro h
    simp only [mem_iUnion] at h
    have h' : f x ∈ ⋃ i, B i := h
    simp only [mem_iUnion] at h'
    exact h'
  . rintro ⟨i, xfiBi⟩
    have : f x ∈ ⋃ i, B i := mem_iUnion_of_mem i xfiBi
    apply mem_preimage.mpr
    exact this

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  have xpos : x > 0 := by apply xpos
  have ypos : y > 0 := by apply ypos
  intro logxeqlogy
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [logxeqlogy]
    _ = y := by rw [exp_log ypos]

example : range exp = { y | y > 0 } := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  . intro (ypos : y > 0)
    use log y
    rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x x_nonneg y y_nonneg heq
  calc
    x = (√x)^2 := Eq.symm (sq_sqrt x_nonneg)
    _ = (√y)^2 := by rw [heq]
    _ = y := sq_sqrt y_nonneg

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x x_nonneg y y_nonneg heq
  dsimp at heq
  calc
    x = √(x^2) := Eq.symm (sqrt_sq x_nonneg)
    _ = √(y^2) := by rw [heq]
    _ = y := sqrt_sq y_nonneg

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext x
  constructor
  . intro h
    rcases (mem_image sqrt { x | x ≥ 0 } x).mp h with ⟨y, yge0, sqrtyeqx⟩
    rw [← sqrtyeqx]
    dsimp
    apply sqrt_nonneg
  . intro x_nonneg
    simp
    use x^2
    constructor
    . apply sq_nonneg
    . apply sqrt_sq x_nonneg

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext x
  constructor
  . intro h
    simp; simp at h
    rcases h with ⟨y, sqyeqx⟩
    have sqy_nonneg : 0 ≤ y^2 := by apply sq_nonneg
    apply le_of_le_of_eq
    exact sqy_nonneg
    exact sqyeqx
  . intro x_nonneg
    simp; simp at x_nonneg
    use √x
    apply sq_sqrt
    exact x_nonneg

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

def inverse
    (f : α → β)
    : β → α
    := λ y : β ↦
  if h : ∃ x, f x = y
  then Classical.choose h
  else default

theorem inverse_spec
    {f : α → β}
    (y : β) (h : ∃ x, f x = y)
    : f (inverse f y) = y
    := by
  rw [inverse]
  rw [dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

-- RESUME FROM HERE? (OR EARLIER???)
example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  . intro injf y
    rw [inverse]
    by_cases h : ∃ x, f x = f y
    . rcases h with ⟨x, fxeqfy⟩
      have : x = y := injf fxeqfy




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
