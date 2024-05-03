import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Subset

-- Practice Session - May 2, 2024

example (x : U) (A : Set U) (h : x ∈ A) : x ∈ A := by
  exact h

example (x : U) (A B : Set U) (h1 : A ⊆ B) (h2 : x ∈ A) : x ∈ B := by
  exact h1 h2

example (x : U) (A B C : Set U) (h1 : A ⊆ B) (h2 : B ⊆ C) (h3 : x ∈ A) : x ∈ C := by
  apply h1 at h3
  apply h2 at h3
  exact h3

example (x : U) (A B C : Set U) (h1 : A ⊆ B) (h2 : B ⊆ C) (h3 : x ∈ A) : x ∈ C := by
  exact h2 (h1 h3)

example {x : U} {A B C : Set U} (h1 : A ⊆ B) (h2 : x ∈ B → x ∈ C) : x ∈ A → x ∈ C := by
  intro xA
  exact h2 (h1 xA)

example (A : Set U) : A ⊆ A := by
  intro x xA
  exact xA

example (A : Set U) : A ⊆ A := by
  rfl

example {A B C : Set U} (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
  intro x xA
  exact h2 (h1 xA)

example {A B : Set U} {x : U} (h1 : x ∈ A) (h2 : x ∉ B) : ¬A ⊆ B := by
  by_contra x
  apply x at h1
  exact h2 h1

example (A : Set U) (x : U) : x ∈ Aᶜ ↔ x ∉ A := by
  rfl
