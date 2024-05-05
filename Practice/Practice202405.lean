import Mathlib.Tactic
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

-- Practice Session - May 3, 2024

example {A B : Set U} (h1 : A ⊆ B) : Bᶜ ⊆ Aᶜ := by
  intro x xB
  --rw [Set.mem_compl_iff] at xB
  rw [Set.mem_compl_iff]
  by_contra xA
  have oops := h1 xA
  exact xB oops

example (A : Set U) : Aᶜᶜ = A := by
  apply Set.Subset.antisymm
  intro x xA
  rw[Set.mem_compl_iff] at xA
  rw[Set.mem_compl_iff] at xA
  push_neg at xA
  exact xA
  intro x xA
  rw[Set.mem_compl_iff]
  rw[Set.mem_compl_iff]
  push_neg
  exact xA

example {A B : Set U} (h1 : A ⊆ B) : Bᶜ ⊆ Aᶜ := by
  intro x xB
  rewrite [Set.mem_compl_iff] at xB
  rewrite [Set.mem_compl_iff]
  by_contra xA
  apply h1 at xA -- In this one I reused xA to mean x ∈ B, but I don't prefer it.
  exact xB xA

-- Practice Session - May 4, 2024

example {A B : Set U} (h1 : A ⊆ B) : Bᶜ ⊆ Aᶜ := by
  intro x xB
  rw [Set.mem_compl_iff] at xB
  rw [Set.mem_compl_iff]
  by_contra xA
  have oops := h1 xA
  exact xB oops

example (A : Set U) : Aᶜᶜ = A := by
  apply Set.Subset.antisymm

  intro x xA
  rw [Set.mem_compl_iff] at xA
  rw [Set.mem_compl_iff] at xA
  push_neg at xA
  exact xA

  intro x xA
  rw [Set.mem_compl_iff]
  rw [Set.mem_compl_iff]
  push_neg
  exact xA

example (A B : Set U) : A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  apply Iff.intro

  intro ASubsetB
  intro x xBCompl
  by_contra xA
  rewrite [Set.mem_compl_iff] at xA
  push_neg at xA
  exact xBCompl (ASubsetB xA)

  intro BCSubsetAC
  intro x xA
  by_contra xBCompl
  apply BCSubsetAC at xBCompl
  exact xBCompl xA

example {A B : Set U} (h1 : A ⊆ B) : Bᶜ ⊆ Aᶜ := by
  intro x xBCompl
  by_contra xA
  rewrite [Set.mem_compl_iff] at xA
  push_neg at xA
  have xB := h1 xA
  exact xBCompl xB

example (x : U) (A B : Set U) (h : x ∈ A ∧ x ∈ B) : x ∈ A := by
  exact h.left

example (A B : Set U) : A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  apply Iff.intro

  intro ASubsetB
  intro x xBCompl
  by_contra xA
  rewrite [Set.mem_compl_iff] at xA
  push_neg at xA
  have xB := ASubsetB xA
  exact xBCompl xB

  intro BComplSubsetACompl
  intro x xA
  by_contra xBCompl
  have h2 : x ∉ A := BComplSubsetACompl xBCompl
  exact h2 xA

-- Practice Session - May 5, 2024

example (x : U) (A : Set U) (h : x ∈ A) : x ∈ A := by
  exact h

example (x : U) (A B : Set U) (h : x ∈ A ∩ B) : x ∈ B := by
  exact h.right

example (A B : Set U) : A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  apply Iff.intro
  intro xAB
  intro x xBCompl
  rewrite [Set.mem_compl_iff]
  by_contra xA
  exact xBCompl (xAB xA)

  intro xAB
  intro x xA
  by_contra xBC
  rewrite [← Set.mem_compl_iff] at xBC
  have xAC := xAB xBC
  exact xAC xA

example (A B : Set U) : A ∩ B ⊆ A := by
  intro x xAB
  exact xAB.left

example {x : U} {A B C : Set U} (h1 : A ⊆ B) (h2 : x ∈ B → x ∈ C) : x ∈ A → x ∈ C := by
  intro xA
  have xB := h1 xA
  have xC := h2 xB
  exact xC
