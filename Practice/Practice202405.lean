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

-- Practice Session - May 6, 2024

example (x : U) (A B : Set U) (h1 : x ∈ A) (h2 : x ∈ B) : x ∈ A ∩ B := by
  exact And.intro h1 h2

example (x : U) (A B C : Set U) (h1 : A ⊆ B) (h2 : B ⊆ C) (h3 : x ∈ A) : x ∈ C := by
  have h4 := h1 h3
  apply h2 at h4
  exact h4

example (A B C : Set U) (h1 : A ⊆ B) (h2 : A ⊆ C) : A ⊆ B ∩ C := by
  intro x xA
  have h3 := h1 xA
  have h4 := h2 xA
  exact And.intro h3 h4

example {A B : Set U} {x : U} (h1 : x ∈ A) (h2 : x ∉ B) : ¬A ⊆ B := by
  by_contra ASubB
  have oops := ASubB h1
  exact h2 oops

example {A B : Set U} {x : U} (h1 : x ∈ A) (h2 : x ∉ B) : ¬A ⊆ B := by
  by_contra ASubB
  have oops := ASubB h1
  exact h2 oops

example (A B : Set U) : A ∩ B ⊆ B ∩ A := by
  intro x xAB
  exact And.intro xAB.right xAB.left

example (A B C : Prop) : ¬((¬B ∨ ¬ C) ∨ (A → B)) → (¬A ∨ B) ∧ ¬ (B ∧ C) := by
  tauto

-- Practice Sessoin - May 7, 2024

-- Drinker's "Paradox"
example {People : Type} [Inhabited People] (isDrinking : People → Prop) : ∃ (x : People), isDrinking x → ∀ (y : People), isDrinking y := by
  by_cases h : ∀ (y : People), isDrinking y
  use default
  intro
  assumption
  push_neg at h
  rcases h with ⟨p,hp⟩
  use p
  intro hp'
  contradiction

example {A B C : Set U} (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
  intro x h
  apply h1 at h
  apply h2 at h
  assumption

example (A B : Set U) : A ∩ B = B ∩ A := by
  apply Set.Subset.antisymm
  intro x xAB
  exact And.intro xAB.right xAB.left
  intro x xAB
  exact And.intro xAB.right xAB.left

example (A : Set U) : A ⊆ A := by
  rfl

example (A B C : Set U) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  apply Set.Subset.antisymm
  intro x xABC
  exact And.intro xABC.left.left (And.intro xABC.left.right xABC.right)
  intro x xABC
  exact And.intro (And.intro xABC.left  xABC.right.left) xABC.right.right

example (x : U) (A B : Set U) (h1 : A ⊆ B) (h2 : x ∈ A) : x ∈ B := by
  apply h1 at h2
  exact h2

example (x : U) (A B : Set U) (h : x ∈ A) : x ∈ A ∨ x ∈ B := by
  exact Or.inl h

example (A : Set U) (x : U) : x ∈ Aᶜ ↔ x ∉ A := by
  apply Iff.intro
  intro xAC
  exact xAC
  intro xAC
  exact xAC

example (A B : Set U) : A ∩ B = B ∩ A := by
  apply Set.Subset.antisymm
  intro x xAB
  exact And.intro xAB.right xAB.left
  intro x xAB
  exact And.intro xAB.right xAB.left

example (A B C : Set U) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  apply Set.Subset.antisymm
  intro x xABC
  exact And.intro xABC.left.left (And.intro xABC.left.right xABC.right)
  intro x xABC
  exact And.intro (And.intro xABC.left xABC.right.left) xABC.right.right

example (A B C : Prop) : ¬((¬B ∨ ¬ C) ∨ (A → B)) → (¬A ∨ B) ∧ ¬ (B ∧ C) := by
  tauto

example : 42 = 42 := by
  rfl

example (n : ℕ) (h₁ : 10 > n) (h₂ : 1 < n) (h₃ : n ≠ 5) : 1 < n := by
  assumption

example (A : Prop) (hA : A) : A := by
  assumption

example : True := by
  trivial

example : ¬False := by
  trivial

example (A : Prop) (h : False) : A := by
  by_contra
  assumption

example (n : ℕ) (h : n ≠ n) : n = 37 := by
  by_contra
  exact h rfl

example (n : ℕ) (h : n = 10) (g : n ≠ 10) : n = 42 := by
  by_contra
  exact g h

example (A B : Prop) (hA : A) (hB : B) : A ∧ B := by
  constructor
  assumption
  assumption

example (A B C : Prop) (h : A ∧ (B ∧ C)) : B := by
  exact h.right.left

example (A B : Prop) (hA : A) : A ∨ (¬ B) := by
  exact Or.inl hA

example (A B : Prop) (h : (A ∧ B) ∨ A) : A := by
  tauto

example (A B : Prop) (h : (A ∧ B) ∨ A) : A := by
  rcases h with h1 | h2
  exact h1.left
  assumption

example (A B C : Prop) (h : A ∨ (B ∧ C)) : (A ∨ B) ∧ (A ∨ C) := by
  tauto

example (A B C : Prop) (h : A ∨ (B ∧ C)) : (A ∨ B) ∧ (A ∨ C) := by
  rcases h with hA | hBC
  exact And.intro (Or.inl hA) (Or.inl hA)
  exact And.intro (Or.inr hBC.left) (Or.inr hBC.right)

example (n : ℕ) (h : n ≠ n) : n = 37 := by
  by_contra
  exact h rfl

example (n : ℕ) (h : n = 10) (g : n ≠ 10) : n = 42 := by
  by_contra
  exact g h

example (A : Prop) (h : False) : A := by
  by_contra
  assumption

example (A B : Prop) (hB : B) : A → (A ∧ B) := by
  intro x
  exact And.intro x hB

example (A B : Prop) (hA : A) (h : A → B) : B := by
  apply h at hA
  assumption

example (A B : Prop) (h : A) (hAB : A → B) : B := by
  apply hAB at h
  assumption

example (A B C : Prop) (f : A → B) (g : B → C) : A → C := by
  intro x
  apply f at x
  apply g at x
  assumption

example (A B C : Prop) (f : A → B) (g : B → C) : A → C := by
  tauto

example (A B C D E F G H I : Prop) (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F) (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I) (q : H → G) (r : H → I) : A → I := by
  intro x
  apply f at x
  apply i at x
  apply l at x
  apply p at x
  assumption

example (A B : Prop) (mp : A → B) (mpr : B → A) : A ↔ B := by
  constructor
  assumption
  assumption

example (n : ℕ) (h : n ≠ n) : n = 37 := by
  by_contra
  exact h rfl

example (A B : Prop) (h : (A ∧ B) ∨ A) : A := by
  rcases h with hAB | hA
  exact hAB.left
  assumption

example (A B C : Prop) (h : A ∨ (B ∧ C)) : (A ∨ B) ∧ (A ∨ C) := by
  rcases h with hA | hBC
  exact And.intro (Or.inl hA) (Or.inl hA)
  exact And.intro (Or.inr hBC.left) (Or.inr hBC.right)

example (n : ℕ) (h : n = 10) (g : n ≠ 10) : n = 42 := by
  by_contra
  apply g h

example (n : ℕ) (h : n ≠ n) : n = 37 := by
  by_contra
  exact h rfl
