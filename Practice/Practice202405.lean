import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Subset

open Finset
open BigOperators

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

example (n : ℕ) : ∑ i : Fin n, ((i : ℕ) + 1) = n + (∑ i : Fin n, (i : ℕ)) := by
  rw[sum_add_distrib]
  simp
  ring

example (F G : Set (Set U)) (h1 : F ⊆ G) : ⋂₀ G ⊆ ⋂₀ F := by
  intro x xGG
  rw[Set.mem_sInter] at xGG
  rw[Set.mem_sInter]
  intro t
  intro tt
  apply h1 at tt
  apply xGG at tt
  assumption

-- Practice Session - May 8, 2024


example (A B : Prop) (h : A ↔ B) : B ↔ A := by
  symm
  assumption

example (n : ℕ) (h : n ≠ n) : n = 37 := by
  trivial

example (A B C D : Prop) (h₁ : C ↔ D) (h₂ : A ↔ B) (h₃ : A ↔ D) : B ↔ C := by
  symm at h₂
  symm at h₁
  rw[h₂]
  rw[h₃]
  rw[h₁]

example (n : ℕ) (h : n = 10) (g : n ≠ 10) : n = 42 := by
  by_contra
  exact g h

example (A B C : Prop) (h : A ↔ B) (g : B → C) : A → C := by
  rw[h]
  assumption

example (A : Set U) : Aᶜᶜ = A := by
  apply Set.Subset.antisymm
  intro x xACC
  rw[Set.mem_compl_iff] at xACC
  rw[Set.mem_compl_iff] at xACC
  push_neg at xACC
  assumption
  intro x xACC
  rw[Set.mem_compl_iff]
  rw[Set.mem_compl_iff]
  push_neg
  assumption

example (A B : Prop) : (A ↔ B) → (A → B) := by
  intro aiffb h
  rw[aiffb] at h
  assumption

example (A B : Prop) (h : A ↔ B) : B ↔ A := by
  symm
  assumption

example (A : Prop) (h : False) : A := by
  trivial

example (A : Prop) : ¬A ∨ A := by
  by_cases a : A
  exact Or.inr a
  exact Or.inl a

example (A B C D : Prop) (h₁ : C ↔ D) (h₂ : A ↔ B) (h₃ : A ↔ D) : B ↔ C := by
  rw[← h₂]
  rw[h₃]
  rw[← h₁]

example {A B : Set U} (h1 : A ⊆ B) : Bᶜ ⊆ Aᶜ := by
  intro x xBCompl
  by_contra xA
  rw[Set.mem_compl_iff] at xA
  push_neg at xA
  apply h1 at xA
  contradiction

example (A B C : Prop) (h : A ↔ B) (g : B → C) : A → C := by
  rw[h]
  assumption

example (A B : Prop) : (A ↔ B) → (A → B) := by
  intro ab a
  rw[ab] at a
  assumption

example (A B : Set U) : B ⊆ A ∪ B := by
  intro x xB
  exact Or.inr xB

example (A B : Set U) : A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  apply Iff.intro
  intro h x xBCompl
  by_contra xA
  rw[Set.mem_compl_iff] at xA
  push_neg at xA
  apply h at xA
  contradiction
  intro h x xA
  by_contra xBCompl
  rw[← Set.mem_compl_iff] at xBCompl
  apply h at xBCompl
  contradiction

example (A B C : Set U) (h1 : A ⊆ C) (h2 : B ⊆ C) : A ∪ B ⊆ C := by
  intro x xAuB
  rcases xAuB with xA | xB
  apply h1 at xA
  assumption
  apply h2 at xB
  assumption

example (A : Prop) : ¬A ∨ A := by
  by_cases a : A
  exact Or.inr a
  exact Or.inl a

example (x : U) (A B : Set U) (h : x ∈ A ∧ x ∈ B) : x ∈ A := by
  exact h.left

example (A B : Set U) : A ∪ B ⊆ B ∪ A := by
  intro x xAuB
  rcases xAuB with xA | xB
  exact Or.inr xA
  exact Or.inl xB

example (A B : Prop) : (A ↔ B) → (A → B) := by
  intro ab
  intro a
  rw[ab] at a
  assumption

example (A B : Set U) : B ⊆ A ∪ B := by
  intro x xB
  exact Or.inr xB

example (A B C : Set U) (h1 : A ⊆ C) (h2 : B ⊆ C) : A ∪ B ⊆ C := by
  intro x xAuB
  rcases xAuB with xA | xB
  apply h1 at xA
  assumption
  apply h2 at xB
  assumption

example (A B : Set U) : A ∪ B ⊆ B ∪ A := by
  intro x xAuB
  rcases xAuB with xA | xB
  exact Or.inr xA
  exact Or.inl xB

-- Practice Session - May 9, 2023

example (A B C : Set U) (h1 : A ⊆ B) (h2 : A ⊆ C) : A ⊆ B ∩ C := by
  intro x xA
  exact And.intro (h1 xA) (h2 xA)

example (A B C : Prop) : (A ∧ (¬¬C)) ∨ (¬¬B) ∧ C ↔ (A ∧ C) ∨ B ∧ (¬¬C) := by
  tauto

example (A B : Set U) : A ∩ B ⊆ A := by
  intro x xAB
  exact xAB.left

example (A B : Prop) : (A → B) ↔ ¬ A ∨ B := by
  tauto -- Nice! But let's do it for real this time.

example (A B : Prop) : (A → B) ↔ ¬ A ∨ B := by
  apply Iff.intro
  intro hatob
  by_cases a : A
  apply hatob at a
  exact Or.inr a
  exact Or.inl a
  intro notaorb
  intro a
  rcases notaorb with nota | b
  contradiction
  assumption

example (A B : Set U) : A ∪ B ⊆ B ∪ A := by
  intro x xAB
  rcases xAB with xA | xB
  exact Or.inr xA
  exact Or.inl xB

example (x y : ℕ) : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

example (A B C : Prop) (h : A ↔ B) (g : B → C) : A → C := by
  rw[h]
  apply g

example (a b c d : ℕ) (h₁ : c = d) (h₂ : a = b) (h₃ : a = d) : b = c := by
  rw[← h₂]
  rw[h₃]
  rw[← h₁]

example (A : Prop) : ¬A ∨ A := by
  by_cases a : A
  exact Or.inr a
  exact Or.inl a

example (a b : ℕ) (h : a = b) (g : a + a ^ 2 = b + 1) : b + b ^ 2 = b + 1 := by
  rw[h] at g
  assumption

example (A B : Prop) : (A ↔ B) → (A → B) := by
  intro aiffb
  rw[aiffb]
  intro b
  assumption

example (A B : Set U) : A ∪ B = B ∪ A := by
  rw[Set.union_comm] -- This is the theorem that is being proved here

example (A B : Set U) : A ∪ B = B ∪ A := by
  apply Set.Subset.antisymm
  intro x xAuB
  rcases xAuB with xA | xB
  exact Or.inr xA
  exact Or.inl xB
  intro x xBuA
  rcases xBuA with xB | xA
  exact Or.inr xB
  exact Or.inl xA

example (A B C D : Prop) (h₁ : C ↔ D) (h₂ : A ↔ B) (h₃ : A ↔ D) : B ↔ C := by
  rw[← h₂]
  rw[h₃]
  rw[← h₁]

example (A B C : Set U) : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  apply Set.Subset.antisymm

  intro x xAuBuC
  rcases xAuBuC with xAuB | xC
  rcases xAuB with xA | xB
  exact Or.inl xA
  exact Or.inr (Or.inl xB)
  exact Or.inr (Or.inr xC)

  intro x xAuBuC
  rcases xAuBuC with xA | xBuC
  exact Or.inl (Or.inl xA)
  rcases xBuC with xB | xC
  exact Or.inl (Or.inr xB)
  exact Or.inr xC

example (A B : Prop) : (A → B) ↔ ¬ A ∨ B := by
  apply Iff.intro
  intro AtoB
  by_cases a : A
  apply AtoB at a
  exact Or.inr a
  exact Or.inl a
  intro nAorB
  intro a
  rcases nAorB
  contradiction
  assumption

example (a b : ℕ) (h : a = b) (g : a + a ^ 2 = b + 1) : b + b ^ 2 = b + 1 := by
  rw[h] at g
  assumption

example (A B C : Set U) (h1 : A ⊆ C) (h2 : B ⊆ C) : A ∪ B ⊆ C := by
  intro x xAuB
  rcases xAuB with xA | xB
  apply h1 at xA
  assumption
  apply h2 at xB
  assumption

example (A B : Set U) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  rewrite [Set.compl_union]
  rfl

example (A B : Set U) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  rewrite [← Set.compl_union]
  rfl

example (A B : Set U) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  rw[Set.mem_compl_iff]
  rw[Set.mem_union]
  rw[Set.mem_inter_iff]
  rw[Set.mem_compl_iff]
  rw[Set.mem_compl_iff]
  apply Iff.intro
  intro h
  push_neg at h
  assumption
  intro h
  push_neg
  assumption

example (A B : Set U) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  rw[Set.mem_compl_iff]
  rw[Set.mem_union]
  rw[Set.mem_inter_iff]
  rw[Set.mem_compl_iff]
  rw[Set.mem_compl_iff]
  apply Iff.intro
  intro h
  push_neg at h
  exact h
  intro h
  push_neg
  exact h

example (A B : Prop) (h : A ↔ B) : B ↔ A := by
  rw[h]

example (A B : Set U) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  -- ext x is a better opener for this kind of proof.
  -- This apply splits the goal before x is introduced.
  -- Since the mem_* theorems require x, I have to do the
  -- rewrites for each sub-goal, which is more work.
  apply Set.Subset.antisymm
  intro x
  rw[Set.mem_compl_iff]
  rw[Set.mem_union]
  rw[Set.mem_inter_iff]
  rw[Set.mem_compl_iff]
  rw[Set.mem_compl_iff]
  intro h
  push_neg at h
  assumption
  intro x
  rw[Set.mem_compl_iff]
  rw[Set.mem_union]
  rw[Set.mem_inter_iff]
  rw[Set.mem_compl_iff]
  rw[Set.mem_compl_iff]
  intro h
  push_neg
  assumption

-- Practice Session - May 10, 2024

example : True := by
  trivial

example (x y z : ℕ) (h : x = 2 * y + 1) (g : z = 3 * y + 1): x ^ 2 = 4 * y ^ 2 + z + y := by
  rw[h]
  rw[g]
  ring

example (n : ℕ) (h₁ : 10 > n) (h₂ : 1 < n) (h₃ : n ≠ 5) : 1 < n := by
  assumption

example (A B C : Set U) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  ext x
  apply Iff.intro
  intro abc
  exact And.intro abc.left.left (And.intro abc.left.right abc.right)
  intro abc
  exact And.intro (And.intro abc.left abc.right.left) abc.right.right

example : 1 + 1 = 2 := by
  ring

example : ¬False := by
  trivial

example (A B : Prop) (h : (A ∧ B) ∨ A) : A := by
  tauto

example (A B : Prop) (h : (A ∧ B) ∨ A) : A := by
  rcases h with ⟨xA1, xb⟩ | xA
  assumption
  assumption

example (n : ℕ) (h : Even n) : Even (n ^ 2) := by
  unfold Even
  unfold Even at h
  rcases h with ⟨r, hr⟩
  rw[hr]
  use 2 * r^2
  ring

example (A B : Prop) : (A → B) ↔ ¬ A ∨ B := by
  tauto

example (A B : Prop) : (A → B) ↔ ¬ A ∨ B := by
  apply Iff.intro
  intro atob
  by_cases a : A
  apply atob at a
  exact Or.inr a
  exact Or.inl a
  intro naorb
  intro a
  rcases naorb with na | b
  contradiction
  assumption

example (n : ℕ) (h : Odd n) : Odd (n ^ 2) := by
  revert h
  unfold Odd
  intro h
  rcases h with ⟨r, hr⟩
  use 2*r^2 + 2*r
  rw[hr]
  ring

example (n : ℕ) (h : Even n) : Even (n ^ 2) := by
  revert h
  unfold Even
  intro h
  rcases h with ⟨r, hr⟩
  use 2 * r^2
  rw[hr]
  ring

example (x : U) (A B : Set U) (h : x ∈ A) : x ∈ A ∨ x ∈ B := by
  exact Or.inl h

example (x : U) (A B : Set U) (h1 : x ∈ A) (h2 : x ∈ B) : x ∈ A ∩ B := by
  exact And.intro h1 h2

example : ∀ (x : ℕ), (Even x) → Odd (1 + x) := by
  intro x
  unfold Even
  unfold Odd
  intro xeven
  rcases xeven with ⟨r, hr⟩
  use r
  rw[hr]
  ring

example (A B : Prop) (hA : A) : A ∨ (¬ B) := by
  tauto

example (A B : Prop) (hA : A) : A ∨ (¬ B) := by
  exact Or.inl hA

example (A B : Set U) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  rw[Set.compl_union]

example (A B : Set U) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  rw[Set.mem_compl_iff]
  apply Iff.intro
  intro hx
  rw[Set.mem_union] at hx
  push_neg at hx
  assumption
  intro hx
  rw[Set.mem_union]
  push_neg
  assumption

example (n : ℕ) (h : Odd n) : Odd (n ^ 2) := by
  unfold Odd
  unfold Odd at h
  rcases h with ⟨r, hr⟩
  use 2*r^2 + 2*r
  rw[hr]
  ring

example (n : ℕ) (h : Even n) : Even (n ^ 2) := by
  unfold Even
  unfold Even at h
  rcases h with ⟨r, hr⟩
  use 2*r^2
  rw[hr]
  ring

example : ∀ (x : ℕ), (Even x) → Odd (1 + x) := by
  unfold Even
  unfold Odd
  intro n h
  rcases h with ⟨r, hr⟩
  use r
  rw[hr]
  ring

example (A B : Set U) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  rw[Set.compl_inter]

example (A B : Set U) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  rw[← compl_compl (Aᶜ ∪ Bᶜ)]
  rw[Set.compl_union]
  rw[compl_compl]
  rw[compl_compl]

example (n : ℕ) (h : Odd n) : Odd (n ^ 2) := by
  unfold Odd at h
  unfold Odd
  rcases h with ⟨r, hr⟩
  use 2*r^2 + 2*r
  rw[hr]
  ring

example (A B : Prop) (mp : A → B) (mpr : B → A) : A ↔ B := by
  tauto

example (A B : Prop) (mp : A → B) (mpr : B → A) : A ↔ B := by
  apply Iff.intro
  assumption
  assumption

example (A B : Prop) (mp : A → B) (mpr : B → A) : A ↔ B := by
  constructor
  assumption
  assumption

example (A B C : Set U) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  apply Iff.intro
  intro xabc
  rcases xabc with ⟨xa, xbc⟩
  rcases xbc with xb | xc
  exact Or.inl (And.intro xa xb)
  exact Or.inr (And.intro xa xc)
  intro xabc
  rcases xabc with xab | xac
  exact And.intro xab.left (Or.inl xab.right)
  exact And.intro xac.left (Or.inr xac.right)

example (A B C : Prop) (h : A ∨ (B ∧ C)) : (A ∨ B) ∧ (A ∨ C) := by
  tauto

example (A B C D E F G H I : Prop) (f : A → B) (g : C → B) (h : A → D) (i : B → E) (j : C → F) (k : E → D) (l : E → F) (m : G → D) (n : H → E) (p : F → I) (q : H → G) (r : H → I) : A → I := by
  intro a
  apply f at a
  apply i at a
  apply l at a
  apply p at a
  assumption

example (A B : Set U) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  rw[← compl_compl (Aᶜ ∪ Bᶜ)]
  ext x
  rw[Set.compl_union]
  rw[compl_compl]
  rw[compl_compl]

example (A B C : Set U) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  apply Iff.intro
  intro xabc
  rcases xabc with xa | xbc
  exact And.intro (Or.inl xa) (Or.inl xa)
  rcases xbc with ⟨xb, xc⟩
  exact And.intro (Or.inr xb) (Or.inr xc)
  intro xabc
  rcases xabc with ⟨xab, xac⟩
  rcases xab with xa | xb
  exact Or.inl xa
  rcases xac with xa | xc
  exact Or.inl xa
  exact Or.inr (And.intro xb xc)

example (x : U) (A B : Set U) (h : x ∈ A ∩ B) : x ∈ B := by
  exact h.right

-- Practice Session - May 11, 2024

example (n : ℕ) (h : Odd n) : Odd (n ^ 2) := by
  unfold Odd
  unfold Odd at h
  rcases h with ⟨k, hk⟩
  use 2*k^2 + 2*k
  rw[hk]
  ring

example {X : Type} (P : X → Prop) : ¬ (∃ x : X, P x) ↔ ∀ x : X, ¬ P x := by
  tauto

example {X : Type} (P : X → Prop) : ¬ (∃ x : X, P x) ↔ ∀ x : X, ¬ P x := by
  push_neg
  rfl

example {X : Type} (P : X → Prop) : ¬ (∃ x : X, P x) ↔ ∀ x : X, ¬ P x := by
  apply Iff.intro
  contrapose
  intro x
  -- rw[Classical.not_forall] at x
  push_neg at x
  push_neg
  assumption
  contrapose
  intro x
  --rw[Classical.not_forall]
  push_neg at x
  push_neg
  assumption

example (A B : Prop) (hA : A) (hB : B) : A ∧ B := by
  exact And.intro hA hB

example : ¬ ∃ (n : ℕ), ∀ (k : ℕ) , Odd (n + k) := by
  push_neg
  intro n
  use n
  rw[Nat.odd_iff_not_even]
  unfold Even
  push_neg
  use n

example (A B : Set U) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  rw[← compl_compl (Aᶜ ∪ Bᶜ)]
  ext x
  rw[Set.compl_union]
  rw[compl_compl]
  rw[compl_compl]

example {People : Type} [Inhabited People] (isDrinking : People → Prop) : ∃ (x : People), isDrinking x → ∀ (y : People), isDrinking y := by
  by_cases h : ∀ (y : People), isDrinking y
  use default
  intro
  assumption
  push_neg at h
  rcases h with ⟨y, hy⟩
  use y
  intro hy
  contradiction

example {People : Type} [Inhabited People] (isDrinking : People → Prop) : ∃ (x : People), isDrinking x → ∀ (y : People), isDrinking y := by
  by_cases h : ∀ (y : People), isDrinking y
  use default
  intro
  exact h
  push_neg at h
  rcases h with ⟨y, hy⟩
  use y
  intro oops
  contradiction

example {X : Type} (P : X → Prop) : ¬ (∃ x : X, P x) ↔ ∀ x : X, ¬ P x := by
  push_neg
  rfl

example {X : Type} (P : X → Prop) : ¬ (∃ x : X, P x) ↔ ∀ x : X, ¬ P x := by
  apply Iff.intro
  contrapose
  intro h
  rw[Classical.not_forall] at h
  push_neg at h
  push_neg
  assumption
  contrapose
  intro h
  push_neg at h
  rw[Classical.not_forall]
  push_neg
  assumption

example : ¬ ∃ (n : ℕ), ∀ (k : ℕ) , Odd (n + k) := by
  push_neg
  intro n
  use n
  rw[← Nat.even_iff_not_odd]
  unfold Even
  use n

example (A B : Set U) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  rw[← compl_compl (Aᶜ ∪ Bᶜ)]
  ext x
  rw[Set.compl_union]
  rw[compl_compl]
  rw[compl_compl]

example {People : Type} [Inhabited People] (isDrinking : People → Prop) : ∃ (x : People), isDrinking x → ∀ (y : People), isDrinking y := by
  by_cases h : ∀ (y : People), isDrinking y
  use default
  intro
  assumption
  push_neg at h
  rcases h with ⟨y, hy⟩
  use y
  intro oops
  contradiction

example (n : ℕ) (h : Even n) : Even (n ^ 2) := by
  unfold Even
  unfold Even at h
  rcases h with ⟨r, hr⟩
  rw[hr]
  use 2*r^2
  ring

example (n m : ℕ) : m < n ↔ m + 1 ≤ n := by
  rfl

example (A B C : Set U) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  rw[Set.inter_union_distrib_left]
  rw[Set.union_inter_distrib_left]
  rw[Set.union_inter_distrib_left]
  rw[Set.inter_union_distrib_left]
  rw[Set.union_inter_distrib_left]

example (A B C : Set U) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  apply Iff.intro
  intro xabc
  rcases xabc with xa | xbc
  exact And.intro (Or.inl xa) (Or.inl xa)
  exact And.intro (Or.inr xbc.left) (Or.inr xbc.right)
  intro xabac
  rcases xabac with ⟨xab, xac⟩
  rcases xab with xa | xb
  exact Or.inl xa
  rcases xac with xa | xc
  exact Or.inl xa
  exact Or.inr (And.intro xb xc)

example {X : Type} (P : X → Prop) : ¬ (∃ x : X, P x) ↔ ∀ x : X, ¬ P x := by
  apply Iff.intro
  intro h
  push_neg at h
  assumption
  intro h
  push_neg
  assumption

example : ¬ ∃ (n : ℕ), ∀ (k : ℕ) , Odd (n + k) := by
  push_neg
  intro n
  use n
  rw[Nat.odd_iff_not_even]
  push_neg
  unfold Even
  use n

theorem compl_inter (A B : Set U) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  rw[← compl_compl (Aᶜ ∪ Bᶜ)]
  ext x
  rw[Set.compl_union]
  rw[compl_compl]
  rw[compl_compl]

example {People : Type} [Inhabited People] (isDrinking : People → Prop) : ∃ (x : People), isDrinking x → ∀ (y : People), isDrinking y := by
  by_cases h : ∀ (y : People), isDrinking y
  use default
  intro
  assumption
  push_neg at h
  rcases h with ⟨y, hy⟩
  use y
  intro
  contradiction

example (n m : ℕ) : m < n ↔ m + 1 ≤ n := by
  rfl

example (A B : Prop) (hA : A) (h : A → B) : B := by
  apply h at hA
  assumption

example (n : ℕ) : 0 < n ↔ n ≠ 0 := by
  rcases n
  simp
  simp

example (A B : Prop) (hB : B) : A → (A ∧ B) := by
  intro hA
  exact And.intro hA hB

example (n : ℕ) : 0 < n ↔ n ≠ 0 := by
  rcases n
  simp
  simp

example : ∀ (x : ℕ), (Even x) → Odd (1 + x) := by
  intro x xeven
  rcases xeven with ⟨r, hr⟩
  use r
  rw[hr]
  ring

example (A B C : Set U) (h1 : A ∪ C ⊆ B ∪ C) (h2 : A ∩ C ⊆ B ∩ C) : A ⊆ B := by
  intro x xA
  have h3 := h1 (Or.inl xA)
  rcases h3 with xB | xC
  assumption
  have h4 := h2 (And.intro xA xC)
  exact h4.left

example (A B C : Set U) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  rw[Set.inter_union_distrib_left]

example (A B C : Set U) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  apply Iff.intro
  intro xabc
  rcases xabc with ⟨xa, xbc⟩
  rcases xbc with xb | xc
  exact Or.inl (And.intro xa xb)
  exact Or.inr (And.intro xa xc)
  intro xabac
  rcases xabac with xab | xac
  exact And.intro xab.left (Or.inl xab.right)
  exact And.intro xac.left (Or.inr xac.right)

example (A : Set U) (F : Set (Set U)) (h1 : A ∈ F) : ⋂₀ F ⊆ A := by
  intro x xfff
  exact (xfff A) h1

example (n : ℕ) : 0 < n ↔ n ≠ 0 := by
  rcases n
  simp
  simp

example (A B : Set U) : A ∩ B ⊆ B ∩ A := by
  intro x xab
  exact And.intro xab.right xab.left

example (F G : Set (Set U)) (h1 : F ⊆ G) : ⋂₀ G ⊆ ⋂₀ F := by
  intro x
  rw[Set.mem_sInter]
  rw[Set.mem_sInter]
  intro hg
  intro h3 f
  apply h1 at f
  have h4 := hg h3
  apply h4 at f
  assumption

example (F G : Set (Set U)) (h1 : F ⊆ G) : ⋂₀ G ⊆ ⋂₀ F := by
  intro x
  rw[Set.mem_sInter]
  rw[Set.mem_sInter]
  intro hG
  intro t tF
  have ting_xint := hG t
  have tG := h1 tF
  have xt := ting_xint tG
  assumption

example (A B C : Set U) (h1 : A ∪ C ⊆ B ∪ C) (h2 : A ∩ C ⊆ B ∩ C) : A ⊆ B := by
  intro x xA
  have xBuC := h1 (Or.inl xA)
  rcases xBuC with xB | xC
  assumption
  have xBnC := h2 (And.intro xA xC)
  exact xBnC.left

example (A : Set U) (F : Set (Set U)) (h1 : A ∈ F) : ⋂₀ F ⊆ A := by
  intro x
  rw[Set.mem_sInter]
  intro xfff
  have h2 := xfff A
  apply h2 at h1
  assumption

example (F G : Set (Set U)) (h1 : F ⊆ G) : ⋂₀ G ⊆ ⋂₀ F := by
  intro x
  rw[Set.mem_sInter]
  rw[Set.mem_sInter]
  intro hG
  intro t tF
  -- I find this pretty confusing, but I'm able to work through it now.
  have tG := h1 tF
  have xt := hG t
  exact xt tG

example (A : Set U) (F : Set (Set U)) (h1 : A ∈ F) : ⋂₀ F ⊆ A := by
  intro x
  rw[Set.mem_sInter]
  intro xF
  have h2 := xF A
  apply h2 at h1
  assumption
