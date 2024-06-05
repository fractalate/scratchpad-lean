import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Subset

open Finset
open Fintype
open BigOperators

-- Practice Session - June 3, 2024

example (n m : ℕ) : ∑ i : Fin n, ∑ j : Fin m, ( 2 ^ (i : ℕ) * (1 + j) : ℕ) = ∑ j : Fin m, ∑ i : Fin n, ( 2 ^ (i : ℕ) * (1 + j) : ℕ) := by
  rw [@sum_comm]

example (A : Set U) (F : Set (Set U)) : A ∩ (⋃₀ F) = ⋃₀ {s | ∃ u ∈ F, s = A ∩ u} := by
  ext x
  apply Iff.intro

  intro ⟨xa, ⟨t, ⟨tf, xt⟩⟩⟩
  use A ∩ t
  constructor
  use t
  exact ⟨xa, xt⟩

  intro ⟨t, ⟨⟨u, ⟨uf, tau⟩⟩, xt⟩⟩
  rw[tau] at xt
  constructor
  exact xt.left
  use u
  exact ⟨uf, xt.right⟩

-- Practice Session - June 4, 2024

theorem arithmetic_sum
 (n : ℕ) : 2 * (∑ i : Fin (n + 1), ↑i) = n * (n + 1) := by
  induction n with
  | zero =>
    simp
  | succ n n_ih =>
    rw[Fin.sum_univ_castSucc]
    simp
    rw[Nat.mul_add]
    rw[n_ih]
    rw[Nat.succ_eq_add_one]
    ring

example (m : ℕ) : (∑ i : Fin (m + 1), (i : ℕ)^3) = (∑ i : Fin (m + 1), (i : ℕ))^2 := by
  induction m with
  | zero =>
    simp
  | succ n n_ih =>
    rw[Fin.sum_univ_castSucc]
    simp
    rw[Fin.sum_univ_castSucc (n := n + 1)]
    simp
    rw[n_ih]
    rw[add_pow_two]
    rw[arithmetic_sum]
    ring

example (A B C : Set U) : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  ext x
  apply Iff.intro

  intro xabc
  obtain xab | xc := xabc
  obtain xa | xb := xab
  exact Or.inl xa
  exact Or.inr (Or.inl xb)
  exact Or.inr (Or.inr xc)

  intro xabc
  obtain xa | xbc := xabc
  exact Or.inl (Or.inl xa)
  obtain xb | xc := xbc
  exact Or.inl (Or.inr xb)
  exact Or.inr xc

example {A : Type} (x : A) : x ∉ (∅ : Set A) := by
  simp

example (A : Set U) : Aᶜᶜ = A := by
  ext x
  apply Iff.intro

  intro xacc
  rw[Set.mem_compl_iff] at xacc
  simp at xacc
  assumption

  intro xa
  rw[Set.mem_compl_iff]
  simp
  assumption

example {People : Type} [Inhabited People] (isDrinking : People → Prop) : ∃ (x : People), isDrinking x → ∀ (y : People), isDrinking y := by
  by_cases h : ∀ (y : People), isDrinking y

  use default
  intro
  assumption

  simp at h
  obtain ⟨x, xh⟩ := h
  use x
  intro
  contradiction

example (x y z : ℕ) (h : x = 2 * y + 1) (g : z = 3 * y + 1): x ^ 2 = 4 * y ^ 2 + z + y := by
  rw[h, g]
  ring

example (A : Set ℕ) : A ⊆ Set.univ := by
  simp

example (A B : Prop) (g : A → B) (b : ¬ B) : ¬ A := by
  tauto

example (A B : Prop) (g : A → B) (b : ¬ B) : ¬ A := by
  by_contra a
  apply g at a
  contradiction

example {A : Type} (x : A) : x ∈ (Set.univ : Set A) := by
  simp

example (A : Set U) (F : Set (Set U)) : ⋃₀ F ⊆ A ↔ ∀ s ∈ F, s ⊆ A := by
  rw [@Set.sUnion_subset_iff]

example (A : Set U) (F : Set (Set U)) : ⋃₀ F ⊆ A ↔ ∀ s ∈ F, s ⊆ A := by
  apply Iff.intro

  intro fa
  intro s sf y ys
  simp at fa
  apply fa at sf
  apply sf at ys
  assumption

  intro sfsa
  intro y yf
  obtain ⟨s, ⟨sf, ys⟩⟩ := yf
  apply sfsa at ys
  assumption
  assumption

example : ∀ (x : ℕ), (Even x) → Odd (1 + x) := by
  unfold Even
  unfold Odd
  intro n
  intro ⟨r, rh⟩
  use r
  rw [rh]
  ring

example (A B C : Set U) (h1 : A ∪ C ⊆ B ∪ C) (h2 : A ∩ C ⊆ B ∩ C) : A ⊆ B := by
  intro x xa
  have xbc := h1 (Or.inl xa)
  obtain xb | xc := xbc
  assumption
  have xbc := h2 ⟨xa, xc⟩
  exact xbc.left

example {A : Type _} (s : Set A) : s.Nonempty ↔ s ≠ ∅ := by
  push_neg
  rfl

example {A : Type _} (s : Set A) : s = ∅ ↔ ∀ x, x ∉ s := by
  apply Iff.intro
  intro se
  rw [se]
  simp

  intro xa
  ext x
  apply Iff.intro
  intro xs
  apply xa at xs
  contradiction

  intro xe
  contradiction
