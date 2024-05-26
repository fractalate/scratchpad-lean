-- Practice Session - May 22, 2024

import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Subset

open Finset
open BigOperators

example (F G : Set (Set U)) : ⋃₀ (F ∪ G) = (⋃₀ F) ∪ (⋃₀ G) := by
  ext x
  apply Iff.intro
  intro xufug

  rw[Set.mem_sUnion] at xufug
  obtain ⟨t, ht⟩ := xufug
  rw[Set.mem_union] at ht
  rw[Set.mem_union, Set.mem_sUnion, Set.mem_sUnion]
  by_cases h : t ∈ F
  apply Or.inl
  use t
  exact And.intro h ht.right
  obtain ⟨tfg, xt⟩ := ht
  rcases tfg
  contradiction
  apply Or.inr
  use t

  intro xfug
  rw[Set.mem_union, Set.mem_sUnion, Set.mem_sUnion] at xfug
  rw[Set.mem_sUnion]
  rcases xfug with xf | xg
  obtain ⟨t, ht⟩ := xf
  use t
  rw[Set.mem_union]
  exact And.intro (Or.inl ht.left) ht.right
  obtain ⟨t, ht⟩ := xg
  use t
  rw[Set.mem_union]
  exact And.intro (Or.inr ht.left) ht.right

example {A B : Set U} {x : U} (h1 : x ∈ A) (h2 : x ∉ B) : ¬A ⊆ B := by
  intro h3
  apply h3 at h1
  contradiction

/-
example (A B : Set U) : A ∩ B = ⋂₀ {A, B} := by
  ext x
  apply Iff.intro

  intro xab
  rw[Set.mem_sInter]
  intro t tab
  rcases tab with ta | tb
  rw[← ta] at xab
  exact xab.left
  rw[← tb] at xab
  exact xab.right

  intro xab
  rw[Set.mem_sInter] at xab
  have h4 := (xab A) A
  have h5 := (xab B) B
  exact ⟨h4, h5⟩
-/

-- Practice Session - May 23, 2024

-- From a chatter on Twitch on DonDoesMath's channel.
example (m n : ℤ) : (2*m + 1)^2 - (2*n - 1)^2 = 4 * (m + n)*(m - n + 1) := by
  ring

-- Practice Session - May 26, 2024

example (x : U) (A B C : Set U) (h1 : A ⊆ B) (h2 : B ⊆ C) (h3 : x ∈ A) : x ∈ C := by
  exact h2 (h1 h3)

example (A : Set U) (F : Set (Set U)) (h1 : A ∈ F) : A ⊆ ⋃₀ F := by
  intro x xa
  use A

example (F G : Set (Set U)) (h1 : F ⊆ G) : ⋃₀ F ⊆ ⋃₀ G := by
  intro x xff
  obtain ⟨t, ⟨tf, xt⟩⟩ := xff
  apply h1 at tf
  use t

example (A : Set U) : A ⊆ A := by
  intro x xa
  assumption

example (A B : Set U) : A ∩ B ⊆ A := by
  intro x xab
  exact xab.left

example (A B : Set U) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  rw[← compl_compl A, ← compl_compl B]
  rw[← Set.compl_union]
  rw[compl_compl, compl_compl, compl_compl]

example (F G : Set (Set U)) (h1 : F ⊆ G) : ⋂₀ G ⊆ ⋂₀ F := by
  intro x
  rw[Set.mem_sInter]
  rw[Set.mem_sInter]
  intro h
  intro t tf
  apply h1 at tf
  apply h at tf
  assumption

example : ¬ ∃ (n : ℕ), ∀ (k : ℕ) , Odd (n + k) := by
  push_neg
  intro n
  use n
  rw[← Nat.even_iff_not_odd]
  unfold Even
  use n

example (n : ℕ) (h₁ : 10 > n) (h₂ : 1 < n) (h₃ : n ≠ 5) : 1 < n := by
  linarith

example (A B C : Prop) (h : A ∨ (B ∧ C)) : (A ∨ B) ∧ (A ∨ C) := by
  tauto

example (n : ℕ) : 2 * (∑ i : Fin (n + 1), ↑i) = n * (n + 1) := by
  induction n with
  | zero =>
    simp
  | succ n n_ih =>
    rw[Fin.sum_univ_succ]; simp
    rw[sum_add_distrib]; simp
    rw[Nat.mul_add]
    rw[n_ih]
    rw[Nat.succ_eq_add_one]
    ring

example (A : Set U) (x : U) : x ∈ Aᶜ ↔ x ∉ A := by
  apply Iff.intro
  intro xac
  assumption
  intro xac
  assumption

example (n m : ℕ) : ∑ i : Fin n, ∑ j : Fin m, ( 2 ^ (i : ℕ) * (1 + j) : ℕ) = ∑ j : Fin m, ∑ i : Fin n, ( 2 ^ (i : ℕ) * (1 + j) : ℕ) := by
  rw[sum_comm]

example (n : ℕ) : ∑ i : Fin n, ((i : ℕ) + 1) = n + (∑ i : Fin n, (i : ℕ)) := by
  induction n
  simp
  rw[sum_add_distrib]
  simp
  ring

example (A B : Prop) (h : A) (hAB : A → B) : B := by
  apply hAB at h
  assumption

example (n : ℕ) : 0 < n ↔ n ≠ 0 := by
  omega

example (A B C : Prop) : (A ∧ (¬¬C)) ∨ (¬¬B) ∧ C ↔ (A ∧ C) ∨ B ∧ (¬¬C) := by
  tauto

example (x : U) (A B : Set U) (h1 : x ∈ A) (h2 : x ∈ B) : x ∈ A ∩ B := by
  exact ⟨h1, h2⟩

example (A B C : Prop) : ¬((¬B ∨ ¬ C) ∨ (A → B)) → (¬A ∨ B) ∧ ¬ (B ∧ C) := by
  tauto

example {A B C : Set U} (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
  intro x hx
  apply h1 at hx
  apply h2 at hx
  assumption
